module

public import Iris.HeapLang.Lib.SpinLock
public import Iris.HeapLang.Lib.FracAgreeLocal
public import Iris.ProgramLogic.Atomic
import Iris.HeapLang.Lib.IInv

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

/-!
## Logically atomic (TaDA-style) lock, on top of the spin lock

A TaDA-style logically atomic specification for a lock, instantiated for the
`SpinLock` implementation. Port of Rocq `iris_heap_lang/lib/logatom_lock.v`.

The abstract lock state `Free`/`Locked` is tracked by a fractional-agreement
ghost variable (`stateVar`, a `DFracAgree` over `State`). The client owns `3/4`
of it (`tada_lock_state`); the lock invariant `R` owns the remaining `1/4`
witnessing `Free`. Acquiring recombines the two fractions, allowing the update
to `Locked`; releasing does the reverse.
-/

namespace AtomicLock

/-- The abstract state of the lock. -/
inductive State where
  | Free
  | Locked
deriving DecidableEq, Repr

/-- `State` is a discrete (Leibniz) OFE/COFE, so it can sit inside `Agree`. -/
scoped instance : COFE State := COFE.ofDiscrete _ Eq_Equivalence
scoped instance : OFE.Leibniz State := ⟨fun h => h⟩
scoped instance : OFE.Discrete State := ⟨fun h => h⟩

/-- The ghost resource tracking the abstract lock state: a fractional agreement
over `State`. -/
abbrev LockStateF : COFE.OFunctorPre := constOF (FracAgree.DFracAgreeR State)

/-- Ghost context for the atomic lock: the state-tracking resource plus the
underlying spin-lock resources. -/
class AtomicLockG (GF : BundledGFunctors) where
  [elemG : ElemG GF LockStateF]
  [spinlockG : SpinLock.SpinLockG GF]

attribute [reducible, instance] AtomicLockG.elemG AtomicLockG.spinlockG

/-- The two fractions used by the TaDA construction, `1/4` and `3/4`, built from
`Qp.half` (avoiding raw rational positivity proofs). -/
def q1_4 : Qp := Qp.half (Qp.half 1)
def q3_4 : Qp := Qp.half 1 + Qp.half (Qp.half 1)

/-- Ghost names bundling the state variable and the underlying lock's name. -/
structure ALockName where
  state : GName
  lock : GName

section Predicates

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [AtomicLockG GF]

/-- Fractional-agreement ownership of the abstract lock state. -/
def stateVar (γ : GName) (q : Qp) (s : State) : IProp GF :=
  iOwn (F := LockStateF) γ (FracAgree.Frac.mk q s)

/-- The client-visible abstract state assertion. Holds `3/4` of the state ghost;
when `Locked` it additionally owns the physical `locked` token and the remaining
`1/4` (which was handed over on acquire). -/
def tada_lock_state (γ : ALockName) (s : State) : IProp GF := iprop%
  stateVar γ.state q3_4 s ∗
  (if s = .Locked then SpinLock.locked γ.lock ∗ stateVar γ.state q1_4 .Locked else True)

/-- The persistent "is a lock" assertion: the underlying spin lock whose resource
invariant `R` is the `1/4` `Free` witness. -/
def tada_is_lock (γ : ALockName) (lk : Val) : IProp GF := iprop%
  SpinLock.isLock γ.lock lk (stateVar γ.state q1_4 .Free)

instance instTadaIsLockPersistent (γ : ALockName) (lk : Val) :
    Persistent (tada_is_lock (GF := GF) γ lk) := by
  unfold tada_is_lock; infer_instance

instance instTadaLockStateTimeless (γ : ALockName) (s : State) :
    Timeless (tada_lock_state (GF := GF) γ s) := by
  unfold tada_lock_state stateVar SpinLock.locked
  cases s <;> simp <;> infer_instance

theorem tada_lock_state_exclusive (γ : ALockName) (s1 s2 : State) :
    tada_lock_state (GF := GF) γ s1 ∗ tada_lock_state γ s2 ⊢ False := by
  iintro ⟨H1, H2⟩
  unfold tada_lock_state stateVar
  icases H1 with ⟨Hvar1, -⟩
  icases H2 with ⟨Hvar2, -⟩
  ihave H := iOwn_cmraValid_op $$ [Hvar1 Hvar2]
  · isplitl [Hvar1] <;> iassumption
  icases internalCmraValid_discrete (A := FracAgree.DFracAgreeR State) $$ H with %Hvalid
  exact absurd (FracAgree.Frac.op_valid_L.mp Hvalid).1 (by unfold q3_4 Qp.half; native_decide)

end Predicates

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [AtomicLockG GF]

/-- Allocation: a fresh lock starts `Free`, handing the client
`tada_is_lock ∗ tada_lock_state Free`. -/
theorem newlock_tada_spec :
    ⊢@{IProp GF} {{ True }} hl(&SpinLock.newlock #())
      {{ lk γ, RET lk; tada_is_lock γ lk ∗ tada_lock_state γ .Free }} := by
  iintro %Φ - HΦ
  iapply wp_fupd
  unfold SpinLock.newlock
  wp_pures
  -- allocate the abstract-state ghost variable, fully owned, in state `Free`
  imod (iOwn_alloc (F := LockStateF) (FracAgree.Frac.mk (1 : Qp) State.Free)
    (by exact ⟨DFrac.valid_own_one, Agree.toAgree_valid⟩)) with ⟨%γvar, Hvar⟩
  -- split full ownership: 1 = 3/4 (client) + 1/4 (lock invariant)
  have qsum : q3_4 + q1_4 = 1 := by unfold q3_4 q1_4 Qp.half; apply Subtype.ext; native_decide
  have hsplit : (FracAgree.Frac.mk (1:Qp) State.Free : FracAgree.DFracAgreeR State)
      = FracAgree.Frac.mk q3_4 State.Free • FracAgree.Frac.mk q1_4 State.Free := by
    rw [← qsum]; exact (FracAgree.Frac.mk_op).to_eq
  have hsp : iOwn (F := LockStateF) (GF := GF) γvar (FracAgree.Frac.mk (1:Qp) State.Free) ⊢
      stateVar γvar q3_4 .Free ∗ stateVar γvar q1_4 .Free := by
    unfold stateVar; rw [hsplit]; exact iOwn_op.mp
  ihave ⟨Hvar1, Hvar2⟩ := hsp $$ [Hvar]; · iexact Hvar
  -- allocate the spin lock: its physical `locked` token and its invariant
  -- (with the `1/4` `Free` witness as the protected resource `R`)
  imod token_alloc with ⟨%γlock, Hlocked⟩
  iapply wp_alloc
  iintro !> %l Halloc
  imod (inv_alloc SpinLock.spinlockN ⊤
      (SpinLock.lockInv γlock l (stateVar γvar q1_4 .Free))) $$ [Halloc Hvar2 Hlocked] with Hinv
  · unfold SpinLock.lockInv SpinLock.locked
    iexists false; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
  imodintro
  -- hand back `tada_is_lock ∗ tada_lock_state Free` for `γ := ⟨γvar, γlock⟩`
  ispecialize HΦ $$ %(hl_val(#l)) %(⟨γvar, γlock⟩ : ALockName)
  iapply HΦ
  isplitr [Hvar1]
  · unfold tada_is_lock SpinLock.isLock
    iexists l
    isplit
    · ipureintro; rfl
    · iexact Hinv
  · unfold tada_lock_state
    simp only [reduceCtorEq, if_false]
    iframe

/-- Logically atomic acquire: atomically observe the lock's abstract state `s`,
learn it was `Free`, and update it to `Locked`. -/
theorem acquire_tada_spec (γ : ALockName) (lk : Val) :
    ⊢@{IProp GF} tada_is_lock γ lk -∗
      ⟪ ∀ s, tada_lock_state γ s ⟫
        hl(&SpinLock.acquire &lk) @ ∅
      ⟪ ⌜s = State.Free⌝ ∗ tada_lock_state γ .Locked | RET hl_val(#()) ⟫ := by
  iintro #H %Φ HAU
  iapply wp_fupd
  simp only [tada_is_lock]
  -- physically acquire the lock; get `locked` + the `1/4 Free` invariant witness
  iapply SpinLock.acquire_spec γ.lock lk (stateVar γ.state q1_4 .Free) $$ [H]
  · iexact H
  iintro ⟨Hlocked, Hvar1⟩
  -- open the atomic update; the `1/4 Free` witness forces the abstract state `s = Free`
  iauopen HAU with ⟨%s, Hl, Hclose⟩
  simp only [tada_lock_state, stateVar]
  icases Hl with ⟨Hvar2, -⟩
  icombine Hvar1 Hvar2 gives %Hvalid
  have hs : s = State.Free := (FracAgree.Frac.op_valid_L.mp Hvalid).2.symm
  subst hs
  -- ghost update Free → Locked (combine 1/4 + 3/4, update, split)
  have qsum2 : q1_4 + q3_4 = 1 := by unfold q1_4 q3_4 Qp.half; apply Subtype.ext; native_decide
  have hupd : (iOwn (F := LockStateF) (GF := GF) γ.state (FracAgree.Frac.mk q1_4 State.Free) ∗
        iOwn γ.state (FracAgree.Frac.mk q3_4 State.Free)) ⊢
      |==> (iOwn (F := LockStateF) γ.state (FracAgree.Frac.mk q1_4 State.Locked) ∗
        iOwn γ.state (FracAgree.Frac.mk q3_4 State.Locked)) :=
    iOwn_op.mpr.trans (Entails.trans
      (iOwn_update (FracAgree.Frac.update₂ (a' := State.Locked) qsum2)) (bupd_mono iOwn_op.mp))
  imod (hupd) $$ [Hvar1 Hvar2] with ⟨Hvar1, Hvar2⟩
  · iframe
  -- commit: return `⌜s = Free⌝ ∗ tada_lock_state γ Locked`
  icases Hclose with ⟨-, Hcommit⟩
  imod Hcommit $$ [Hvar2 Hlocked Hvar1] with HΦ
  · simp only [↓reduceIte]
    isplit
    · ipureintro; trivial
    · iframe
  imodintro
  iexact HΦ

/-- Logically atomic release: atomically move the lock from `Locked` back to
`Free`. The precondition is fixed to `Locked` (no `∀∀` binder). -/
theorem release_tada_spec (γ : ALockName) (lk : Val) :
    ⊢@{IProp GF} tada_is_lock γ lk -∗
      ⟪ tada_lock_state γ .Locked ⟫
        hl(&SpinLock.release &lk) @ ∅
      ⟪ tada_lock_state γ .Free | RET hl_val(#()) ⟫ := by
  iintro #H %Φ HAU
  -- open the atomic update *before* the physical step (release commits its
  -- abstract effect via ghost state, independent of the store's timing)
  iapply fupd_wp
  iauopen HAU with ⟨Hl, Hclose⟩
  simp only [tada_lock_state, ↓reduceIte]
  icases Hl with ⟨Hvar1, Hlocked, Hvar2⟩
  icases Hclose with ⟨-, Hcommit⟩
  -- ghost update Locked → Free: combine the 3/4 + 1/4 fractions, update, split back
  have qsum : q3_4 + q1_4 = 1 := by unfold q3_4 q1_4 Qp.half; apply Subtype.ext; native_decide
  have hupd : (stateVar (GF := GF) γ.state q3_4 .Locked ∗ stateVar γ.state q1_4 .Locked) ⊢
      |==> (stateVar γ.state q3_4 .Free ∗ stateVar γ.state q1_4 .Free) := by
    unfold stateVar
    exact iOwn_op.mpr.trans (Entails.trans
      (iOwn_update (FracAgree.Frac.update₂ (a' := State.Free) qsum)) (bupd_mono iOwn_op.mp))
  imod (hupd) $$ [Hvar1 Hvar2] with ⟨Hvar1, Hvar2⟩
  · iframe
  simp only [reduceCtorEq, if_false] at *
  -- commit the atomic update with the fresh 3/4 `Free`
  imod Hcommit $$ [Hvar1] with HΦ
  · iframe
  imodintro
  -- physical release via the underlying spin lock (R = the 1/4 `Free` witness)
  simp only [tada_is_lock]
  iapply SpinLock.release_spec γ.lock lk (stateVar γ.state q1_4 .Free) $$ [H Hlocked Hvar2]
  · iframe; iexact H
  · iintro _; iexact HΦ

end Specs

/-!
## Sketch: a "concrete" (HOCAP-style) atomic spec on the raw location

The `tada_*` specs above use *data abstraction*: the physical boolean is sealed
inside `isLock`'s invariant, and the client only ever sees the abstract
`Free`/`Locked` state via the ghost witness `tada_lock_state`.

An alternative is a logically-atomic spec stated **directly on the physical
`l ↦ #b`**, with **no ghost state and no invariant** — the linearization point
is literally the machine step that flips the bit. This is more concrete/precise
(it exposes the representation) but it drops abstraction: the client owns the raw
cell, so nothing in the *spec* stops it from writing `l` itself and breaking
mutual exclusion. (These are *sketches*, stated but not proved.)
-/
section ConcreteSketch

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

/-- Logically-atomic `acquire` on the raw cell: the environment may hold `l = true`
(contention), so `acquire` spins — a failed CAS *aborts* (restores the AU and
retries); the LP is the successful CAS that observes `false` and flips it to
`true`. No ghost state. -/
theorem acquire_atomic_spec (l : Loc) :
    ⊢@{IProp GF}
      ⟪ ∀ b, l ↦ some hl_val(#(b : Bool)) ⟫
        hl(&SpinLock.acquire v(#l)) @ ∅
      ⟪ l ↦ some hl_val(#true) | RET hl_val(#()) ⟫ := by
  iintro %Φ HAU
  iloeb as IH
  unfold SpinLock.acquire SpinLock.tryAcquire
  wp_rec
  wp_pures
  wp_bind cmpXchg(_,_,_)
  iapply wp_atomic (s := Stuckness.NotStuck) (E1 := ⊤) (E2 := ∅)
  iauopen HAU with ⟨%b, Hl, Hclose⟩
  imodintro
  by_cases Heq : b = false
  · -- observed `false`: CAS succeeds — this is the LP, commit `l ↦ true`
    subst Heq
    iapply wp_wand $$ [Hl]
    · iapply wp_cmpXchg_true rfl rfl $$ Hl <;>
        simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
    · iintro %v ⟨%Hv, Hl⟩
      icases Hclose with ⟨-, Hcommit⟩
      imod Hcommit $$ [Hl] with HΦ
      · iframe
      imodintro; rw [Hv]; wp_pures; imodintro; itrivial
  · -- observed `true`: CAS fails — abort (restore the AU) and spin
    iapply wp_wand $$ [Hl]
    · iapply wp_cmpXchg_fail rfl rfl $$ Hl
      · trivial
      · simp_all
    · iintro %v ⟨%Hv, Hl⟩
      icases Hclose with ⟨Habort, -⟩
      imod Habort $$ Hl with HAU
      imodintro
      rw [Hv]
      -- `wp_pure` (not `wp_pures`): stop at the recursive call `acquire #l`
      -- instead of unfolding it, so `iapply IH` still matches
      wp_pure
      wp_pure
      iapply IH $$ HAU

/-- Strengthened physical acquire: the LP additionally exposes that the observed
old value was `false`. This extra `⌜b = false⌝` is exactly what lets a client
pin the abstract update `Free → Locked` when deriving the TaDA spec on top.

加强版的 physical acquire spec:除了 `l ↦ true` 之外,在 commit 时额外暴露
`⌜b = false⌝`(即 LP 那一步观察到的旧值是 false)。
原来的 `acquire_atomic_spec` 只保证 `l ↦ true`,并不告诉 client "旧值是什么";
但派生 TaDA spec 时,抽象 update `Free → Locked` 需要知道旧的 abstract state 是
`Free`(对应物理 `b = false`),否则这个 update 是 underdetermined 的。
所以这里把 `⌜b = false⌝` 显式塞进 postcondition。 -/
theorem acquire_atomic_spec' (l : Loc) :
    ⊢@{IProp GF}
      ⟪ ∀ b, l ↦ some hl_val(#(b : Bool)) ⟫
        hl(&SpinLock.acquire v(#l)) @ ∅
      ⟪ l ↦ some hl_val(#true) ∗ ⌜b = false⌝ | RET hl_val(#()) ⟫ := by
  iintro %Φ HAU
  iloeb as IH                                    -- Löb 归纳:处理 acquire 的自旋循环
  unfold SpinLock.acquire SpinLock.tryAcquire
  wp_rec
  wp_pures
  wp_bind cmpXchg(_,_,_)                          -- 聚焦到 CAS 这一原子步
  iapply wp_atomic (s := Stuckness.NotStuck) (E1 := ⊤) (E2 := ∅)
  iauopen HAU with ⟨%b, Hl, Hclose⟩                 -- 打开 atomic update,拿到物理 `l ↦ b`
  imodintro
  by_cases Heq : b = false
  · -- 观察到 false:CAS 会成功,这就是 LP
    subst Heq
    iapply wp_wand $$ [Hl]
    · iapply wp_cmpXchg_true rfl rfl $$ Hl <;>
        simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
    · iintro %v ⟨%Hv, Hl⟩
      icases Hclose with ⟨-, Hcommit⟩            -- 选择 commit 分支
      imod Hcommit $$ [Hl] with HΦ
      · isplitl [Hl]                             -- 提供 postcondition `l ↦ true ∗ ⌜b = false⌝`
        · iframe                                 --   左:l ↦ true
        · ipureintro; rfl                        --   右:⌜false = false⌝,trivial
      imodintro; rw [Hv]; wp_pures; imodintro; itrivial
  · -- 观察到 true:CAS 失败,abort(把 AU 原样还回)后继续自旋
    iapply wp_wand $$ [Hl]
    · iapply wp_cmpXchg_fail rfl rfl $$ Hl
      · trivial
      · simp_all
    · iintro %v ⟨%Hv, Hl⟩
      icases Hclose with ⟨Habort, -⟩             -- 选择 abort 分支,还回 AU
      imod Habort $$ Hl with HAU
      imodintro
      rw [Hv]
      wp_pure                                    -- 只走两个 pure step,停在递归调用 `acquire #l`
      wp_pure
      iapply IH $$ HAU                           -- 用 Löb 归纳假设收尾自旋

/-- Logically-atomic `release` on the raw cell: atomically store `false`. -/
theorem release_atomic_spec (l : Loc) :
    ⊢@{IProp GF}
      ⟪ ∀ b, l ↦ some hl_val(#b) ⟫
        hl(&SpinLock.release v(#l)) @ ∅
      ⟪ l ↦ some hl_val(#false) | RET hl_val(#()) ⟫ := by
  iintro %Φ HAU
  unfold SpinLock.release
  wp_pures
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%b, Hl, Hclose⟩
  imodintro
  iapply wp_store $$ Hl
  iintro !> Hl
  icases Hclose with ⟨-, Hcommit⟩
  imod Hcommit $$ [Hl] with HΦ
  · iframe
  imodintro
  itrivial

end ConcreteSketch

/-!
## Deriving the TaDA spec from the physical (pointers-to) spec

This section shows the promised direction *concrete ⟹ abstract*: the TaDA-style
logically-atomic specs can be **re-derived** on top of the concrete physical
specs `acquire_atomic_spec'` / `release_atomic_spec` (which talk only about the
raw cell `l ↦ b`), by wrapping `l` in an invariant that ties the physical boolean
to a fractional-agreement ghost variable — exactly the construction `isLock`
performs internally, but done explicitly here and layered on the atomic specs.

`atomicWP_inv` opens the lock invariant around the atomic step; the client's
abstract atomic update is threaded through it (`tacAupdIntro` + opening the AU)
to synthesise the physical atomic update the concrete spec demands. The derived
specs carry mask `@ ↑plockN` (the invariant namespace), as usual for logically
atomic specs that open an invariant.

────────────────────────────────────────────────────────────────────────
中文总览:本节演示 **concrete ⟹ abstract** 这个方向。

上一节的 physical spec(`acquire_atomic_spec'` / `release_atomic_spec`)只谈论
裸的物理 cell `l ↦ b`,没有任何 ghost state。这里我们把 `l` 用一个 invariant
包起来,invariant 里维持一个 fractional-agreement ghost variable,把物理布尔值
`b` 和抽象状态 `Free`/`Locked` 绑定(`lockRel`)。然后就能把 TaDA 风格的
`plock_state`/`plock_is_lock` spec **重新证明**出来 —— 完全建立在 physical spec 之上。

整个派生的三个关键工具:
* `atomicWP_inv`:在原子步周围打开 invariant(把 `▷ I` 加进原子的 pre/post)。
* `tacAupdIntro`:把 `⊢ atomicUpdate ...` 目标降解为 `⊢ atomicAcc ...`(即"要造一个 AU,
  只需给出一次 atomic access")。
* `iauopen HAU`:打开 client 手里的抽象 atomic update(= `imod` + `itele_reduce`),
  拿到它的 α(已清掉 telescope 噪音),并得到 abort/commit 两个 closer。

派生 spec 带 mask `@ ↑plockN`,因为它要打开名字空间 `plockN` 的 invariant
(logically-atomic spec 打开 invariant 的标准写法)。
-/
section PhysDerivation

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [AtomicLockG GF]

/-- Namespace for the lock invariant used by the derivation.
派生所用 invariant 的名字空间。 -/
def plockN : Namespace := ndot nroot "plock"

/-- Relate the physical boolean to the abstract state.
物理布尔值 ↔ 抽象状态的对应:`false ↦ Free`,`true ↦ Locked`。 -/
def bToState : Bool → State
  | false => .Free
  | true  => .Locked

/-- The lock invariant: the physical cell agrees with the `1/4` abstract witness.
锁的 invariant:存在某个物理值 `b`,使得 `l ↦ b`,并且 invariant 持有 `1/4` 份
的 ghost(见证抽象状态就是 `bToState b`)。client 持有另外 `3/4`(见 `plock_state`)。
agreement 保证物理 `b` 和抽象状态始终一致。 -/
def lockRel (γ : GName) (l : Loc) : IProp GF :=
  iprop(∃ b : Bool, (l ↦ some hl_val(#b)) ∗ stateVar γ q1_4 (bToState b))

/-- "Is a lock" for the derivation: the invariant tying `l` to the ghost state.
派生版的"这是一把锁":就是上面 invariant 的分配。persistent、可自由复制。 -/
def plock_is_lock (γ : GName) (l : Loc) : IProp GF :=
  inv plockN (lockRel γ l)

/-- Client-visible abstract state: the `3/4` share of the state ghost.
client 看到的抽象状态断言:持有 `3/4` 份 ghost。`3/4 + 3/4 > 1` 保证 exclusive。 -/
def plock_state (γ : GName) (s : State) : IProp GF :=
  stateVar γ q3_4 s

instance instPlockIsLockPersistent (γ : GName) (l : Loc) :
    Persistent (plock_is_lock (GF := GF) γ l) := by
  unfold plock_is_lock; infer_instance

-- `lockRel` 是 Timeless 的(内容都是 `l ↦ _` 和 `iOwn`,都在 discrete CMRA 上)。
-- 需要这个实例,才能在证明里用 `>` 把 `▷ lockRel` 的 later 剥掉。
-- 因为 body 里有 `∃ b`,而 `bToState b` 是一个 match,实例搜索会卡住;
-- 所以用 `haveI` 先对 `b` 做 case split,把 match 消掉,再交给自动搜索。
instance instLockRelTimeless (γ : GName) (l : Loc) : Timeless (lockRel (GF := GF) γ l) := by
  unfold lockRel
  haveI : ∀ b : Bool,
      Timeless (iprop((l ↦ some hl_val(#b)) ∗ stateVar (GF := GF) γ q1_4 (bToState b))) :=
    fun b => by cases b <;> (unfold stateVar bToState; infer_instance)
  infer_instance

/-- **Clean, Rocq-style derivation** of logically-atomic acquire, on the physical
spec `acquire_atomic_spec'` (`iauintro; iinv; iaaccintro'`). The abstract state
`s` is observed to be `Free` at the LP (the successful CAS, whose `⌜b = false⌝`
pins `s = Free`) and updated to `Locked`.

派生的 logically-atomic acquire,建立在加强版 physical `acquire_atomic_spec'` 之上,
用 Rocq idiom `iauintro; iinv …; iaaccintro' …`(见 `release_plock_spec`)。
和 release 的唯一区别在 commit:physical spec 交回 `⌜b = false⌝`,于是(经 agreement)
推出抽象状态 `s = Free`,既满足 postcondition 的 `⌜s = Free⌝`,又能做 update `Free → Locked`。
注意 client 这侧 pre 是 `∀ s`(telescope 多一个 `s`),打开 AU 时会拿到 `%s`。 -/
theorem acquire_plock_spec (γ : GName) (l : Loc) :
    ⊢@{IProp GF} plock_is_lock γ l -∗
      ⟪ ∀ s, plock_state γ s ⟫
        hl(&SpinLock.acquire v(#l)) @ ↑plockN
      ⟪ ⌜s = State.Free⌝ ∗ plock_state γ .Locked | RET hl_val(#()) ⟫ := by
  simp only [plock_is_lock]
  iintro #Hinv %Φ HAU
  -- 套加强版 physical acquire:它内部自己自旋,每次 CAS 都访问我们提供的 physical AU。
  iapply acquire_atomic_spec'.{0, 0} l
  iauintro
  -- 在 accessor 内部打开 lock invariant(poor-man's `iInv`):
  iinv Hinv as Hbody
  simp only [lockRel, plock_state, stateVar]
  icases Hbody with ⟨%b, Hl, Hst1⟩
  -- 把物理 cell 交给 accessor;abort/commit 自动分开:
  iaaccintro' with Hl
  · -- abort:CAS 失败(物理已 locked)时走这里,原样还回 invariant + client AU(状态不变)。
    -- abort 不需要 agreement:直接用手上的 b 重建 invariant body 即可。
    iintro Hl; imodintro; isplitl [Hl Hst1]
    · iexists b; iframe                           -- 重建 invariant body,物理值仍是 b
    · iframe HAU; iexact Hinv                     -- Pas = □inv ∗ HAU(client AU 原样)
  · -- commit:CAS 成功,physical spec 交回 `l↦true ∗ ⌜b = false⌝`。
    iintro %y Hcr
    icases Hcr with ⟨Hl, %Hbf⟩                   -- 拆出 `l↦true`(Hl)和纯命题 `b = false`(Hbf)
    subst Hbf                                     -- b := false ⇒ invariant 的 ghost 是 `1/4 Free`
    --
    iauopen HAU with ⟨%s, Hst3, Hclose⟩             -- 打开 client AU:抽象状态 %s、Hst3 = plock_state s
    -- agreement:`1/4 Free`(Hst1)与 `3/4 s`(Hst3)合起来 valid ⇒ Free = s(非破坏性,保留两份)
    icombine Hst1 Hst3 gives %Hvalid
    have hsf : s = State.Free := (FracAgree.Frac.op_valid_L.mp Hvalid).2.symm
    subst hsf                                     -- s := Free ⇒ postcondition 的 `⌜s = Free⌝` 变 trivial
    have qsum : q1_4 + q3_4 = 1 := by unfold q1_4 q3_4 Qp.half; apply Subtype.ext; native_decide
    -- ghost update `Free → Locked`(合成整份 → 改 agree → 拆回)。
    have hupd : (iOwn (F := LockStateF) (GF := GF) γ (FracAgree.Frac.mk q1_4 State.Free) ∗
          iOwn γ (FracAgree.Frac.mk q3_4 State.Free)) ⊢
        |==> (iOwn (F := LockStateF) γ (FracAgree.Frac.mk q1_4 State.Locked) ∗
          iOwn γ (FracAgree.Frac.mk q3_4 State.Locked)) :=
      iOwn_op.mpr.trans (Entails.trans
        (iOwn_update (FracAgree.Frac.update₂ (a' := State.Locked) qsum)) (bupd_mono iOwn_op.mp))
    imod hupd $$ [Hst1 Hst3] with ⟨Hst1, Hst3⟩   -- Hst1 = 1/4 Locked,Hst3 = 3/4 Locked
    · simp only [bToState]; iframe
    icases Hclose with ⟨-, Hcommit⟩
    -- 提交 client AU:premise = client β = `⌜Free = Free⌝ ∗ plock_state Locked`,得到 HΦ
    imod Hcommit $$ [Hst3] with HΦ
    · isplitr [Hst3]                              -- premise = `⌜Free=Free⌝ ∗ plock_state Locked`
      · ipureintro; rfl                           -- 左:`⌜Free = Free⌝`
      · iframe                                    -- 右:plock_state Locked = Hst3
    imodintro
    isplitl [Hl Hst1]                             -- accessor commit result = invariant body ∗ Φ
    · simp only [bToState]; iexists true; iframe                        -- 重建 invariant body:l↦true + 1/4 Locked
    · iexact HΦ                                   -- Φ

/-- **Clean, Rocq-style derivation** of the release spec, using the ported
`elim_acc_aacc` (`aacc_inv`) and the telescope-aware `iaaccintro'`:
`iauintro` turns the goal into a physical accessor, `aacc_inv` opens the lock
invariant *inside* the accessor (keeping it an accessor), and `iaaccintro'`
selects the physical cell and splits abort/commit — mirroring Rocq's
`awp_apply; iInv; iaaccintro`. -/
theorem release_plock_spec (γ : GName) (l : Loc) :
    ⊢@{IProp GF} plock_is_lock γ l -∗
      ⟪ plock_state γ .Locked ⟫
        hl(&SpinLock.release v(#l)) @ ↑plockN
      ⟪ plock_state γ .Free | RET hl_val(#()) ⟫ := by
  simp only [plock_is_lock]
  iintro #Hinv %Φ HAU
  iapply release_atomic_spec.{0, 0} l
  iauintro
  -- open the lock invariant *inside* the accessor (`iinv` = poor-man's `iInv`):
  iinv Hinv as Hbody
  simp only [lockRel, plock_state, stateVar]
  icases Hbody with ⟨%b, Hl, Hst1⟩
  -- hand the physical cell to the accessor; abort/commit are split for us:
  iaaccintro' with Hl
  · -- abort: rebuild the invariant body and return everything unchanged
    iintro Hl; imodintro; isplitl [Hl Hst1]
    · iexists b; iframe
    · iframe HAU; iexact Hinv
  · -- commit: fire the client AU, ghost-update `Locked → Free`, rebuild the invariant
    iintro %y Hl
    iauopen HAU with ⟨Hst3, Hclose⟩   -- open client AU (nil telescope)
    cases b
    · -- physical `false` contradicts the client's `Locked`
      simp only [bToState]
      icombine Hst1 Hst3 gives %Hvalid
      exact absurd (FracAgree.Frac.op_valid_L.mp Hvalid).2 (by decide)
    · -- physical `true`: ghost-update `Locked → Free` and commit the client AU
      simp only [bToState]
      have qsum : q1_4 + q3_4 = 1 := by unfold q1_4 q3_4 Qp.half; apply Subtype.ext; native_decide
      have hupd : (iOwn (F := LockStateF) (GF := GF) γ (FracAgree.Frac.mk q1_4 State.Locked) ∗
            iOwn γ (FracAgree.Frac.mk q3_4 State.Locked)) ⊢
          |==> (iOwn (F := LockStateF) γ (FracAgree.Frac.mk q1_4 State.Free) ∗
            iOwn γ (FracAgree.Frac.mk q3_4 State.Free)) :=
        iOwn_op.mpr.trans (Entails.trans
          (iOwn_update (FracAgree.Frac.update₂ (a' := State.Free) qsum)) (bupd_mono iOwn_op.mp))
      imod hupd $$ [Hst1 Hst3] with ⟨Hst1, Hst3⟩
      · iframe
      icases Hclose with ⟨-, Hcommit⟩
      imod Hcommit $$ [Hst3] with HΦ
      · iframe
      imodintro
      isplitl [Hl Hst1]
      · iexists false; iframe
      · iexact HΦ

end PhysDerivation

end AtomicLock

end
