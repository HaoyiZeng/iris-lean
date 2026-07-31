module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.ProgramLogic.Atomic
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Agree

@[expose] public section
namespace Iris.Examples.HeapLang

open Iris BI ProgramLogic CMRA OFE Auth
open Iris.HeapLang
open scoped Iris

namespace RwLock

inductive State
  | free
  | read (n : Nat)
  | write
deriving DecidableEq, Repr

inductive Mode
  | read
  | write
deriving DecidableEq, Repr

namespace State

/-- `read 0` is excluded because physical counter zero represents `free`. -/
inductive Valid : State → Prop
  | free : Valid .free
  | read (n : Nat) : Valid (.read (n + 1))
  | write : Valid .write

def counter : State → Int
  | .free => 0
  | .read n => n
  | .write => -1

theorem counter_injective {s₁ s₂ : State} (h₁ : Valid s₁) (h₂ : Valid s₂)
    (h : counter s₁ = counter s₂) : s₁ = s₂ := by
  cases h₁ <;> cases h₂ <;> simp_all [counter] <;> grind

end State

/-- A guard is compatible only with the matching held lock state. -/
inductive GuardCompatible : State → Mode → Prop
  | read (n : Nat) : GuardCompatible (.read (n + 1)) .read
  | write : GuardCompatible .write .write

/-- Public RwLock interface. The concrete implementation below is exposed as
`RwLock.instAPI`, following the class/implementation split in `Lock.lean`. -/
class API (GF : BundledGFunctors) [HeapLangGS hlc GF] where
  new : Val
  read_acquire : Val
  write_acquire : Val
  read_release : Val
  write_release : Val
  drop : Val

  name : Type
  [name_inhabited : Inhabited name]

  isRwLock : name → Val → State → Val → IProp GF
  rwGuard : name → Mode → IProp GF
  /-- A **fractional** permit.  Splitting one lets a client lend part of its
      permission away (e.g. into a data-structure invariant) while keeping enough to
      still prove the lock has not changed hands. -/
  rwGuardFrac : name → Mode → Qp → IProp GF

  isRwLock_timeless γ l s x : Timeless (isRwLock γ l s x)
  rwGuard_timeless γ mode : Timeless (rwGuard γ mode)
  rwGuardFrac_timeless γ mode q : Timeless (rwGuardFrac γ mode q)

  /-- `rwGuard` is the full (`q = 1`) permit of its mode. -/
  rwGuard_eq γ mode :
    rwGuard γ mode ⊣⊢@{IProp GF} rwGuardFrac γ mode 1
  /-- Permits of the same mode add up, so a full permit can be split and later
      reassembled.  Only a reassembled full permit is accepted by the release specs,
      which forces a client to reclaim every lent-out share before giving the lock
      back. -/
  rwGuardFrac_split γ mode q₁ q₂ :
    rwGuardFrac γ mode (q₁ + q₂) ⊣⊢@{IProp GF} rwGuardFrac γ mode q₁ ∗ rwGuardFrac γ mode q₂
  /-- Any positive share already pins the lock to that mode. -/
  rwGuardFrac_valid γ l s x mode q :
    isRwLock γ l s x ∗ rwGuardFrac γ mode q ⊢@{IProp GF} ⌜GuardCompatible s mode⌝

  isRwLock_valid γ l s x :
    isRwLock γ l s x ⊢@{IProp GF} ⌜State.Valid s⌝
  isRwLock_exclusive γ l s₁ s₂ x₁ x₂ :
    isRwLock γ l s₁ x₁ ∗ isRwLock γ l s₂ x₂ ⊢@{IProp GF} False
  rwGuard_valid γ l s x mode :
    isRwLock γ l s x ∗ rwGuard γ mode ⊢@{IProp GF} ⌜GuardCompatible s mode⌝
  rwGuard_write_exclusive γ :
    rwGuard γ .write ∗ rwGuard γ .write ⊢@{IProp GF} False
  rwGuard_write_read_exclusive γ :
    rwGuard γ .write ∗ rwGuard γ .read ⊢@{IProp GF} False

  new_spec (x : Val) :
    ⊢@{IProp GF}
      ⦃ True ⦄
        hl(&new &x)
      ⦃ l, RET l; ∃ γ, isRwLock γ l .free x ⦄
  ptr_drop_spec (γ : name) (l : Val) (x : Loc) (v : Val) :
    ⊢@{IProp GF}
      ⦃ isRwLock γ l .free hl_val(#x) ∗ x ↦ v ⦄
        hl(&drop &l)
      ⦃ RET hl_val(#()); True ⦄
  write_acquire_spec (γ : name) (l x : Val) :
    ⊢@{IProp GF}
      ⟪ ∀ s, isRwLock γ l s x ⟫
        hl(&write_acquire &l) @ ∅
      ⟪ isRwLock γ l .write x ∗ rwGuard γ .write ∗ ⌜s = .free⌝ | RET x ⟫
  write_release_spec (γ : name) (l x : Val) :
    ⊢@{IProp GF}
      rwGuard γ .write -∗
      ⟪ isRwLock γ l .write x ⟫
        hl(&write_release &l) @ ∅
      ⟪ isRwLock γ l .free x | RET hl_val(#()) ⟫
  read_acquire_spec (γ : name) (l x : Val) :
    ⊢@{IProp GF}
      ⟪ ∀ s, isRwLock γ l s x ⟫
        hl(&read_acquire &l) @ ∅
      ⟪ rwGuard γ .read ∗
          ((isRwLock γ l (.read 1) x ∗ ⌜s = .free⌝) ∨
           (∃ n, isRwLock γ l (.read (n + 1)) x ∗ ⌜s = .read n⌝))
        | RET x ⟫
  read_release_spec (γ : name) (l x : Val) :
    ⊢@{IProp GF}
      rwGuard γ .read -∗
      ⟪ ∀ n, isRwLock γ l (.read (n + 1)) x ⟫
        hl(&read_release &l) @ ∅
      ⟪ (isRwLock γ l .free x ∗ ⌜n = 0⌝) ∨
          (isRwLock γ l (.read n) x ∗ ⌜n > 0⌝)
        | RET hl_val(#()) ⟫

instance instAPINameInhabited [HeapLangGS hlc GF] [api : API GF] :
    Inhabited api.name :=
  api.name_inhabited

instance instAPIIsRwLockTimeless [HeapLangGS hlc GF] [api : API GF] γ l s x :
    Timeless (api.isRwLock γ l s x) :=
  api.isRwLock_timeless γ l s x

instance instAPIRwGuardTimeless [HeapLangGS hlc GF] [api : API GF] γ mode :
    Timeless (api.rwGuard γ mode) :=
  api.rwGuard_timeless γ mode

def new : Val := hl_val(
  λ x, (ref(#0), x)
)

def read_acquire : Val := hl_val(
  rec acquire l :=
    let state := fst(l);
    let n := !state;
    if n < #0 then
      acquire l
    else if snd(cmpXchg(state, n, n + #1)) then
      snd(l)
    else
      acquire l
)

def write_acquire : Val := hl_val(
  rec acquire l :=
    if snd(cmpXchg(fst(l), #0, -#1)) then
      snd(l)
    else
      acquire l
)

def read_release : Val := hl_val(
  λ l, faa(fst(l), -#1); #()
)

def write_release : Val := hl_val(
  λ l, fst(l) ← #0
)

def drop : Val := hl_val(
  λ l, free(fst(l)); free(snd(l))
)

end RwLock

namespace Arc

/-- Public Arc/Weak interface. Arc and Weak share one ghost identity and exact
strong/explicit-weak counts, so their operations belong to one interface. -/
class API (GF : BundledGFunctors) [HeapLangGS hlc GF] where
  new : Val
  clone : Val
  get : Val
  downgrade : Val
  drop_strong : Val
  drop : Val
  weak_clone : Val
  weak_drop : Val
  weak_upgrade : Val

  name : Type
  [name_inhabited : Inhabited name]

  arcAuth : name → Nat → Nat → IProp GF
  isArc : name → Val → Val → IProp GF
  isWeak : name → Val → Val → IProp GF

  arcAuth_timeless γ n m : Timeless (arcAuth γ n m)
  isArc_timeless γ a x : Timeless (isArc γ a x)
  isWeak_timeless γ w x : Timeless (isWeak γ w x)

  arcAuth_exclusive γ n₁ m₁ n₂ m₂ :
    arcAuth γ n₁ m₁ ∗ arcAuth γ n₂ m₂ ⊢@{IProp GF} False
  arcAuth_isArc_valid γ n m a x :
    arcAuth γ n m ∗ isArc γ a x ⊢@{IProp GF} ⌜n > 0⌝
  arcAuth_isWeak_valid γ n m w x :
    arcAuth γ n m ∗ isWeak γ w x ⊢@{IProp GF} ⌜m > 0⌝
  isArc_agree γ a₁ a₂ x₁ x₂ :
    isArc γ a₁ x₁ ∗ isArc γ a₂ x₂ ⊢@{IProp GF} ⌜a₁ = a₂ ∧ x₁ = x₂⌝
  isWeak_agree γ w₁ w₂ x₁ x₂ :
    isWeak γ w₁ x₁ ∗ isWeak γ w₂ x₂ ⊢@{IProp GF} ⌜w₁ = w₂ ∧ x₁ = x₂⌝
  isArc_isWeak_agree γ a w x₁ x₂ :
    isArc γ a x₁ ∗ isWeak γ w x₂ ⊢@{IProp GF} ⌜a = w ∧ x₁ = x₂⌝

  new_spec (x : Val) :
    ⊢@{IProp GF}
      ⦃ True ⦄
        hl(&new &x)
      ⦃ a, RET a; ∃ γ, arcAuth γ 1 0 ∗ isArc γ a x ⦄
  clone_spec (γ : name) (a x : Val) :
    ⊢@{IProp GF}
      isArc γ a x -∗
      ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
        hl(&clone &a) @ ∅
      ⟪ arcAuth γ (n + 1) m ∗ isArc γ a x ∗ isArc γ a x
        | RET a ⟫
  get_spec (γ : name) (a x : Val) :
    ⊢@{IProp GF}
      ⦃ isArc γ a x ⦄
        hl(&get &a)
      ⦃ RET x; isArc γ a x ⦄
  downgrade_spec (γ : name) (a x : Val) :
    ⊢@{IProp GF}
      isArc γ a x -∗
      ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
        hl(&downgrade &a) @ ∅
      ⟪ arcAuth γ n (m + 1) ∗ isArc γ a x ∗ isWeak γ a x
        | RET a ⟫
  /-- Atomic strong-count decrement. Returning `true` means this handle was the
  last strong reference; the caller then also owns the control block's former
  *implicit* weak reference as an explicit `isWeak` handle. -/
  drop_strong_spec (γ : name) (a x : Val) :
    ⊢@{IProp GF}
      isArc γ a x -∗
      ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
        hl(&drop_strong &a) @ ∅
      ⟪ (⌜n = 1⌝ ∗ arcAuth γ 0 (m + 1) ∗ isWeak γ a x) ∨
          (⌜n > 1⌝ ∗ arcAuth γ (n - 1) m)
        | RET hl_val(#(decide (n = 1))) ⟫
  /-- Derived composite. `dropT` is the client-supplied payload destructor and
  `Q` its precondition, which the client only has to provide when this really is
  the last strong reference. `Q` takes the place of the former hard-wired
  `lastStrongResource`, so `Arc` no longer mentions `RwLock` at all. -/
  drop_spec (γ : name) (dropT a x : Val) (n m : Nat) (Q : IProp GF) :
    ⊢@{IProp GF}
      (⦃ Q ⦄ hl(&dropT &x) ⦃ RET hl_val(#()); True ⦄) -∗
      ⦃ isArc γ a x ∗ arcAuth γ n m ∗ (if n = 1 then Q else True) ⦄
        hl(&drop &dropT &a)
      ⦃ RET hl_val(#()); arcAuth γ (n - 1) m ⦄
  weak_clone_spec (γ : name) (w x : Val) :
    ⊢@{IProp GF}
      isWeak γ w x -∗
      ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
        hl(&weak_clone &w) @ ∅
      ⟪ arcAuth γ n (m + 1) ∗ isWeak γ w x ∗ isWeak γ w x
        | RET w ⟫
  weak_drop_spec (γ : name) (w x : Val) :
    ⊢@{IProp GF}
      isWeak γ w x -∗
      ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
        hl(&weak_drop &w) @ ∅
      ⟪ arcAuth γ n (m - 1) | RET hl_val(#()) ⟫
  weak_upgrade_spec (γ : name) (w x : Val) (n m : Nat) :
    ⊢@{IProp GF}
      ⦃ isWeak γ w x ∗ arcAuth γ n m ⦄
        hl(&weak_upgrade &w)
      ⦃ r, RET r;
          (⌜n = 0⌝ ∗ ⌜r = hl_val(none())⌝ ∗ arcAuth γ 0 (m - 1)) ∨
          (⌜n > 0⌝ ∗ ⌜r = hl_val(some(&w))⌝ ∗
            arcAuth γ (n + 1) (m - 1) ∗ isArc γ w x) ⦄

instance instAPINameInhabited [HeapLangGS hlc GF] [api : API GF] :
    Inhabited api.name :=
  api.name_inhabited

instance instAPIArcAuthTimeless [HeapLangGS hlc GF] [api : API GF] γ n m :
    Timeless (api.arcAuth γ n m) :=
  api.arcAuth_timeless γ n m

instance instAPIIsArcTimeless [HeapLangGS hlc GF] [api : API GF] γ a x :
    Timeless (api.isArc γ a x) :=
  api.isArc_timeless γ a x

instance instAPIIsWeakTimeless [HeapLangGS hlc GF] [api : API GF] γ w x :
    Timeless (api.isWeak γ w x) :=
  api.isWeak_timeless γ w x

def strongPtr : Val := hl_val(
  λ a, fst(fst(a))
)

def weakPtr : Val := hl_val(
  λ a, snd(fst(a))
)

/-- The physical weak counter includes one implicit weak reference while the
strong count is positive. -/
def new : Val := hl_val(
  λ x,
    let strong := ref(#1);
    let weak := ref(#1);
    ((strong, weak), x)
)

def clone : Val := hl_val(
  λ a, faa(&strongPtr(a), #1); a
)

def get : Val := hl_val(
  λ a, snd(a)
)

def downgrade : Val := hl_val(
  λ a, faa(&weakPtr(a), #1); a
)

/-- Internal first stage of `drop`. -/
def dropStrong : Val := hl_val(
  λ a,
    let old := faa(&strongPtr(a), -#1);
    old = #1
)

/-- Internal weak-count stage shared by `Arc.drop` and `Weak.drop`. The
implicit-weak protocol guarantees that observing `old = 1` means the strong
count is already zero. -/
def dropWeak : Val := hl_val(
  λ w,
    let old := faa(&weakPtr(w), -#1);
    if old = #1 then
      (free(&strongPtr(w)); free(&weakPtr(w)))
    else
      #()
)

/-- Internal last-strong cleanup stage. `dropT` is the client-supplied
destructor for the payload, so `Arc` itself stays agnostic to the payload
type (in particular it is no longer hard-wired to `RwLock`). -/
def closeLastStrong : Val := hl_val(
  λ dropT a,
    dropT (snd(a));
    &dropWeak(a)
)

def drop : Val := hl_val(
  λ dropT a,
    if &dropStrong(a) then
      &closeLastStrong dropT a
    else
      #()
)

end Arc

namespace Weak

def clone : Val := hl_val(
  λ w, faa(&Arc.weakPtr(w), #1); w
)

/-- Internal non-consuming CAS stage of `upgrade`. -/
def tryUpgrade : Val := hl_val(
  rec tryUpgrade w :=
    let strong := &Arc.strongPtr(w);
    let n := !strong;
    if n = #0 then
      none()
    else if snd(cmpXchg(strong, n, n + #1)) then
      some(w)
    else
      tryUpgrade w
)

/-- Consuming user-facing upgrade, defined by `tryUpgrade` followed by one weak
drop. This is intentionally different from Rust's borrowing `Weak::upgrade`. -/
def upgrade : Val := hl_val(
  λ w,
    let result := &tryUpgrade(w);
    &Arc.dropWeak(w);
    result
)

def drop : Val := Arc.dropWeak

end Weak

/-! ### The reader-credit camera

`Credit = Nat` (later credits) has a unit but is indivisible; `Qp` is divisible but
strictly positive, so it has no unit and cannot be the value type of an `Auth`.
Non-negative rationals have both, which is exactly what makes a read permit
splittable while still letting `● 0` mean "no reader holds this lock". -/
abbrev RwCredit := { q : Rat // 0 ≤ q }

namespace RwCredit

instance : Add RwCredit := ⟨fun x y => ⟨x.val + y.val, by have := x.2; have := y.2; grind⟩⟩
instance : Zero RwCredit := ⟨⟨0, by grind⟩⟩
instance : One RwCredit := ⟨⟨1, by grind⟩⟩
instance : NatCast RwCredit := ⟨fun n => ⟨(n : Rat), Rat.natCast_nonneg⟩⟩

/-- Every fraction is a credit.  `Qp` is strictly positive, `RwCredit` merely
    non-negative, so this direction is always available. -/
def ofQp (q : Qp) : RwCredit := ⟨q.val, by have := q.2; grind⟩

@[simp] theorem ofQp_val (q : Qp) : (ofQp q).val = q.val := rfl
@[simp] theorem ofQp_one : ofQp 1 = (1 : RwCredit) := Subtype.ext rfl
theorem ofQp_pos (q : Qp) : 0 < (ofQp q).val := q.2



theorem ext {x y : RwCredit} (h : x.val = y.val) : x = y := Subtype.ext h

theorem add_comm (x y : RwCredit) : x + y = y + x := ext (Rat.add_comm ..)
@[simp] theorem zero_add (x : RwCredit) : (0 : RwCredit) + x = x := ext (Rat.zero_add _)
@[simp] theorem add_zero (x : RwCredit) : x + (0 : RwCredit) = x := ext (Rat.add_zero _)

@[simp] theorem natCast_zero : ((0 : Nat) : RwCredit) = 0 := ext rfl
@[simp] theorem natCast_succ (n : Nat) : ((n + 1 : Nat) : RwCredit) = (n : RwCredit) + 1 :=
  ext (by show ((n + 1 : Nat) : Rat) = (n : Rat) + 1; push_cast; rfl)

scoped instance : _root_.Std.Associative (Add.add (α := RwCredit)) :=
  ⟨fun _ _ _ => ext (Rat.add_assoc ..)⟩
scoped instance : _root_.Std.Commutative (Add.add (α := RwCredit)) :=
  ⟨fun _ _ => ext (Rat.add_comm ..)⟩
scoped instance : _root_.Std.LeftIdentity (Add.add (α := RwCredit)) (0 : RwCredit) where
scoped instance : _root_.Std.LawfulLeftIdentity (Add.add (α := RwCredit)) (0 : RwCredit) :=
  ⟨fun _ => ext (Rat.zero_add _)⟩
scoped instance : LeftCancelAdd RwCredit :=
  ⟨fun {x₁ x₂ y} h => ext (by
    have h' : y.val + x₁.val = y.val + x₂.val := congrArg Subtype.val h
    grind)⟩

scoped instance : COFE RwCredit := COFE.ofDiscrete _ Eq_Equivalence
scoped instance : OFE.Discrete RwCredit := ⟨congrArg id⟩
scoped instance : OFE.Leibniz RwCredit := ⟨congrArg id⟩
scoped instance : UCMRA RwCredit := CommMonoidLike.instUCMRA
scoped instance : CMRA.Discrete RwCredit := CommMonoidLike.instDiscrete
scoped instance instCancelable {a : RwCredit} : CMRA.Cancelable a where
  cancelableN {_ _ _} _ :=
    .of_eq ∘ LeftCancelAdd.cancel_left ∘ OFE.eq_of_eqv ∘ OFE.Discrete.discrete

end RwCredit

open scoped RwCredit

abbrev RwLockF := AuthURF (constOF RwCredit)

/-- Ghost-state availability for the rwlock.  Previously the rwlock silently reused
    the *later-credit* functor (both were `AuthURF (constOF Credit)`); now that the
    reader count is rational it needs its own slot, declared like `ArcG`. -/
class RwLockG (GF : BundledGFunctors) where
  [rwLockG : ElemG GF RwLockF]

attribute [reducible, instance] RwLockG.rwLockG

abbrev ArcMeta := LeibnizO (Val × Val)
abbrev ArcRes := Option (Agree ArcMeta) × (Credit × Credit)

instance instSafeAPIUCMRAProd {α β : Type _} [UCMRA α] [UCMRA β] :
    UCMRA (α × β) where
  unit := (CMRA.unit, CMRA.unit)
  unit_valid := ⟨CMRA.unit_valid, CMRA.unit_valid⟩
  unit_left_id := ⟨CMRA.unit_left_id, CMRA.unit_left_id⟩
  pcore_unit := by
    simp only [CMRA.pcore, Prod.pcore]
    apply OFE.equiv_dist.mpr
    intro n
    exact Option.bind_ne
      (fun a a' ha => Option.bind_ne
        (fun b b' hb => some_dist_some.mpr (dist_prod_ext ha hb))
        (CMRA.pcore_unit (α := β)).dist)
      (CMRA.pcore_unit (α := α)).dist

abbrev ArcF := AuthURF (constOF ArcRes)

class ArcG (GF : BundledGFunctors) where
  [arcG : ElemG GF ArcF]

attribute [reducible, instance] ArcG.arcG

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [RwLockG GF]

def rwQ1_4 : Qp := Qp.half (Qp.half 1)

/-- Scale a fraction by `3/4`, spelled with `half` so that no multiplication on `Qp`
    is needed.  A write permit of "strength `q`" owns `scale3_4 q` of the lock's
    authority; the invariant keeps the remaining `1/4`, which is what keeps
    `isRwLock … .write …` a non-trivial assertion. -/
def scale3_4 (q : Qp) : Qp := Qp.half q + Qp.half (Qp.half q)

def rwQ3_4 : Qp := scale3_4 1

@[simp] theorem scale3_4_one : scale3_4 1 = rwQ3_4 := rfl

@[simp] theorem scale3_4_val (q : Qp) : (scale3_4 q).val = q.val * 3 / 4 := by
  simp [scale3_4, Qp.half]
  grind

theorem scale3_4_add (q₁ q₂ : Qp) : scale3_4 (q₁ + q₂) = scale3_4 q₁ + scale3_4 q₂ := by
  apply Subtype.ext
  simp
  grind

/-- The defining property: a full write permit plus the invariant's quarter is one. -/
theorem scale3_4_le_one_iff (q : Qp) : (rwQ1_4 + scale3_4 q).val ≤ 1 ↔ q.val ≤ 1 := by
  simp [rwQ1_4, Qp.half]
  grind

private theorem rwQsum : rwQ1_4 + rwQ3_4 = 1 := by
  apply Subtype.ext
  simp [rwQ1_4, rwQ3_4, scale3_4, Qp.half]
  grind

private theorem rwQ3_twice_invalid : ¬ (rwQ3_4 + rwQ3_4).val ≤ 1 := by
  have hsum : rwQ3_4 + rwQ3_4 = 1 + Qp.half 1 := by
    apply Subtype.ext
    simp [rwQ3_4, scale3_4, Qp.half]
    grind
  rw [hsum, Qp.val_add]
  have hpos := (Qp.half (1 : Qp)).2
  have hone : (1 : Qp).val = 1 := rfl
  grind

private theorem rwOwnOneOpInvalid {dq : DFrac} (h : ✓ DFrac.own 1 • dq) : False := by
  have hlt := DFrac.valid_own_op h
  have hone : (1 : Qp).val = 1 := rfl
  grind

/-- No positive read credit can coexist with an authority claiming zero readers.
    Generalised from `◯ 1` to `◯ q`: with a rational credit, *any* fraction of a read
    permit is enough to prove the lock is read-held. -/
private theorem rwAuthZeroFragInvalid {dq : DFrac} {q : Qp}
    (h : ✓ ((●{dq} (0 : RwCredit) : Auth RwCredit) • ◯ (RwCredit.ofQp q))) : False := by
  have hinc := (Auth.both_dfrac_valid_discrete.mp h).2.1
  rcases hinc with ⟨c, hc⟩
  have hc' := eq_of_eqv hc
  rw [CommMonoidLike.op_eq] at hc'
  have hval : (0 : Rat) = (RwCredit.ofQp q).val + c.val := congrArg Subtype.val hc'
  have hq := RwCredit.ofQp_pos q
  have hc0 := c.2
  grind

private theorem rwAuthZeroFragOneInvalid {dq : DFrac}
    (h : ✓ ((●{dq} (0 : RwCredit) : Auth RwCredit) • ◯ (1 : RwCredit))) : False :=
  rwAuthZeroFragInvalid (q := 1) h

def rwStateOwn (γ : GName) : RwLock.State → IProp GF
  | .free => iOwn (F := RwLockF) γ (● (0 : RwCredit))
  | .read n => iOwn (F := RwLockF) γ (● (n : RwCredit))
  | .write => iOwn (F := RwLockF) γ (●{DFrac.own rwQ1_4} (0 : RwCredit))

/-- Client-owned physical and authoritative lock state. -/
def isRwLock (γ : GName) (l : Val) (s : RwLock.State) (x : Val) : IProp GF := iprop%
  ∃ p : Loc, ⌜l = hl_val((#p, &x))⌝ ∗ ⌜RwLock.State.Valid s⌝ ∗
    p ↦ hl_val(#(RwLock.State.counter s)) ∗ rwStateOwn γ s

/-- A **fractional** read permit.  Any positive fraction already proves the lock is
    read-held; only a full permit (`q = 1`) can be handed back to `read_release`.
    This is what lets a client lend part of its read permission to a data structure
    invariant while retaining enough to keep reasoning about the lock state. -/
def rwGuardFrac (γ : GName) : RwLock.Mode → Qp → IProp GF
  | .read,  q => iOwn (F := RwLockF) γ (◯ (RwCredit.ofQp q))
  | .write, q => iOwn (F := RwLockF) γ (●{DFrac.own (scale3_4 q)} (0 : RwCredit))

/-- One linear release permit: the full (`q = 1`) share of its mode. -/
def rwGuard (γ : GName) (mode : RwLock.Mode) : IProp GF := rwGuardFrac (GF := GF) γ mode 1

theorem rwGuard_eq (γ : GName) (mode : RwLock.Mode) :
    rwGuard (GF := GF) γ mode = rwGuardFrac γ mode 1 := rfl

section ArcResources

variable [ArcG GF]

def arcMeta (a x : Val) : Option (Agree ArcMeta) :=
  some (toAgree ⟨(a, x)⟩)

def arcStateRes (a x : Val) (strong weak : Nat) : ArcRes :=
  (arcMeta a x, (strong, weak))

def arcMetaRes (a x : Val) : ArcRes :=
  (arcMeta a x, (0, 0))

def arcStrongRes : ArcRes :=
  (none, (1, 0))

def arcWeakRes : ArcRes :=
  (none, (0, 1))

def arcStateOwn (γ : GName) (a x : Val) (strong weak : Nat) : IProp GF :=
  iOwn (F := ArcF) γ (● arcStateRes a x strong weak)

def arcMetaOwn (γ : GName) (a x : Val) : IProp GF :=
  iOwn (F := ArcF) γ (◯ arcMetaRes a x)

def arcStrongOwn (γ : GName) : IProp GF :=
  iOwn (F := ArcF) γ (◯ arcStrongRes)

def arcWeakOwn (γ : GName) : IProp GF :=
  iOwn (F := ArcF) γ (◯ arcWeakRes)

noncomputable def arcPhysical (strong weak : Loc) : Nat → Nat → IProp GF
  | 0, 0 => iprop% True
  | 0, m + 1 =>
      iprop% strong ↦ hl_val(#(0 : Int)) ∗ weak ↦ hl_val(#((m + 1 : Nat) : Int))
  | n + 1, m =>
      iprop% strong ↦ hl_val(#((n + 1 : Nat) : Int)) ∗
        weak ↦ hl_val(#((m + 1 : Nat) : Int))

/-- Exact client-owned Arc state. The indices are the strong count and the
explicit weak count; the Rust-style implicit weak is not included. -/
noncomputable def arcAuth (γ : GName) (strong weak : Nat) : IProp GF := iprop%
  ∃ ps pw : Loc, ∃ a x : Val,
    ⌜a = hl_val(((#ps, #pw), &x))⌝ ∗
    arcPhysical ps pw strong weak ∗
    arcStateOwn γ a x strong weak

/-- One strong-reference token tied to an Arc runtime value and payload. -/
def isArc (γ : GName) (a x : Val) : IProp GF := iprop%
  ∃ ps pw : Loc,
    ⌜a = hl_val(((#ps, #pw), &x))⌝ ∗
    arcMetaOwn γ a x ∗
    arcStrongOwn γ

/-- One weak-reference token tied to the same control block and payload. -/
def isWeak (γ : GName) (w x : Val) : IProp GF := iprop%
  ∃ ps pw : Loc,
    ⌜w = hl_val(((#ps, #pw), &x))⌝ ∗
    arcMetaOwn γ w x ∗
    arcWeakOwn γ

instance instIsRwLockTimeless (γ : GName) (l : Val) (s : RwLock.State) (x : Val) :
    Timeless (PROP := IProp GF) (isRwLock γ l s x) := by
  unfold isRwLock rwStateOwn
  cases s <;> infer_instance

instance instRwGuardFracTimeless (γ : GName) (mode : RwLock.Mode) (q : Qp) :
    Timeless (PROP := IProp GF) (rwGuardFrac γ mode q) := by
  unfold rwGuardFrac
  cases mode <;> infer_instance

instance instRwGuardTimeless (γ : GName) (mode : RwLock.Mode) :
    Timeless (PROP := IProp GF) (rwGuard γ mode) := by
  unfold rwGuard rwGuardFrac
  cases mode <;> infer_instance

private instance instArcStateOwnTimeless (γ : GName) (a x : Val) (strong weak : Nat) :
    Timeless (PROP := IProp GF) (arcStateOwn γ a x strong weak) := by
  unfold arcStateOwn arcStateRes arcMeta
  infer_instance

instance instArcAuthTimeless (γ : GName) (strong weak : Nat) :
    Timeless (PROP := IProp GF) (arcAuth γ strong weak) := by
  unfold arcAuth
  cases strong <;> cases weak <;> simp [arcPhysical] <;> infer_instance

instance instIsArcTimeless (γ : GName) (a x : Val) :
    Timeless (PROP := IProp GF) (isArc γ a x) := by
  unfold isArc arcMetaOwn arcStrongOwn
  infer_instance

instance instIsWeakTimeless (γ : GName) (w x : Val) :
    Timeless (PROP := IProp GF) (isWeak γ w x) := by
  unfold isWeak arcMetaOwn arcWeakOwn
  infer_instance

instance instArcMetaOwnPersistent (γ : GName) (a x : Val) :
    Persistent (PROP := IProp GF) (arcMetaOwn γ a x) := by
  letI : CMRA.CoreId (0 : Credit) := ⟨by rfl⟩
  unfold arcMetaOwn arcMetaRes arcMeta
  infer_instance

end ArcResources

namespace RwLock

section ResourceLaws

/-- The abstract state always matches a valid physical counter encoding. -/
theorem isRwLock_valid (γ : GName) (l : Val) (s : State) (x : Val) :
    isRwLock γ l s x ⊢@{IProp GF} ⌜State.Valid s⌝ := by
  unfold isRwLock
  iintro ⟨%p, %Hl, %Hs, _⟩
  itrivial

/-- The exact physical/authoritative lock state is linear. -/
theorem isRwLock_exclusive (γ : GName) (l : Val) (s₁ s₂ : State) (x₁ x₂ : Val) :
    isRwLock γ l s₁ x₁ ∗ isRwLock γ l s₂ x₂ ⊢@{IProp GF} False := by
  unfold isRwLock
  iintro ⟨H1, H2⟩
  icases H1 with ⟨%p1, %Hl1, %_, Hp1, _⟩
  icases H2 with ⟨%p2, %Hl2, %_, Hp2, _⟩
  have hp : p1 = p2 := by
    rw [Hl1] at Hl2
    exact BaseLit.loc.inj (Val.lit.inj (Val.pair.inj Hl2).1)
  subst p2
  icases (pointsTo_ne (l₁ := p1) (l₂ := p1)) $$ Hp1 Hp2 with %Hne
  ipureintro
  exact Hne rfl

/-- Permits of the same mode add up, so a full permit can be split and later
    reassembled.  Only a reassembled *full* permit is accepted by the release specs,
    which is what forces a client to reclaim every lent-out share before giving the
    lock back. -/
theorem rwGuardFrac_split (γ : GName) (mode : RwLock.Mode) (q₁ q₂ : Qp) :
    rwGuardFrac (GF := GF) γ mode (q₁ + q₂) ⊣⊢
      rwGuardFrac γ mode q₁ ∗ rwGuardFrac γ mode q₂ := by
  unfold rwGuardFrac
  cases mode <;> dsimp only []
  · have h : (◯ (RwCredit.ofQp (q₁ + q₂)) : Auth RwCredit)
        = (◯ (RwCredit.ofQp q₁) : Auth RwCredit) • (◯ (RwCredit.ofQp q₂) : Auth RwCredit) := by
      rw [← Auth.frag_op]
      exact congrArg _ (RwCredit.ext rfl)
    rw [h]
    exact iOwn_op
  · have h : (●{DFrac.own (scale3_4 (q₁ + q₂))} (0 : RwCredit) : Auth RwCredit)
        = (●{DFrac.own (scale3_4 q₁)} (0 : RwCredit) : Auth RwCredit)
          • (●{DFrac.own (scale3_4 q₂)} (0 : RwCredit) : Auth RwCredit) := by
      rw [scale3_4_add, ← DFrac.op_own]
      exact eq_of_eqv Auth.auth_dfrac_op
    rw [h]
    exact iOwn_op

/-- **Any** positive share already pins the lock to that mode.  This is the point of
    making permits fractional: a thread can lend most of its permit away — e.g. into a
    data-structure invariant — and still know the lock has not changed hands. -/
theorem rwGuardFrac_valid (γ : GName) (l : Val) (s : State) (x : Val)
    (mode : Mode) (q : Qp) :
    isRwLock γ l s x ∗ rwGuardFrac γ mode q ⊢@{IProp GF} ⌜GuardCompatible s mode⌝ := by
  unfold isRwLock rwStateOwn rwGuardFrac
  iintro ⟨Hs, Hg⟩
  icases Hs with ⟨%p, %Hl, %Hvalid, Hp, Ha⟩
  cases s <;> cases mode <;> dsimp only [] at *
  · ihave HvI := (iOwn_cmraValid_op (F := RwLockF)
      (a1 := (● (0 : RwCredit) : Auth RwCredit))
      (a2 := (◯ (RwCredit.ofQp q) : Auth RwCredit))) $$ [Ha Hg]
    · isplitl [Ha] <;> iassumption
    icases internalCmraValid_discrete (A := Auth RwCredit) $$ HvI with %Hv
    ipureintro
    exact (rwAuthZeroFragInvalid Hv).elim
  · ihave HvI := (iOwn_cmraValid_op (F := RwLockF)
      (a1 := (● (0 : RwCredit) : Auth RwCredit))
      (a2 := (●{DFrac.own (scale3_4 q)} (0 : RwCredit) : Auth RwCredit))) $$ [Ha Hg]
    · isplitl [Ha] <;> iassumption
    icases internalCmraValid_discrete (A := Auth RwCredit) $$ HvI with %Hv
    ipureintro
    exact (rwOwnOneOpInvalid (Auth.auth_dfrac_op_valid.mp Hv).1).elim
  · cases Hvalid with
    | read n =>
      ipureintro
      exact GuardCompatible.read n
  · ihave HvI := (iOwn_cmraValid_op (F := RwLockF)
      (a1 := (● (_ : RwCredit) : Auth RwCredit))
      (a2 := (●{DFrac.own (scale3_4 q)} (0 : RwCredit) : Auth RwCredit))) $$ [Ha Hg]
    · isplitl [Ha] <;> iassumption
    icases internalCmraValid_discrete (A := Auth RwCredit) $$ HvI with %Hv
    ipureintro
    exact (rwOwnOneOpInvalid (Auth.auth_dfrac_op_valid.mp Hv).1).elim
  · ihave HvI := (iOwn_cmraValid_op (F := RwLockF)
      (a1 := (●{DFrac.own rwQ1_4} (0 : RwCredit) : Auth RwCredit))
      (a2 := (◯ (RwCredit.ofQp q) : Auth RwCredit))) $$ [Ha Hg]
    · isplitl [Ha] <;> iassumption
    icases internalCmraValid_discrete (A := Auth RwCredit) $$ HvI with %Hv
    ipureintro
    exact (rwAuthZeroFragInvalid Hv).elim
  · ipureintro
    exact GuardCompatible.write

/-- A state and guard can coexist only in the matching held mode. -/
theorem rwGuard_valid (γ : GName) (l : Val) (s : State) (x : Val) (mode : Mode) :
    isRwLock γ l s x ∗ rwGuard γ mode ⊢@{IProp GF} ⌜GuardCompatible s mode⌝ :=
  rwGuardFrac_valid γ l s x mode 1

theorem rwGuard_write_exclusive (γ : GName) :
    rwGuard γ .write ∗ rwGuard γ .write ⊢@{IProp GF} False := by
  unfold rwGuard rwGuardFrac
  simp only [scale3_4_one]
  iintro ⟨H1, H2⟩
  ihave HvI := (iOwn_cmraValid_op (F := RwLockF)
    (a1 := (●{DFrac.own rwQ3_4} (0 : RwCredit) : Auth RwCredit))
    (a2 := (●{DFrac.own rwQ3_4} (0 : RwCredit) : Auth RwCredit))) $$ [H1 H2]
  · isplitl [H1] <;> iassumption
  icases internalCmraValid_discrete (A := Auth RwCredit) $$ HvI with %Hv
  iclear HvI
  ipureintro
  exact rwQ3_twice_invalid (Auth.auth_dfrac_op_valid.mp Hv).1

/-- A writer guard cannot coexist with a reader guard for the same lock. -/
theorem rwGuard_write_read_exclusive (γ : GName) :
    rwGuard γ .write ∗ rwGuard γ .read ⊢@{IProp GF} False := by
  unfold rwGuard rwGuardFrac
  simp only [scale3_4_one]
  iintro ⟨Hw, Hr⟩
  ihave HvI := (iOwn_cmraValid_op (F := RwLockF)
    (a1 := (●{DFrac.own rwQ3_4} (0 : RwCredit) : Auth RwCredit))
    (a2 := (◯ (RwCredit.ofQp 1) : Auth RwCredit))) $$ [Hw Hr]
  · isplitl [Hw] <;> iassumption
  icases internalCmraValid_discrete (A := Auth RwCredit) $$ HvI with %Hv
  iclear HvI
  ipureintro
  exact rwAuthZeroFragOneInvalid Hv

-- Multiple read guards are intentionally compatible.

end ResourceLaws

end RwLock

namespace Arc

variable [ArcG GF]
omit [RwLockG GF]

private theorem arcStrongRes_included_positive (a x : Val) (n m : Nat)
    (h : arcStrongRes ≼ arcStateRes a x n m) : n > 0 := by
  obtain ⟨rest, hrest⟩ := h
  have hs := congrArg (fun r : ArcRes => r.2.1) (eq_of_eqv hrest)
  change n = 1 + rest.2.1 at hs
  omega

private theorem arcWeakRes_included_positive (a x : Val) (n m : Nat)
    (h : arcWeakRes ≼ arcStateRes a x n m) : m > 0 := by
  obtain ⟨rest, hrest⟩ := h
  have hw := congrArg (fun r : ArcRes => r.2.2) (eq_of_eqv hrest)
  change m = 1 + rest.2.2 at hw
  omega

private theorem arcMetaRes_included_agree (a₀ a x₀ x : Val) (n m : Nat)
    (h : arcMetaRes a x ≼ arcStateRes a₀ x₀ n m) : a₀ = a ∧ x₀ = x := by
  obtain ⟨rest, hrest⟩ := h
  have hmeta : arcMeta a x ≼ arcMeta a₀ x₀ := ⟨rest.1, hrest.1⟩
  change
    some (toAgree (⟨(a, x)⟩ : ArcMeta)) ≼
      some (toAgree (⟨(a₀, x₀)⟩ : ArcMeta)) at hmeta
  have hpairs : (a, x) = (a₀, x₀) := by
    rcases Option.some_inc_some_iff.mp hmeta with heq | hinc
    · exact congrArg LeibnizO.car
        (OFE.leibniz.mp (Agree.toAgree_inj heq))
    · exact congrArg LeibnizO.car
        (Agree.toAgree_included_L.mp hinc)
  exact ⟨(congrArg Prod.fst hpairs).symm, (congrArg Prod.snd hpairs).symm⟩

private theorem arcStateOwn_meta_agree
    (γ : GName) (a₀ a x₀ x : Val) (n m : Nat) :
    arcStateOwn γ a₀ x₀ n m ∗ arcMetaOwn γ a x ⊢@{IProp GF}
      ⌜a₀ = a ∧ x₀ = x⌝ := by
  unfold arcStateOwn arcMetaOwn
  iintro ⟨Hauth, Hmeta⟩
  ihave HvI := (iOwn_cmraValid_op (F := ArcF)
    (a1 := (● arcStateRes a₀ x₀ n m : Auth ArcRes))
    (a2 := (◯ arcMetaRes a x : Auth ArcRes))) $$ [Hauth Hmeta]
  · isplitl [Hauth] <;> iassumption
  icases internalCmraValid_discrete (A := Auth ArcRes) $$ HvI with %Hv
  ipureintro
  exact arcMetaRes_included_agree a₀ a x₀ x n m
    (Auth.auth_both_valid_discrete.mp Hv).1

private theorem arcMetaOwn_agree (γ : GName) (a₁ a₂ x₁ x₂ : Val) :
    arcMetaOwn γ a₁ x₁ ∗ arcMetaOwn γ a₂ x₂ ⊢@{IProp GF}
      ⌜a₁ = a₂ ∧ x₁ = x₂⌝ := by
  unfold arcMetaOwn
  iintro ⟨H1, H2⟩
  ihave HvI := (iOwn_cmraValid_op (F := ArcF)
    (a1 := (◯ arcMetaRes a₁ x₁ : Auth ArcRes))
    (a2 := (◯ arcMetaRes a₂ x₂ : Auth ArcRes))) $$ [H1 H2]
  · isplitl [H1] <;> iassumption
  icases internalCmraValid_discrete (A := Auth ArcRes) $$ HvI with %Hv
  have Hmeta : ✓ (arcMeta a₁ x₁ • arcMeta a₂ x₂) :=
    (Auth.frag_op_valid.mp Hv).1
  have Hagree :
      ✓ (toAgree (⟨(a₁, x₁)⟩ : ArcMeta) • toAgree (⟨(a₂, x₂)⟩ : ArcMeta)) :=
    Hmeta
  have Hpair : (a₁, x₁) = (a₂, x₂) :=
    congrArg LeibnizO.car (toAgree_op_valid_iff_eq.mp Hagree)
  ipureintro
  exact ⟨congrArg Prod.fst Hpair, congrArg Prod.snd Hpair⟩

/-- The exact physical/authoritative Arc state is linear. -/
theorem arcAuth_exclusive (γ : GName) (n₁ m₁ n₂ m₂ : Nat) :
    arcAuth γ n₁ m₁ ∗ arcAuth γ n₂ m₂ ⊢@{IProp GF} False := by
  unfold arcAuth arcStateOwn
  iintro ⟨H1, H2⟩
  icases H1 with ⟨%_, %_, %a₁, %x₁, %_, _, Hown1⟩
  icases H2 with ⟨%_, %_, %a₂, %x₂, %_, _, Hown2⟩
  ihave HvI := (iOwn_cmraValid_op (F := ArcF)
    (a1 := (● arcStateRes a₁ x₁ n₁ m₁ : Auth ArcRes))
    (a2 := (● arcStateRes a₂ x₂ n₂ m₂ : Auth ArcRes))) $$ [Hown1 Hown2]
  · isplitl [Hown1] <;> iassumption
  icases internalCmraValid_discrete (A := Auth ArcRes) $$ HvI with %Hv
  ipureintro
  exact (Auth.auth_op_valid.mp Hv).elim

/-- A strong token requires a positive strong count. -/
theorem arcAuth_isArc_valid (γ : GName) (n m : Nat) (a x : Val) :
    arcAuth γ n m ∗ isArc γ a x ⊢@{IProp GF} ⌜n > 0⌝ := by
  unfold arcAuth isArc arcStateOwn arcMetaOwn arcStrongOwn
  iintro ⟨Hauth, Harc⟩
  icases Hauth with ⟨%_, %_, %a₀, %x₀, %_, _, Hown⟩
  icases Harc with ⟨%_, %_, %_, _, Hstrong⟩
  ihave HvI := (iOwn_cmraValid_op (F := ArcF)
    (a1 := (● arcStateRes a₀ x₀ n m : Auth ArcRes))
    (a2 := (◯ arcStrongRes : Auth ArcRes))) $$ [Hown Hstrong]
  · isplitl [Hown] <;> iassumption
  icases internalCmraValid_discrete (A := Auth ArcRes) $$ HvI with %Hv
  ipureintro
  exact arcStrongRes_included_positive a₀ x₀ n m
    (Auth.auth_both_valid_discrete.mp Hv).1

/-- A weak token requires a positive explicit weak count. -/
theorem arcAuth_isWeak_valid (γ : GName) (n m : Nat) (w x : Val) :
    arcAuth γ n m ∗ isWeak γ w x ⊢@{IProp GF} ⌜m > 0⌝ := by
  unfold arcAuth isWeak arcStateOwn arcMetaOwn arcWeakOwn
  iintro ⟨Hauth, Hweak⟩
  icases Hauth with ⟨%_, %_, %a₀, %x₀, %_, _, Hown⟩
  icases Hweak with ⟨%_, %_, %_, _, Htoken⟩
  ihave HvI := (iOwn_cmraValid_op (F := ArcF)
    (a1 := (● arcStateRes a₀ x₀ n m : Auth ArcRes))
    (a2 := (◯ arcWeakRes : Auth ArcRes))) $$ [Hown Htoken]
  · isplitl [Hown] <;> iassumption
  icases internalCmraValid_discrete (A := Auth ArcRes) $$ HvI with %Hv
  ipureintro
  exact arcWeakRes_included_positive a₀ x₀ n m
    (Auth.auth_both_valid_discrete.mp Hv).1

/-- Strong clones for one ghost identity agree on runtime value and payload. -/
theorem isArc_agree (γ : GName) (a₁ a₂ x₁ x₂ : Val) :
    isArc γ a₁ x₁ ∗ isArc γ a₂ x₂ ⊢@{IProp GF} ⌜a₁ = a₂ ∧ x₁ = x₂⌝ := by
  unfold isArc
  iintro ⟨H1, H2⟩
  icases H1 with ⟨%_, %_, %_, Hmeta1, _⟩
  icases H2 with ⟨%_, %_, %_, Hmeta2, _⟩
  ihave Hagree := (arcMetaOwn_agree γ a₁ a₂ x₁ x₂) $$ [Hmeta1 Hmeta2]
  · isplitl [Hmeta1] <;> iassumption
  iexact Hagree

/-- Weak clones for one ghost identity agree on runtime value and payload. -/
theorem isWeak_agree (γ : GName) (w₁ w₂ x₁ x₂ : Val) :
    isWeak γ w₁ x₁ ∗ isWeak γ w₂ x₂ ⊢@{IProp GF} ⌜w₁ = w₂ ∧ x₁ = x₂⌝ := by
  unfold isWeak
  iintro ⟨H1, H2⟩
  icases H1 with ⟨%_, %_, %_, Hmeta1, _⟩
  icases H2 with ⟨%_, %_, %_, Hmeta2, _⟩
  ihave Hagree := (arcMetaOwn_agree γ w₁ w₂ x₁ x₂) $$ [Hmeta1 Hmeta2]
  · isplitl [Hmeta1] <;> iassumption
  iexact Hagree

/-- Strong and weak handles for one identity share a control block and payload. -/
theorem isArc_isWeak_agree (γ : GName) (a w x₁ x₂ : Val) :
    isArc γ a x₁ ∗ isWeak γ w x₂ ⊢@{IProp GF} ⌜a = w ∧ x₁ = x₂⌝ := by
  unfold isArc isWeak
  iintro ⟨Harc, Hweak⟩
  icases Harc with ⟨%_, %_, %_, Hmeta1, _⟩
  icases Hweak with ⟨%_, %_, %_, Hmeta2, _⟩
  ihave Hagree := (arcMetaOwn_agree γ a w x₁ x₂) $$ [Hmeta1 Hmeta2]
  · isplitl [Hmeta1] <;> iassumption
  iexact Hagree

end Arc

namespace RwLock

private theorem writeAcquireSplit (γ : GName) :
    rwStateOwn γ .free ⊢@{IProp GF} rwStateOwn γ .write ∗ rwGuard γ .write := by
  unfold rwStateOwn rwGuard
  have hsplit : (● (0 : RwCredit) : Auth RwCredit) =
      (●{DFrac.own rwQ1_4} (0 : RwCredit)) •
        (●{DFrac.own rwQ3_4} (0 : RwCredit)) := by
    apply eq_of_eqv
    change (●{DFrac.own 1} (0 : RwCredit) : Auth RwCredit) ≡ _
    rw [← rwQsum]
    exact @Auth.auth_dfrac_op RwCredit _ (DFrac.own rwQ1_4) (DFrac.own rwQ3_4) 0
  rw [hsplit]
  exact iOwn_op.mp

private theorem writeReleaseCombine (γ : GName) :
    rwStateOwn γ .write ∗ rwGuard γ .write ⊢@{IProp GF} rwStateOwn γ .free := by
  unfold rwStateOwn rwGuard
  have hsplit : (● (0 : RwCredit) : Auth RwCredit) =
      (●{DFrac.own rwQ1_4} (0 : RwCredit)) •
        (●{DFrac.own rwQ3_4} (0 : RwCredit)) := by
    apply eq_of_eqv
    change (●{DFrac.own 1} (0 : RwCredit) : Auth RwCredit) ≡ _
    rw [← rwQsum]
    exact @Auth.auth_dfrac_op RwCredit _ (DFrac.own rwQ1_4) (DFrac.own rwQ3_4) 0
  rw [hsplit]
  exact iOwn_op.mpr

private theorem readAllocUpdate (n : RwCredit) :
    (● n : Auth RwCredit) ~~> (● (n + 1)) • ◯ (1 : RwCredit) := by
  exact Auth.auth_update_alloc (by
    have h := LocalUpdate.op_discrete n (CMRA.unit : RwCredit) (1 : RwCredit)
      (by intro _; trivial)
    have hu : (CMRA.unit : RwCredit) = 0 := rfl
    simpa [CommMonoidLike.op_eq, RwCredit.add_comm, hu] using h)

private theorem readAlloc (γ : GName) (n : RwCredit) :
    iOwn (F := RwLockF) γ (● n) ⊢@{IProp GF} |==>
      (iOwn (F := RwLockF) γ (● (n + 1)) ∗ rwGuard γ .read) := by
  unfold rwGuard
  exact (iOwn_update (F := RwLockF) (γ := γ) (readAllocUpdate n)).trans
    (bupd_mono ((iOwn_op (F := RwLockF) (γ := γ)
      (a1 := (● (n + 1) : Auth RwCredit))
      (a2 := (◯ (1 : RwCredit) : Auth RwCredit))).mp))

private theorem readAllocFree (γ : GName) :
    rwStateOwn γ .free ⊢@{IProp GF} |==>
      (rwStateOwn γ (.read 1) ∗ rwGuard γ .read) := by
  unfold rwStateOwn
  simpa using readAlloc (GF := GF) γ 0

private theorem readAllocRead (γ : GName) (n : Nat) :
    rwStateOwn γ (.read n) ⊢@{IProp GF} |==>
      (rwStateOwn γ (.read (n + 1)) ∗ rwGuard γ .read) := by
  unfold rwStateOwn
  simpa using readAlloc (GF := GF) γ (n : RwCredit)

private theorem readDeallocUpdate (n : RwCredit) :
    ((● (n + 1) : Auth RwCredit) • ◯ (1 : RwCredit)) ~~> ● n := by
  exact Auth.auth_update_dealloc (by
    have h := cancel_local_update_unit (1 : RwCredit) n
    have hu : (CMRA.unit : RwCredit) = 0 := rfl
    simpa [CommMonoidLike.op_eq, RwCredit.add_comm, hu] using h)

private theorem readDealloc (γ : GName) (n : RwCredit) :
    iOwn (F := RwLockF) γ (● (n + 1)) ∗ rwGuard γ .read ⊢@{IProp GF}
      |==> iOwn (F := RwLockF) γ (● n) := by
  unfold rwGuard
  exact (iOwn_op (F := RwLockF) (γ := γ)
    (a1 := (● (n + 1) : Auth RwCredit))
    (a2 := (◯ (1 : RwCredit) : Auth RwCredit))).mpr.trans
      (iOwn_update (F := RwLockF) (γ := γ) (readDeallocUpdate n))

private theorem readDeallocState (γ : GName) (n : Nat) :
    rwStateOwn γ (.read (n + 1)) ∗ rwGuard γ .read ⊢@{IProp GF}
      |==> iOwn (F := RwLockF) γ (● (n : RwCredit)) := by
  unfold rwStateOwn
  simpa using readDealloc (GF := GF) γ (n : RwCredit)

theorem isRwLock_copyRuntime (γ : GName) (l x : Val) (s : State) :
    isRwLock γ l s x ⊢@{IProp GF}
      (∃ p : Loc, ⌜l = hl_val((#p, &x))⌝) ∗ isRwLock γ l s x := by
  unfold isRwLock
  iintro H
  icases H with ⟨%p, %Hl, %Hvalid, Hp, Ha⟩
  isplitl []
  · iexists p
    ipureintro
    exact Hl
  · iexists p
    isplit; itrivial
    isplit
    · ipureintro
      exact Hvalid
    · iframe

theorem new_spec (x : Val) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&new &x)
    ⦃ l, RET l; ∃ γ, isRwLock γ l .free x ⦄ := by
  iintro %Φ - HΦ
  iapply wp_fupd
  unfold new
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %p Hp
  wp_pures
  imod (iOwn_alloc (F := RwLockF) (● (0 : RwCredit) : Auth RwCredit)
    (Auth.auth_valid.mpr (by trivial))) with ⟨%γ, Hγ⟩
  imodintro
  iapply HΦ
  iexists γ
  unfold isRwLock rwStateOwn State.counter
  iexists p
  iframe
  isplit
  · itrivial
  · ipureintro
    exact State.Valid.free

theorem ptr_drop_spec (γ : GName) (l : Val) (x : Loc) (v : Val) :
  ⊢@{IProp GF}
    ⦃ isRwLock γ l .free hl_val(#x) ∗ x ↦ v ⦄
      hl(&drop &l)
    ⦃ RET hl_val(#()); True ⦄ := by
  unfold isRwLock
  iintro %Φ ⟨Hlock, Hx⟩ HΦ
  icases Hlock with ⟨%p, %Hl, %Hvalid, Hp, Ha⟩
  subst l
  unfold drop
  wp_rec
  wp_pures
  wp_bind free(#p)
  iapply wp_wand $$ [Hp]
  · iapply wp_free $$ Hp
  iintro %r ⟨%Hr, Hp⟩
  rw [Hr]
  wp_pures
  iapply wp_wand $$ [Hx]
  · iapply wp_free $$ Hx
  iintro %r ⟨%Hr, Hx⟩
  rw [Hr]
  wp_pures
  iapply HΦ
  itrivial

theorem write_acquire_spec (γ : GName) (l x : Val) :
  ⊢@{IProp GF}
    ⟪ ∀ s, isRwLock γ l s x ⟫
      hl(&write_acquire &l) @ ∅
    ⟪ isRwLock γ l .write x ∗ rwGuard γ .write ∗ ⌜s = .free⌝ | RET x ⟫ := by
  iintro %Φ HAU
  iapply fupd_wp
  iauopen HAU with ⟨%s, Hs, Hclose⟩
  icases isRwLock_copyRuntime γ l x s $$ Hs with ⟨Hruntime, Hs⟩
  icases Hruntime with ⟨%p, %Hl⟩
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ Hs with HAU
  imodintro
  subst l
  iloeb as IH
  unfold write_acquire
  wp_rec
  wp_pures
  wp_bind cmpXchg(_,_,_)
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%s, Hs, Hclose⟩
  unfold isRwLock
  icases Hs with ⟨%p2, %Hl2, %Hvalid, Hp, Ha⟩
  have hp2 : p2 = p := (BaseLit.loc.inj (Val.lit.inj (Val.pair.inj Hl2).1)).symm
  subst p2
  imodintro
  cases Hvalid with
  | free =>
      iapply wp_wand $$ [Hp]
      · iapply wp_cmpXchg_true rfl rfl $$ Hp <;>
          simp [State.counter, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
      iintro %v ⟨%Hv, Hp⟩
      icases Hclose with ⟨-, Hcommit⟩
      icases writeAcquireSplit γ $$ Ha with ⟨Ha, Hg⟩
      imod Hcommit $$ [Hp Ha Hg] with Hcommit
      · unfold rwStateOwn State.counter
        isplitl [Hp Ha]
        · iexists p
          isplit; itrivial
          isplit
          · ipureintro
            exact State.Valid.write
          · iframe
        · isplitl [Hg]
          · iassumption
          · itrivial
      imodintro
      simp [State.counter] at Hv
      rw [Hv]
      wp_pures
      imodintro
      itrivial
  | read n =>
      iapply wp_wand $$ [Hp]
      · iapply wp_cmpXchg_fail rfl rfl $$ Hp <;>
          simp [State.counter, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed] <;>
          grind
      iintro %v ⟨%Hv, Hp⟩
      icases Hclose with ⟨Habort, -⟩
      imod Habort $$ [Hp Ha] with HAU
      · unfold rwStateOwn State.counter
        iexists p
        isplit; itrivial
        isplit
        · ipureintro
          exact State.Valid.read n
        · iframe
      imodintro
      simp [State.counter] at Hv
      rw [Hv]
      wp_pure
      wp_pure
      iapply IH $$ HAU
  | write =>
      iapply wp_wand $$ [Hp]
      · iapply wp_cmpXchg_fail rfl rfl $$ Hp <;>
          simp [State.counter, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
      iintro %v ⟨%Hv, Hp⟩
      icases Hclose with ⟨Habort, -⟩
      imod Habort $$ [Hp Ha] with HAU
      · unfold rwStateOwn State.counter
        iexists p
        isplit; itrivial
        isplit
        · ipureintro
          exact State.Valid.write
        · iframe
      imodintro
      simp [State.counter] at Hv
      rw [Hv]
      wp_pure
      wp_pure
      iapply IH $$ HAU

theorem write_release_spec (γ : GName) (l x : Val) :
  ⊢@{IProp GF}
    rwGuard γ .write -∗
    ⟪ isRwLock γ l .write x ⟫
      hl(&write_release &l) @ ∅
    ⟪ isRwLock γ l .free x | RET hl_val(#()) ⟫ := by
  iintro Hg %Φ HAU
  iapply fupd_wp
  iauopen HAU with ⟨Hs, Hclose⟩
  icases isRwLock_copyRuntime γ l x .write $$ Hs with ⟨Hruntime, Hs⟩
  icases Hruntime with ⟨%p, %Hl⟩
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ Hs with HAU
  imodintro
  subst l
  unfold write_release
  wp_rec
  wp_pures
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨Hs, Hclose⟩
  unfold isRwLock
  icases Hs with ⟨%p2, %Hl2, %Hvalid, Hp, Ha⟩
  have hp2 : p2 = p := (BaseLit.loc.inj (Val.lit.inj (Val.pair.inj Hl2).1)).symm
  subst p2
  imodintro
  iapply wp_store $$ Hp
  iintro !> Hp
  icases Hclose with ⟨-, Hcommit⟩
  ihave Ha0 := writeReleaseCombine γ $$ [Ha Hg]
  · isplitl [Ha] <;> iassumption
  imod Hcommit $$ [Hp Ha0] with Hcommit
  · unfold rwStateOwn State.counter
    iexists p
    isplit; itrivial
    isplit
    · ipureintro
      exact State.Valid.free
    · iframe
  imodintro
  itrivial

theorem read_acquire_spec (γ : GName) (l x : Val) :
  ⊢@{IProp GF}
    ⟪ ∀ s, isRwLock γ l s x ⟫
      hl(&read_acquire &l) @ ∅
    ⟪ rwGuard γ .read ∗
        ((isRwLock γ l (.read 1) x ∗ ⌜s = .free⌝) ∨
         (∃ n, isRwLock γ l (.read (n + 1)) x ∗ ⌜s = .read n⌝))
      | RET x ⟫ := by
  iintro %Φ HAU
  iapply fupd_wp
  iauopen HAU with ⟨%s, Hs, Hclose⟩
  icases isRwLock_copyRuntime γ l x s $$ Hs with ⟨Hruntime, Hs⟩
  icases Hruntime with ⟨%p, %Hl⟩
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ Hs with HAU
  imodintro
  subst l
  iloeb as IH
  unfold read_acquire
  wp_rec
  wp_pures
  wp_bind !#p
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%s, Hs, Hclose⟩
  unfold isRwLock
  icases Hs with ⟨%p2, %Hl2, %Hvalid, Hp, Ha⟩
  have hp2 : p2 = p := (BaseLit.loc.inj (Val.lit.inj (Val.pair.inj Hl2).1)).symm
  subst p2
  imodintro
  iapply wp_load $$ Hp
  iintro !> Hp
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ [Hp Ha] with HAU
  · iexists p
    isplit; itrivial
    isplit
    · ipureintro
      exact Hvalid
    · iframe
  imodintro
  cases Hvalid with
  | write =>
      simp only [State.counter]
      wp_pure
      wp_pure
      wp_pure
      have Hdec : decide ((-1 : Int) < 0) = true := by decide
      rw [Hdec]
      wp_pure
      iapply IH $$ HAU
  | free =>
      simp only [State.counter]
      wp_pure
      wp_pure
      wp_pure
      have Hdec : decide ((0 : Int) < 0) = false := by decide
      rw [Hdec]
      wp_pure
      wp_pures
      wp_bind cmpXchg(_,_,_)
      iapply wp_atomic (E2 := ∅)
      iauopen HAU with ⟨%s2, Hs2, Hclose2⟩
      icases Hs2 with ⟨%p2, %Hl2, %Hvalid2, Hp, Ha⟩
      have hp2 : p2 = p := (BaseLit.loc.inj (Val.lit.inj (Val.pair.inj Hl2).1)).symm
      subst p2
      imodintro
      by_cases Hcounter : State.counter s2 = 0
      · have Hs2eq : s2 = .free := State.counter_injective Hvalid2 State.Valid.free
          (by simpa [State.counter] using Hcounter)
        subst s2
        iapply wp_wand $$ [Hp]
        · iapply wp_cmpXchg_true rfl rfl $$ Hp <;>
            simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
        iintro %v ⟨%Hv, Hp⟩
        icases Hclose2 with ⟨-, Hcommit⟩
        imod readAllocFree γ $$ Ha with ⟨Ha, Hg⟩
        imod Hcommit $$ [Hp Ha Hg] with Hcommit
        · isplitl [Hg]
          · iassumption
          · ileft
            isplitl [Hp Ha]
            · iexists p
              isplit; itrivial
              isplit
              · ipureintro
                exact State.Valid.read 0
              · have Hval : (0 : Int) + 1 = (1 : Nat) := by rfl
                rw [← Hval]
                iframe
            · itrivial
        imodintro
        simp at Hv
        rw [Hv]
        wp_pures
        imodintro
        itrivial
      · iapply wp_wand $$ [Hp]
        · iapply wp_cmpXchg_fail rfl rfl $$ Hp
          · simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
          · simpa [State.counter] using Hcounter
        iintro %v ⟨%Hv, Hp⟩
        icases Hclose2 with ⟨Habort, -⟩
        imod Habort $$ [Hp Ha] with HAU
        · iexists p
          isplit; itrivial
          isplit
          · ipureintro
            exact Hvalid2
          · iframe
        imodintro
        rw [Hv]
        wp_pure
        wp_pure
        iapply IH $$ HAU
  | read n =>
      simp only [State.counter]
      wp_pure
      wp_pure
      wp_pure
      have Hdec : decide (((n + 1 : Nat) : Int) < 0) = false := by
        apply decide_eq_false_iff_not.mpr
        exact Int.not_lt.mpr (Int.natCast_nonneg (n + 1))
      rw [Hdec]
      wp_pure
      wp_pures
      wp_bind cmpXchg(_,_,_)
      iapply wp_atomic (E2 := ∅)
      iauopen HAU with ⟨%s2, Hs2, Hclose2⟩
      icases Hs2 with ⟨%p2, %Hl2, %Hvalid2, Hp, Ha⟩
      have hp2 : p2 = p := (BaseLit.loc.inj (Val.lit.inj (Val.pair.inj Hl2).1)).symm
      subst p2
      imodintro
      by_cases Hcounter : State.counter s2 = ((n + 1 : Nat) : Int)
      · have Hs2eq : s2 = .read (n + 1) :=
          State.counter_injective Hvalid2 (State.Valid.read n)
            (by simpa [State.counter] using Hcounter)
        subst s2
        iapply wp_wand $$ [Hp]
        · iapply wp_cmpXchg_true rfl rfl $$ Hp <;>
            simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
        iintro %v ⟨%Hv, Hp⟩
        icases Hclose2 with ⟨-, Hcommit⟩
        imod readAllocRead γ (n + 1) $$ Ha with ⟨Ha, Hg⟩
        imod Hcommit $$ [Hp Ha Hg] with Hcommit
        · isplitl [Hg]
          · iassumption
          · iright
            iexists n + 1
            isplitl [Hp Ha]
            · iexists p
              isplit; itrivial
              isplit
              · ipureintro
                exact State.Valid.read (n + 1)
              · have Hval :
                    (((n + 1 : Nat) : Int) + 1) = (((n + 1) + 1 : Nat) : Int) := by
                  omega
                rw [← Hval]
                iframe
            · itrivial
        imodintro
        simp at Hv
        rw [Hv]
        wp_pures
        imodintro
        itrivial
      · iapply wp_wand $$ [Hp]
        · iapply wp_cmpXchg_fail rfl rfl $$ Hp
          · simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
          · simpa [State.counter] using Hcounter
        iintro %v ⟨%Hv, Hp⟩
        icases Hclose2 with ⟨Habort, -⟩
        imod Habort $$ [Hp Ha] with HAU
        · iexists p
          isplit; itrivial
          isplit
          · ipureintro
            exact Hvalid2
          · iframe
        imodintro
        rw [Hv]
        wp_pure
        wp_pure
        iapply IH $$ HAU

theorem read_release_spec (γ : GName) (l x : Val) :
  ⊢@{IProp GF}
    rwGuard γ .read -∗
    ⟪ ∀ n, isRwLock γ l (.read (n + 1)) x ⟫
      hl(&read_release &l) @ ∅
    ⟪ (isRwLock γ l .free x ∗ ⌜n = 0⌝) ∨
        (isRwLock γ l (.read n) x ∗ ⌜n > 0⌝)
      | RET hl_val(#()) ⟫ := by
  iintro Hg %Φ HAU
  iapply fupd_wp
  iauopen HAU with ⟨%n, Hs, Hclose⟩
  icases isRwLock_copyRuntime γ l x (.read (n + 1)) $$ Hs with ⟨Hruntime, Hs⟩
  icases Hruntime with ⟨%p, %Hl⟩
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ Hs with HAU
  imodintro
  subst l
  unfold read_release
  wp_rec
  wp_pures
  wp_bind faa(_, _)
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%n, Hs, Hclose⟩
  unfold isRwLock
  icases Hs with ⟨%p2, %Hl2, %Hvalid, Hp, Ha⟩
  have hp2 : p2 = p := (BaseLit.loc.inj (Val.lit.inj (Val.pair.inj Hl2).1)).symm
  subst p2
  imodintro
  iapply wp_wand $$ [Hp]
  · iapply wp_faa $$ Hp
  iintro %v ⟨%Hv, Hp⟩
  icases Hclose with ⟨-, Hcommit⟩
  imod readDeallocState γ n $$ [Ha Hg] with Ha
  · isplitl [Ha] <;> iassumption
  cases n with
  | zero =>
      imod Hcommit $$ [Hp Ha] with Hcommit
      · ileft
        isplitl [Hp Ha]
        · iexists p
          isplit; itrivial
          isplit
          · ipureintro
            exact State.Valid.free
          · simp only [State.counter, rwStateOwn]
            have Hval : (((0 + 1 : Nat) : Int) + (-1)) = (0 : Int) := by omega
            rw [← Hval]
            iframe
        · itrivial
      imodintro
      rw [Hv]
      wp_pures
      imodintro
      itrivial
  | succ n =>
      imod Hcommit $$ [Hp Ha] with Hcommit
      · iright
        isplitl [Hp Ha]
        · iexists p
          isplit; itrivial
          isplit
          · ipureintro
            exact State.Valid.read n
          · simp only [State.counter, rwStateOwn]
            have Hval :
                ((((n + 1) + 1 : Nat) : Int) + (-1)) = ((n + 1 : Nat) : Int) := by
              omega
            rw [← Hval]
            iframe
        · ipureintro
          omega
      imodintro
      rw [Hv]
      wp_pures
      imodintro
      itrivial

end RwLock

namespace Arc

variable [ArcG GF]
omit [RwLockG GF]

private theorem strongAllocUpdate (a x : Val) (n m : Nat) :
    (● arcStateRes a x n m : Auth ArcRes) ~~>
      (● arcStateRes a x (n + 1) m) • ◯ arcStrongRes := by
  apply Auth.auth_update_alloc
  apply LocalUpdate.prod'
  · exact LocalUpdate.id _
  · apply LocalUpdate.prod'
    · exact CommMonoidLike.leftCancelAdd_local_update (by rfl)
    · exact LocalUpdate.id _

private theorem weakAllocUpdate (a x : Val) (n m : Nat) :
    (● arcStateRes a x n m : Auth ArcRes) ~~>
      (● arcStateRes a x n (m + 1)) • ◯ arcWeakRes := by
  apply Auth.auth_update_alloc
  apply LocalUpdate.prod'
  · exact LocalUpdate.id _
  · apply LocalUpdate.prod'
    · exact LocalUpdate.id _
    · exact CommMonoidLike.leftCancelAdd_local_update (by rfl)

private theorem strongDeallocUpdate (a x : Val) (n m : Nat) :
    ((● arcStateRes a x (n + 1) m : Auth ArcRes) • ◯ arcStrongRes) ~~>
      ● arcStateRes a x n m := by
  apply Auth.auth_update_dealloc
  apply LocalUpdate.prod'
  · exact LocalUpdate.id _
  · apply LocalUpdate.prod'
    · simpa [CommMonoidLike.op_eq, Nat.add_comm] using
        (cancel_local_update_unit (1 : Credit) n)
    · exact LocalUpdate.id _

private theorem weakDeallocUpdate (a x : Val) (n m : Nat) :
    ((● arcStateRes a x n (m + 1) : Auth ArcRes) • ◯ arcWeakRes) ~~>
      ● arcStateRes a x n m := by
  apply Auth.auth_update_dealloc
  apply LocalUpdate.prod'
  · exact LocalUpdate.id _
  · apply LocalUpdate.prod'
    · exact LocalUpdate.id _
    · simpa [CommMonoidLike.op_eq, Nat.add_comm] using
        (cancel_local_update_unit (1 : Credit) m)

private theorem strongAlloc (γ : GName) (a x : Val) (n m : Nat) :
    arcStateOwn γ a x n m ⊢@{IProp GF} |==>
      (arcStateOwn γ a x (n + 1) m ∗ arcStrongOwn γ) := by
  unfold arcStateOwn arcStrongOwn
  exact (iOwn_update (F := ArcF) (γ := γ) (strongAllocUpdate a x n m)).trans
    (bupd_mono ((iOwn_op (F := ArcF) (γ := γ)
      (a1 := (● arcStateRes a x (n + 1) m : Auth ArcRes))
      (a2 := (◯ arcStrongRes : Auth ArcRes))).mp))

private theorem weakAlloc (γ : GName) (a x : Val) (n m : Nat) :
    arcStateOwn γ a x n m ⊢@{IProp GF} |==>
      (arcStateOwn γ a x n (m + 1) ∗ arcWeakOwn γ) := by
  unfold arcStateOwn arcWeakOwn
  exact (iOwn_update (F := ArcF) (γ := γ) (weakAllocUpdate a x n m)).trans
    (bupd_mono ((iOwn_op (F := ArcF) (γ := γ)
      (a1 := (● arcStateRes a x n (m + 1) : Auth ArcRes))
      (a2 := (◯ arcWeakRes : Auth ArcRes))).mp))

private theorem strongDealloc (γ : GName) (a x : Val) (n m : Nat) :
    arcStateOwn γ a x (n + 1) m ∗ arcStrongOwn γ ⊢@{IProp GF}
      |==> arcStateOwn γ a x n m := by
  unfold arcStateOwn arcStrongOwn
  exact (iOwn_op (F := ArcF) (γ := γ)
    (a1 := (● arcStateRes a x (n + 1) m : Auth ArcRes))
    (a2 := (◯ arcStrongRes : Auth ArcRes))).mpr.trans
      (iOwn_update (F := ArcF) (γ := γ) (strongDeallocUpdate a x n m))

private theorem weakDealloc (γ : GName) (a x : Val) (n m : Nat) :
    arcStateOwn γ a x n (m + 1) ∗ arcWeakOwn γ ⊢@{IProp GF}
      |==> arcStateOwn γ a x n m := by
  unfold arcStateOwn arcWeakOwn
  exact (iOwn_op (F := ArcF) (γ := γ)
    (a1 := (● arcStateRes a x n (m + 1) : Auth ArcRes))
    (a2 := (◯ arcWeakRes : Auth ArcRes))).mpr.trans
      (iOwn_update (F := ArcF) (γ := γ) (weakDeallocUpdate a x n m))

theorem isArc_copyRuntime (γ : GName) (a x : Val) :
    isArc γ a x ⊢@{IProp GF}
      (∃ ps pw : Loc, ⌜a = hl_val(((#ps, #pw), &x))⌝) ∗ isArc γ a x := by
  unfold isArc
  iintro Harc
  icases Harc with ⟨%ps, %pw, %Ha, Hmeta, Hstrong⟩
  isplitl []
  · iexists ps, pw
    ipureintro
    exact Ha
  · iexists ps, pw
    isplit
    · ipureintro
      exact Ha
    · iframe

private theorem arcAuth_isArc_valid_l (γ : GName) (n m : Nat) (a x : Val) :
    arcAuth γ n m ∗ isArc γ a x ⊢@{IProp GF}
      ⌜n > 0⌝ ∗ (arcAuth γ n m ∗ isArc γ a x) :=
  BI.persistent_entails_right (arcAuth_isArc_valid γ n m a x)

private theorem arcStateOwn_meta_agree_l
    (γ : GName) (a₀ a x₀ x : Val) (n m : Nat) :
    arcStateOwn γ a₀ x₀ n m ∗ arcMetaOwn γ a x ⊢@{IProp GF}
      ⌜a₀ = a ∧ x₀ = x⌝ ∗
        (arcStateOwn γ a₀ x₀ n m ∗ arcMetaOwn γ a x) :=
  BI.persistent_entails_right (arcStateOwn_meta_agree γ a₀ a x₀ x n m)

private theorem arcMetaOwn_dup (γ : GName) (a x : Val) :
    arcMetaOwn γ a x ⊢@{IProp GF} arcMetaOwn γ a x ∗ arcMetaOwn γ a x :=
  BI.persistent_entails_right (.rfl)

private theorem arcControl_injective
    {ps₁ pw₁ ps₂ pw₂ : Loc} {x₁ x₂ : Val}
    (h : hl_val(((#ps₁, #pw₁), &x₁)) = hl_val(((#ps₂, #pw₂), &x₂))) :
    ps₁ = ps₂ ∧ pw₁ = pw₂ := by
  have hpairs := Val.pair.inj (Val.pair.inj h).1
  exact ⟨BaseLit.loc.inj (Val.lit.inj hpairs.1),
    BaseLit.loc.inj (Val.lit.inj hpairs.2)⟩

omit [ArcG GF] in
private theorem arcPhysical_positive (ps pw : Loc) (n m : Nat) :
    arcPhysical ps pw (n + 1) m ⊣⊢@{IProp GF}
      ps ↦ hl_val(#((n + 1 : Nat) : Int)) ∗
        pw ↦ hl_val(#((m + 1 : Nat) : Int)) := by
  unfold arcPhysical
  exact .rfl

omit [ArcG GF] in
private theorem arcPhysical_zero_weak (ps pw : Loc) (m : Nat) :
    arcPhysical ps pw 0 (m + 1) ⊣⊢@{IProp GF}
      ps ↦ hl_val(#(0 : Int)) ∗ pw ↦ hl_val(#((m + 1 : Nat) : Int)) := by
  unfold arcPhysical
  exact .rfl

theorem new_spec (x : Val) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&new &x)
    ⦃ a, RET a; ∃ γ, arcAuth γ 1 0 ∗ isArc γ a x ⦄ := by
  iintro %Φ - HΦ
  iapply wp_fupd
  unfold new
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %ps Hps
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %pw Hpw
  wp_pures
  let a : Val := hl_val(((#ps, #pw), &x))
  have Hvalid :
      ✓ ((● arcStateRes a x 1 0 : Auth ArcRes) • ◯ arcStateRes a x 1 0) :=
    Auth.auth_both_valid_2 (by
      unfold arcStateRes arcMeta
      exact ⟨Agree.toAgree_valid, ⟨trivial, trivial⟩⟩) (CMRA.inc_refl _)
  imod (iOwn_alloc (F := ArcF)
    ((● arcStateRes a x 1 0 : Auth ArcRes) • ◯ arcStateRes a x 1 0)
    Hvalid) with ⟨%γ, Hghost⟩
  ihave Hsplit := (iOwn_op (F := ArcF) (γ := γ)
    (a1 := (● arcStateRes a x 1 0 : Auth ArcRes))
    (a2 := (◯ arcStateRes a x 1 0 : Auth ArcRes))).mp $$ Hghost
  icases Hsplit with ⟨Hauth, Hhandle⟩
  have Hstate : arcStateRes a x 1 0 = arcMetaRes a x • arcStrongRes := by
    rfl
  have Hfrag :
      (◯ arcStateRes a x 1 0 : Auth ArcRes) =
        (◯ arcMetaRes a x : Auth ArcRes) • ◯ arcStrongRes := by
    rw [Hstate, Auth.frag_op]
  have HhandleSplit :
      iOwn (F := ArcF) γ (◯ arcStateRes a x 1 0) ⊢@{IProp GF}
        iOwn (F := ArcF) γ (◯ arcMetaRes a x) ∗
          iOwn (F := ArcF) γ (◯ arcStrongRes) := by
    rw [Hfrag]
    exact (iOwn_op (F := ArcF) (γ := γ)
      (a1 := (◯ arcMetaRes a x : Auth ArcRes))
      (a2 := (◯ arcStrongRes : Auth ArcRes))).mp
  ihave Hsplit := HhandleSplit $$ Hhandle
  icases Hsplit with ⟨Hmeta, Hstrong⟩
  imodintro
  iapply HΦ
  iexists γ
  isplitl [Hps Hpw Hauth]
  · unfold arcAuth arcStateOwn arcPhysical
    iexists ps, pw, a, x
    isplit
    · ipureintro
      rfl
    · simp only
      iframe
  · unfold isArc arcMetaOwn arcStrongOwn
    iexists ps, pw
    isplit
    · ipureintro
      rfl
    · iframe

theorem clone_spec (a x : Val) :
  ⊢@{IProp GF}
    isArc γ a x -∗
    ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
      hl(&clone &a) @ ∅
    ⟪ arcAuth γ (n + 1) m ∗ isArc γ a x ∗ isArc γ a x
      | RET a ⟫ := by
  iintro Harc %Φ HAU
  icases isArc_copyRuntime γ a x $$ Harc with ⟨Hruntime, Harc⟩
  icases Hruntime with ⟨%ps, %pw, %Ha⟩
  subst a
  unfold clone strongPtr
  wp_rec
  wp_pures
  wp_bind faa(_, _)
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%n, %m, Hauth, Hclose⟩
  ihave Hvalid := (arcAuth_isArc_valid_l γ n m
    hl_val(((#ps, #pw), &x)) x) $$ [Hauth Harc]
  · isplitl [Hauth] <;> iassumption
  icases Hvalid with ⟨%Hn, Hresources⟩
  icases Hresources with ⟨Hauth, Harc⟩
  cases n with
  | zero => omega
  | succ n =>
      unfold arcAuth isArc
      icases Hauth with ⟨%ps₀, %pw₀, %a₀, %x₀, %Ha₀, Hphysical, Hown⟩
      icases Harc with ⟨%ps₁, %pw₁, %Ha₁, Hmeta, Hold⟩
      ihave Hagree := (arcStateOwn_meta_agree_l γ a₀
        hl_val(((#ps, #pw), &x)) x₀ x (n + 1) m) $$ [Hown Hmeta]
      · isplitl [Hown] <;> iassumption
      icases Hagree with ⟨%Hagree, Hresources⟩
      icases Hresources with ⟨Hown, Hmeta⟩
      icases arcMetaOwn_dup γ hl_val(((#ps, #pw), &x)) x $$ Hmeta with
        ⟨Hmeta1, Hmeta2⟩
      rcases Hagree with ⟨Ha₀eq, Hx₀eq⟩
      have Hruntime₀ :
          hl_val(((#ps, #pw), &x)) = hl_val(((#ps₀, #pw₀), &x)) := by
        calc
          _ = a₀ := Ha₀eq.symm
          _ = hl_val(((#ps₀, #pw₀), &x₀)) := Ha₀
          _ = _ := by rw [Hx₀eq]
      have ⟨Hps₀, Hpw₀⟩ := arcControl_injective Hruntime₀
      subst ps₀
      subst pw₀
      icases (arcPhysical_positive ps pw n m).mp $$ Hphysical with ⟨Hps, Hpw⟩
      imodintro
      iapply wp_wand $$ [Hps]
      · iapply wp_faa $$ Hps
      iintro %v ⟨%Hv, Hps⟩
      icases Hclose with ⟨-, Hcommit⟩
      imod strongAlloc γ a₀ x₀ (n + 1) m $$ Hown with
        ⟨Hown, Hnew⟩
      imod Hcommit $$ [Hps Hpw Hown Hmeta1 Hmeta2 Hold Hnew] with Hcommit
      · isplitl [Hps Hpw Hown]
        · iexists ps, pw, a₀, x₀
          isplit
          · ipureintro
            exact Ha₀
          · simp only [arcPhysical]
            have Hcounter :
                (((n + 1 : Nat) : Int) + 1) = (((n + 1) + 1 : Nat) : Int) := by
              omega
            rw [← Hcounter]
            iframe
        · isplitl [Hold Hmeta1]
          · iexists ps₁, pw₁
            isplit
            · ipureintro
              exact Ha₁
            · iframe
          · iexists ps₁, pw₁
            isplit
            · ipureintro
              exact Ha₁
            · iframe
      imodintro
      rw [Hv]
      wp_pures
      imodintro
      itrivial

theorem get_spec (a x : Val) :
  ⊢@{IProp GF}
    ⦃ isArc γ a x ⦄
      hl(&get &a)
    ⦃ RET x; isArc γ a x ⦄ := by
  unfold isArc
  iintro %Φ Harc HΦ
  icases Harc with ⟨%ps, %pw, %Ha, Hmeta, Hstrong⟩
  subst a
  unfold get
  wp_pures
  imodintro
  iapply HΦ
  iexists ps, pw
  isplit
  · itrivial
  · iframe

theorem downgrade_spec (a x : Val) :
  ⊢@{IProp GF}
    isArc γ a x -∗
    ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
      hl(&downgrade &a) @ ∅
    ⟪ arcAuth γ n (m + 1) ∗ isArc γ a x ∗ isWeak γ a x
      | RET a ⟫ := by
  iintro Harc %Φ HAU
  icases isArc_copyRuntime γ a x $$ Harc with ⟨Hruntime, Harc⟩
  icases Hruntime with ⟨%ps, %pw, %Ha⟩
  subst a
  unfold downgrade weakPtr
  wp_rec
  wp_pures
  wp_bind faa(_, _)
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%n, %m, Hauth, Hclose⟩
  ihave Hvalid := (arcAuth_isArc_valid_l γ n m
    hl_val(((#ps, #pw), &x)) x) $$ [Hauth Harc]
  · isplitl [Hauth] <;> iassumption
  icases Hvalid with ⟨%Hn, Hresources⟩
  icases Hresources with ⟨Hauth, Harc⟩
  cases n with
  | zero => omega
  | succ n =>
      unfold arcAuth isArc isWeak
      icases Hauth with ⟨%ps₀, %pw₀, %a₀, %x₀, %Ha₀, Hphysical, Hown⟩
      icases Harc with ⟨%ps₁, %pw₁, %Ha₁, Hmeta, Hstrong⟩
      ihave Hagree := (arcStateOwn_meta_agree_l γ a₀
        hl_val(((#ps, #pw), &x)) x₀ x (n + 1) m) $$ [Hown Hmeta]
      · isplitl [Hown] <;> iassumption
      icases Hagree with ⟨%Hagree, Hresources⟩
      icases Hresources with ⟨Hown, Hmeta⟩
      icases arcMetaOwn_dup γ hl_val(((#ps, #pw), &x)) x $$ Hmeta with
        ⟨Hmeta1, Hmeta2⟩
      rcases Hagree with ⟨Ha₀eq, Hx₀eq⟩
      have Hruntime₀ :
          hl_val(((#ps, #pw), &x)) = hl_val(((#ps₀, #pw₀), &x)) := by
        calc
          _ = a₀ := Ha₀eq.symm
          _ = hl_val(((#ps₀, #pw₀), &x₀)) := Ha₀
          _ = _ := by rw [Hx₀eq]
      have ⟨Hps₀, Hpw₀⟩ := arcControl_injective Hruntime₀
      subst ps₀
      subst pw₀
      icases (arcPhysical_positive ps pw n m).mp $$ Hphysical with ⟨Hps, Hpw⟩
      imodintro
      iapply wp_wand $$ [Hpw]
      · iapply wp_faa $$ Hpw
      iintro %v ⟨%Hv, Hpw⟩
      icases Hclose with ⟨-, Hcommit⟩
      imod weakAlloc γ a₀ x₀ (n + 1) m $$ Hown with ⟨Hown, Hweak⟩
      imod Hcommit $$ [Hps Hpw Hown Hmeta1 Hmeta2 Hstrong Hweak] with Hcommit
      · isplitl [Hps Hpw Hown]
        · iexists ps, pw, a₀, x₀
          isplit
          · ipureintro
            exact Ha₀
          · simp only [arcPhysical]
            have Hcounter :
                (((m + 1 : Nat) : Int) + 1) = (((m + 1) + 1 : Nat) : Int) := by
              omega
            rw [← Hcounter]
            iframe
        · isplitl [Hstrong Hmeta1]
          · iexists ps₁, pw₁
            isplit
            · ipureintro
              exact Ha₁
            · iframe
          · iexists ps₁, pw₁
            isplit
            · ipureintro
              exact Ha₁
            · iframe
      imodintro
      rw [Hv]
      wp_pures
      imodintro
      itrivial

/-- Atomic strong-count decrement; the single `faa` is the linearization point.

When this handle is the last strong reference the caller receives the control
block's *implicit* weak reference as an explicit `isWeak` handle. This mirrors
`drop(Weak { ptr: self.ptr })` at the end of Rust's `Arc::drop`: the physical
weak counter is untouched, only its accounting moves from implicit to explicit,
which is exactly why `arcPhysical ps pw 1 m` and `arcPhysical ps pw 0 (m + 1)`
describe the same two cells. -/
theorem dropStrong_spec (a x : Val) :
  ⊢@{IProp GF}
    isArc γ a x -∗
    ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
      hl(&dropStrong &a) @ ∅
    ⟪ (⌜n = 1⌝ ∗ arcAuth γ 0 (m + 1) ∗ isWeak γ a x) ∨
        (⌜n > 1⌝ ∗ arcAuth γ (n - 1) m)
      | RET hl_val(#(decide (n = 1))) ⟫ := by
  iintro Harc %Φ HAU
  icases isArc_copyRuntime γ a x $$ Harc with ⟨Hruntime, Harc⟩
  icases Hruntime with ⟨%ps, %pw, %Ha⟩
  subst a
  unfold dropStrong strongPtr
  wp_rec
  wp_pures
  wp_bind faa(_, _)
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%n, %m, Hauth, Hclose⟩
  ihave Hvalid := (arcAuth_isArc_valid_l γ n m
    hl_val(((#ps, #pw), &x)) x) $$ [Hauth Harc]
  · isplitl [Hauth] <;> iassumption
  icases Hvalid with ⟨%Hn, Hresources⟩
  icases Hresources with ⟨Hauth, Harc⟩
  unfold arcAuth isArc isWeak
  icases Hauth with ⟨%ps₀, %pw₀, %a₀, %x₀, %Ha₀, Hphysical, Hown⟩
  icases Harc with ⟨%ps₁, %pw₁, %Ha₁, Hmeta, Hstrong⟩
  ihave Hagree := (arcStateOwn_meta_agree_l γ a₀
    hl_val(((#ps, #pw), &x)) x₀ x n m) $$ [Hown Hmeta]
  · isplitl [Hown] <;> iassumption
  icases Hagree with ⟨%Hagree, Hresources⟩
  icases Hresources with ⟨Hown, Hmeta⟩
  rcases Hagree with ⟨Ha₀eq, Hx₀eq⟩
  have Hruntime₀ :
      hl_val(((#ps, #pw), &x)) = hl_val(((#ps₀, #pw₀), &x)) := by
    calc
      _ = a₀ := Ha₀eq.symm
      _ = hl_val(((#ps₀, #pw₀), &x₀)) := Ha₀
      _ = _ := by rw [Hx₀eq]
  have ⟨Hps₀, Hpw₀⟩ := arcControl_injective Hruntime₀
  subst ps₀
  subst pw₀
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          icases (arcPhysical_positive ps pw 0 m).mp $$ Hphysical with
            ⟨Hps, Hpw⟩
          imodintro
          iapply wp_wand $$ [Hps]
          · iapply wp_faa $$ Hps
          iintro %old ⟨%Hold, Hps⟩
          icases Hclose with ⟨-, Hcommit⟩
          imod strongDealloc γ a₀ x₀ 0 m $$ [Hown Hstrong] with Hown
          · isplitl [Hown] <;> iassumption
          imod weakAlloc γ a₀ x₀ 0 m $$ Hown with ⟨Hown, Hweak⟩
          imod Hcommit $$ [Hps Hpw Hown Hmeta Hweak] with Hcommit
          · ileft
            isplit
            · ipureintro
              rfl
            · isplitl [Hps Hpw Hown]
              · iexists ps, pw, a₀, x₀
                isplit
                · ipureintro
                  exact Ha₀
                · simp only [arcPhysical]
                  let before : Int := ((0 + 1 : Nat) : Int) + (-1)
                  have Hcounter : before = (0 : Int) := by
                    dsimp [before]
                  have HpsNormalize :
                      ps ↦ hl_val(#before) ⊢@{IProp GF}
                        ps ↦ hl_val(#(0 : Int)) := by
                    rw [Hcounter]
                    exact .rfl
                  ihave Hps := HpsNormalize $$ Hps
                  iframe
              · iexists ps₁, pw₁
                isplit
                · ipureintro
                  exact Ha₁
                · iframe
          imodintro
          rw [Hold]
          wp_pures
          imodintro
          have Hbranch :
              (hl_val(#((0 + 1 : Nat) : Int)) == hl_val(#(1 : Int))) = true := by
            simp
          simp only [Hbranch, decide_true]
          itrivial
      | succ n =>
          icases (arcPhysical_positive ps pw (n + 1) m).mp $$ Hphysical with
            ⟨Hps, Hpw⟩
          imodintro
          iapply wp_wand $$ [Hps]
          · iapply wp_faa $$ Hps
          iintro %old ⟨%Hold, Hps⟩
          icases Hclose with ⟨-, Hcommit⟩
          imod strongDealloc γ a₀ x₀ (n + 1) m $$ [Hown Hstrong] with Hown
          · isplitl [Hown] <;> iassumption
          imod Hcommit $$ [Hps Hpw Hown] with Hcommit
          · iright
            isplit
            · ipureintro
              omega
            · iexists ps, pw, a₀, x₀
              isplit
              · ipureintro
                exact Ha₀
              · simp only [Nat.add_sub_cancel, arcPhysical]
                let before : Int := ((n + 1 + 1 : Nat) : Int) + (-1)
                have Hcounter : before = ((n + 1 : Nat) : Int) := by
                  dsimp [before]
                  omega
                have HpsNormalize :
                    ps ↦ hl_val(#before) ⊢@{IProp GF}
                      ps ↦ hl_val(#((n + 1 : Nat) : Int)) := by
                  rw [Hcounter]
                  exact .rfl
                ihave Hps := HpsNormalize $$ Hps
                iframe
          imodintro
          rw [Hold]
          wp_pures
          imodintro
          have Hbranch :
              (hl_val(#((n + 1 + 1 : Nat) : Int)) == hl_val(#(1 : Int)))
                = false := by
            simp
            omega
          have Hdecide : decide (n + 1 + 1 = 1) = false := rfl
          simp only [Hbranch, Hdecide]
          itrivial

end Arc

namespace Weak

variable [ArcG GF]
omit [RwLockG GF]

private theorem isWeak_copyRuntime (γ : GName) (w x : Val) :
    isWeak γ w x ⊢@{IProp GF}
      (∃ ps pw : Loc, ⌜w = hl_val(((#ps, #pw), &x))⌝) ∗ isWeak γ w x := by
  unfold isWeak
  iintro Hweak
  icases Hweak with ⟨%ps, %pw, %Hw, Hmeta, Htoken⟩
  isplitl []
  · iexists ps, pw
    ipureintro
    exact Hw
  · iexists ps, pw
    isplit
    · ipureintro
      exact Hw
    · iframe

private theorem arcAuth_isWeak_valid_l (γ : GName) (n m : Nat) (w x : Val) :
    arcAuth γ n m ∗ isWeak γ w x ⊢@{IProp GF}
      ⌜m > 0⌝ ∗ (arcAuth γ n m ∗ isWeak γ w x) :=
  BI.persistent_entails_right (Arc.arcAuth_isWeak_valid γ n m w x)

theorem clone_spec (w x : Val) :
  ⊢@{IProp GF}
    isWeak γ w x -∗
    ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
      hl(&clone &w) @ ∅
    ⟪ arcAuth γ n (m + 1) ∗ isWeak γ w x ∗ isWeak γ w x
      | RET w ⟫ := by
  iintro Hweak %Φ HAU
  icases isWeak_copyRuntime γ w x $$ Hweak with ⟨Hruntime, Hweak⟩
  icases Hruntime with ⟨%ps, %pw, %Hw⟩
  subst w
  unfold clone Arc.weakPtr
  wp_rec
  wp_pures
  wp_bind faa(_, _)
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%n, %m, Hauth, Hclose⟩
  ihave Hvalid := (arcAuth_isWeak_valid_l γ n m
    hl_val(((#ps, #pw), &x)) x) $$ [Hauth Hweak]
  · isplitl [Hauth] <;> iassumption
  icases Hvalid with ⟨%Hm, Hresources⟩
  icases Hresources with ⟨Hauth, Hweak⟩
  unfold arcAuth isWeak
  icases Hauth with ⟨%ps₀, %pw₀, %a₀, %x₀, %Ha₀, Hphysical, Hown⟩
  icases Hweak with ⟨%ps₁, %pw₁, %Hw₁, Hmeta, Hold⟩
  ihave Hagree := (Arc.arcStateOwn_meta_agree_l γ a₀
    hl_val(((#ps, #pw), &x)) x₀ x n m) $$ [Hown Hmeta]
  · isplitl [Hown] <;> iassumption
  icases Hagree with ⟨%Hagree, Hresources⟩
  icases Hresources with ⟨Hown, Hmeta⟩
  icases Arc.arcMetaOwn_dup γ hl_val(((#ps, #pw), &x)) x $$ Hmeta with
    ⟨Hmeta1, Hmeta2⟩
  rcases Hagree with ⟨Ha₀eq, Hx₀eq⟩
  have Hruntime₀ :
      hl_val(((#ps, #pw), &x)) = hl_val(((#ps₀, #pw₀), &x)) := by
    calc
      _ = a₀ := Ha₀eq.symm
      _ = hl_val(((#ps₀, #pw₀), &x₀)) := Ha₀
      _ = _ := by rw [Hx₀eq]
  have ⟨Hps₀, Hpw₀⟩ := Arc.arcControl_injective Hruntime₀
  subst ps₀
  subst pw₀
  cases n with
  | zero =>
      cases m with
      | zero => omega
      | succ m =>
          icases (Arc.arcPhysical_zero_weak ps pw m).mp $$ Hphysical with ⟨Hps, Hpw⟩
          imodintro
          iapply wp_wand $$ [Hpw]
          · iapply wp_faa $$ Hpw
          iintro %v ⟨%Hv, Hpw⟩
          icases Hclose with ⟨-, Hcommit⟩
          imod Arc.weakAlloc γ a₀ x₀ 0 (m + 1) $$ Hown with ⟨Hown, Hnew⟩
          imod Hcommit $$ [Hps Hpw Hown Hmeta1 Hmeta2 Hold Hnew] with Hcommit
          · isplitl [Hps Hpw Hown]
            · iexists ps, pw, a₀, x₀
              isplit
              · ipureintro
                exact Ha₀
              · simp only [arcPhysical]
                have Hcounter :
                    (((m + 1 : Nat) : Int) + 1) =
                      (((m + 1) + 1 : Nat) : Int) := by
                  omega
                rw [← Hcounter]
                iframe
            · isplitl [Hold Hmeta1]
              · iexists ps₁, pw₁
                isplit
                · ipureintro
                  exact Hw₁
                · iframe
              · iexists ps₁, pw₁
                isplit
                · ipureintro
                  exact Hw₁
                · iframe
          imodintro
          rw [Hv]
          wp_pures
          imodintro
          itrivial
  | succ n =>
      icases (Arc.arcPhysical_positive ps pw n m).mp $$ Hphysical with ⟨Hps, Hpw⟩
      imodintro
      iapply wp_wand $$ [Hpw]
      · iapply wp_faa $$ Hpw
      iintro %v ⟨%Hv, Hpw⟩
      icases Hclose with ⟨-, Hcommit⟩
      imod Arc.weakAlloc γ a₀ x₀ (n + 1) m $$ Hown with ⟨Hown, Hnew⟩
      imod Hcommit $$ [Hps Hpw Hown Hmeta1 Hmeta2 Hold Hnew] with Hcommit
      · isplitl [Hps Hpw Hown]
        · iexists ps, pw, a₀, x₀
          isplit
          · ipureintro
            exact Ha₀
          · simp only [arcPhysical]
            have Hcounter :
                (((m + 1 : Nat) : Int) + 1) = (((m + 1) + 1 : Nat) : Int) := by
              omega
            rw [← Hcounter]
            iframe
        · isplitl [Hold Hmeta1]
          · iexists ps₁, pw₁
            isplit
            · ipureintro
              exact Hw₁
            · iframe
          · iexists ps₁, pw₁
            isplit
            · ipureintro
              exact Hw₁
            · iframe
      imodintro
      rw [Hv]
      wp_pures
      imodintro
      itrivial

/-- **Atomic weak-count decrement.** The single `faa` is the linearization
point. The counter deallocation that follows on the last weak reference happens
*after* the commit, using the two points-to assertions this thread keeps
locally. That is sound precisely because `arcPhysical ps pw 0 0` is `True`: the
abstract state `(0, 0)` records that the control block has already been handed
over to the thread that is tearing it down. -/
theorem drop_spec (w x : Val) :
  ⊢@{IProp GF}
    isWeak γ w x -∗
    ⟪ ∀ n, ∀ m, arcAuth γ n m ⟫
      hl(&drop &w) @ ∅
    ⟪ arcAuth γ n (m - 1) | RET hl_val(#()) ⟫ := by
  iintro Hweak %Φ HAU
  icases isWeak_copyRuntime γ w x $$ Hweak with ⟨Hruntime, Hweak⟩
  icases Hruntime with ⟨%ps, %pw, %Hw⟩
  subst w
  unfold drop Arc.dropWeak Arc.weakPtr Arc.strongPtr
  wp_rec
  wp_pures
  wp_bind faa(_, _)
  iapply wp_atomic (E2 := ∅)
  iauopen HAU with ⟨%n, %m, Hauth, Hclose⟩
  ihave Hvalid := (arcAuth_isWeak_valid_l γ n m
    hl_val(((#ps, #pw), &x)) x) $$ [Hauth Hweak]
  · isplitl [Hauth] <;> iassumption
  icases Hvalid with ⟨%Hm, Hresources⟩
  icases Hresources with ⟨Hauth, Hweak⟩
  unfold arcAuth isWeak
  icases Hauth with ⟨%ps₀, %pw₀, %a₀, %x₀, %Ha₀, Hphysical, Hown⟩
  icases Hweak with ⟨%ps₁, %pw₁, %Hw₁, Hmeta, Htoken⟩
  ihave Hagree := (Arc.arcStateOwn_meta_agree_l γ a₀
    hl_val(((#ps, #pw), &x)) x₀ x n m) $$ [Hown Hmeta]
  · isplitl [Hown] <;> iassumption
  icases Hagree with ⟨%Hagree, Hresources⟩
  icases Hresources with ⟨Hown, Hmeta⟩
  rcases Hagree with ⟨Ha₀eq, Hx₀eq⟩
  have Hruntime₀ :
      hl_val(((#ps, #pw), &x)) = hl_val(((#ps₀, #pw₀), &x)) := by
    calc
      _ = a₀ := Ha₀eq.symm
      _ = hl_val(((#ps₀, #pw₀), &x₀)) := Ha₀
      _ = _ := by rw [Hx₀eq]
  have ⟨Hps₀, Hpw₀⟩ := Arc.arcControl_injective Hruntime₀
  subst ps₀
  subst pw₀
  cases m with
  | zero => omega
  | succ m =>
      cases n with
      | zero =>
          cases m with
          | zero =>
              icases (Arc.arcPhysical_zero_weak ps pw 0).mp $$ Hphysical with
                ⟨Hps, Hpw⟩
              imodintro
              iapply wp_wand $$ [Hpw]
              · iapply wp_faa $$ Hpw
              iintro %old ⟨%Hold, Hpw⟩
              icases Hclose with ⟨-, Hcommit⟩
              imod Arc.weakDealloc γ a₀ x₀ 0 0 $$ [Hown Htoken] with Hown
              · isplitl [Hown] <;> iassumption
              imod Hcommit $$ [Hown] with Hcommit
              · iexists ps, pw, a₀, x₀
                isplit
                · ipureintro
                  exact Ha₀
                · simp only [Nat.add_sub_cancel, arcPhysical]
                  iframe
              imodintro
              rw [Hold]
              wp_pure
              wp_pure
              wp_pure
              simp
              wp_pures
              wp_bind free(#ps)
              iapply wp_wand $$ [Hps]
              · iapply wp_free $$ Hps
              iintro %r ⟨%Hr, Hps⟩
              rw [Hr]
              wp_pures
              iapply wp_wand $$ [Hpw]
              · iapply wp_free $$ Hpw
              iintro %r ⟨%Hr, Hpw⟩
              rw [Hr]
              wp_pures
              itrivial
          | succ m =>
              icases (Arc.arcPhysical_zero_weak ps pw (m + 1)).mp $$ Hphysical with
                ⟨Hps, Hpw⟩
              imodintro
              iapply wp_wand $$ [Hpw]
              · iapply wp_faa $$ Hpw
              iintro %old ⟨%Hold, Hpw⟩
              icases Hclose with ⟨-, Hcommit⟩
              imod Arc.weakDealloc γ a₀ x₀ 0 (m + 1) $$ [Hown Htoken] with Hown
              · isplitl [Hown] <;> iassumption
              imod Hcommit $$ [Hps Hpw Hown] with Hcommit
              · iexists ps, pw, a₀, x₀
                isplit
                · ipureintro
                  exact Ha₀
                · simp only [Nat.add_sub_cancel, arcPhysical]
                  let before : Int := ((m + 1 + 1 : Nat) : Int) + (-1)
                  let after : Int := ((m + 1 : Nat) : Int)
                  have Hcounter : before = after := by
                    dsimp only [before, after]
                    omega
                  have HpwNormalize :
                      pw ↦ hl_val(#before) ⊢@{IProp GF} pw ↦ hl_val(#after) := by
                    rw [Hcounter]
                    exact .rfl
                  ihave Hpw := HpwNormalize $$ Hpw
                  iframe
              imodintro
              rw [Hold]
              wp_pure
              wp_pure
              wp_pure
              simp
              have Hbranch :
                  (hl_val(#((m : Int) + (1 : Int) + (1 : Int))) ==
                    hl_val(#(1 : Int))) = false := by
                simp
                omega
              simp only [Hbranch]
              wp_pures
              itrivial
      | succ n =>
          icases (Arc.arcPhysical_positive ps pw n (m + 1)).mp $$ Hphysical with
            ⟨Hps, Hpw⟩
          imodintro
          iapply wp_wand $$ [Hpw]
          · iapply wp_faa $$ Hpw
          iintro %old ⟨%Hold, Hpw⟩
          icases Hclose with ⟨-, Hcommit⟩
          imod Arc.weakDealloc γ a₀ x₀ (n + 1) m $$ [Hown Htoken] with Hown
          · isplitl [Hown] <;> iassumption
          imod Hcommit $$ [Hps Hpw Hown] with Hcommit
          · iexists ps, pw, a₀, x₀
            isplit
            · ipureintro
              exact Ha₀
            · simp only [Nat.add_sub_cancel, arcPhysical]
              let before : Int := ((m + 1 + 1 : Nat) : Int) + (-1)
              let after : Int := ((m + 1 : Nat) : Int)
              have Hcounter : before = after := by
                dsimp only [before, after]
                omega
              have HpwNormalize :
                  pw ↦ hl_val(#before) ⊢@{IProp GF} pw ↦ hl_val(#after) := by
                rw [Hcounter]
                exact .rfl
              ihave Hpw := HpwNormalize $$ Hpw
              iframe
          imodintro
          rw [Hold]
          wp_pure
          wp_pure
          wp_pure
          simp
          have Hbranch :
              (hl_val(#((m : Int) + (1 : Int) + (1 : Int))) ==
                hl_val(#(1 : Int))) = false := by
            simp
            omega
          simp only [Hbranch]
          wp_pures
          itrivial

/-- Sequential view of `drop_spec`, obtained by `atomicWP_seq`: a client that
privately owns `arcAuth` does not need the atomic interface. -/
private theorem dropWeak_spec (w x : Val) (n m : Nat) :
    ⊢@{IProp GF}
      ⦃ isWeak γ w x ∗ arcAuth γ n m ⦄
        hl(&Arc.dropWeak &w)
      ⦃ RET hl_val(#()); arcAuth γ n (m - 1) ⦄ := by
  rw [show (Arc.dropWeak : Val) = drop from rfl]
  iintro %Φ ⟨Hweak, Hauth⟩ HΦ
  ihave Hspec := (drop_spec (γ := γ) w x) $$ Hweak
  iapply atomicWP_seq_step _ _ _ _ _ _ (by rfl) $$ Hspec %Φ %(⟨n, m, ⟨⟩⟩)
    [Hauth] [HΦ]
  · itele_reduce
    iframe Hauth
  · inext
    itele_reduce
    iintro Hβ
    iapply HΦ $$ Hβ

private theorem tryUpgrade_spec (w x : Val) (n m : Nat) :
    ⊢@{IProp GF}
      ⦃ isWeak γ w x ∗ arcAuth γ n m ⦄
        hl(&tryUpgrade &w)
      ⦃ r, RET r;
          (⌜n = 0⌝ ∗ ⌜r = hl_val(none())⌝ ∗ isWeak γ w x ∗ arcAuth γ n m) ∨
          (⌜n > 0⌝ ∗ ⌜r = hl_val(some(&w))⌝ ∗
            isWeak γ w x ∗ arcAuth γ (n + 1) m ∗ isArc γ w x) ⦄ := by
  iintro %Φ ⟨Hweak, Hauth⟩ HΦ
  icases isWeak_copyRuntime γ w x $$ Hweak with ⟨Hruntime, Hweak⟩
  icases Hruntime with ⟨%ps, %pw, %Hw⟩
  subst w
  ihave Hvalid := (arcAuth_isWeak_valid_l γ n m
    hl_val(((#ps, #pw), &x)) x) $$ [Hauth Hweak]
  · isplitl [Hauth] <;> iassumption
  icases Hvalid with ⟨%Hm, Hresources⟩
  icases Hresources with ⟨Hauth, Hweak⟩
  unfold arcAuth isWeak isArc
  icases Hauth with ⟨%ps₀, %pw₀, %a₀, %x₀, %Ha₀, Hphysical, Hown⟩
  icases Hweak with ⟨%ps₁, %pw₁, %Hw₁, Hmeta, Htoken⟩
  ihave Hagree := (Arc.arcStateOwn_meta_agree_l γ a₀
    hl_val(((#ps, #pw), &x)) x₀ x n m) $$ [Hown Hmeta]
  · isplitl [Hown] <;> iassumption
  icases Hagree with ⟨%Hagree, Hresources⟩
  icases Hresources with ⟨Hown, Hmeta⟩
  rcases Hagree with ⟨Ha₀eq, Hx₀eq⟩
  have Hruntime₀ :
      hl_val(((#ps, #pw), &x)) = hl_val(((#ps₀, #pw₀), &x)) := by
    calc
      _ = a₀ := Ha₀eq.symm
      _ = hl_val(((#ps₀, #pw₀), &x₀)) := Ha₀
      _ = _ := by rw [Hx₀eq]
  have ⟨Hps₀, Hpw₀⟩ := Arc.arcControl_injective Hruntime₀
  subst ps₀
  subst pw₀
  cases n with
  | zero =>
      cases m with
      | zero => omega
      | succ m =>
          icases (Arc.arcPhysical_zero_weak ps pw m).mp $$ Hphysical with ⟨Hps, Hpw⟩
          unfold tryUpgrade Arc.strongPtr
          wp_rec
          wp_pures
          wp_bind !#ps
          iapply wp_load $$ Hps
          iintro !> Hps
          wp_pures
          simp
          wp_pures
          imodintro
          iapply HΦ
          ileft
          isplit
          · itrivial
          · isplit
            · itrivial
            · isplitl [Hmeta Htoken]
              · iexists ps₁, pw₁
                isplit
                · ipureintro
                  exact Arc.arcControl_injective Hw₁
                · iframe
              · iexists ps, pw, a₀, x₀
                isplit
                · ipureintro
                  exact Ha₀
                · simp [arcPhysical]
                  iframe
  | succ n =>
      icases (Arc.arcPhysical_positive ps pw n m).mp $$ Hphysical with ⟨Hps, Hpw⟩
      unfold tryUpgrade Arc.strongPtr
      wp_rec
      wp_pures
      wp_bind !#ps
      iapply wp_load $$ Hps
      iintro !> Hps
      wp_pures
      simp
      have Hzero :
          (hl_val(#((n : Int) + (1 : Int))) == hl_val(#(0 : Int))) = false := by
        simp
        omega
      simp only [Hzero]
      wp_pures
      wp_bind cmpXchg(_,_,_)
      iapply wp_wand $$ [Hps]
      · iapply wp_cmpXchg_true rfl rfl $$ Hps <;>
          simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
      iintro %cas ⟨%Hcas, Hps⟩
      imod Arc.strongAlloc γ a₀ x₀ (n + 1) m $$ Hown with ⟨Hown, Hstrong⟩
      icases Arc.arcMetaOwn_dup γ hl_val(((#ps, #pw), &x)) x $$ Hmeta with
        ⟨Hmeta1, Hmeta2⟩
      rw [Hcas]
      wp_pures
      imodintro
      iapply HΦ
      iright
      isplit
      · itrivial
      · isplit
        · itrivial
        · isplitl [Hmeta1 Htoken]
          · iexists ps₁, pw₁
            isplit
            · ipureintro
              exact Arc.arcControl_injective Hw₁
            · iframe
          · isplitl [Hps Hpw Hown]
            · iexists ps, pw, a₀, x₀
              isplit
              · ipureintro
                exact Ha₀
              · simp [arcPhysical]
                iframe
            · iexists ps₁, pw₁
              isplit
              · ipureintro
                exact Arc.arcControl_injective Hw₁
              · iframe

/-- Consuming upgrade. The proof retains exclusive `arcAuth` across the
strong-count CAS and the input Weak decrement. -/
theorem upgrade_spec (w x : Val) (n m : Nat) :
  ⊢@{IProp GF}
    ⦃ isWeak γ w x ∗ arcAuth γ n m ⦄
      hl(&upgrade &w)
    ⦃ r, RET r;
        (⌜n = 0⌝ ∗ ⌜r = hl_val(none())⌝ ∗ arcAuth γ 0 (m - 1)) ∨
        (⌜n > 0⌝ ∗ ⌜r = hl_val(some(&w))⌝ ∗
          arcAuth γ (n + 1) (m - 1) ∗ isArc γ w x) ⦄ := by
  iintro %Φ Hpre HΦ
  unfold upgrade
  wp_rec
  wp_pures
  wp_bind &tryUpgrade _
  ihave Hup :
      (WP hl(&tryUpgrade &w) {{ r,
        (⌜n = 0⌝ ∗ ⌜r = hl_val(none())⌝ ∗
          isWeak γ w x ∗ arcAuth γ n m) ∨
        (⌜n > 0⌝ ∗ ⌜r = hl_val(some(&w))⌝ ∗
          isWeak γ w x ∗ arcAuth γ (n + 1) m ∗ isArc γ w x) }}) $$ [Hpre]
  · iapply tryUpgrade_spec w x n m $$ Hpre
    inext
    iintro %r Hstage
    iexact Hstage
  iapply wp_wand $$ Hup
  iintro %r Hstage
  wp_pures
  icases Hstage with (Hnone | Hsome)
  · icases Hnone with ⟨%Hn, %Hr, Hweak, Hauth⟩
    subst n
    wp_bind &Arc.dropWeak _
    ihave Hdrop :
        (WP hl(&Arc.dropWeak &w) {{ _v, arcAuth γ 0 (m - 1) }}) $$
          [Hweak Hauth]
    · iapply dropWeak_spec w x 0 m $$ [Hweak Hauth]
      · isplitl [Hweak] <;> iassumption
      iintro !> Hauth
      iexact Hauth
    iapply wp_wand $$ Hdrop
    iintro %_ Hauth
    wp_pures
    imodintro
    iapply HΦ
    ileft
    isplit
    · itrivial
    · isplit
      · ipureintro
        exact Hr
      · iassumption
  · icases Hsome with ⟨%Hn, %Hr, Hweak, Hauth, Harc⟩
    wp_bind &Arc.dropWeak _
    ihave Hdrop :
        (WP hl(&Arc.dropWeak &w) {{ _v, arcAuth γ (n + 1) (m - 1) }}) $$
          [Hweak Hauth]
    · iapply dropWeak_spec w x (n + 1) m $$ [Hweak Hauth]
      · isplitl [Hweak] <;> iassumption
      iintro !> Hauth
      iexact Hauth
    iapply wp_wand $$ Hdrop
    iintro %_ Hauth
    wp_pures
    imodintro
    iapply HΦ
    iright
    isplit
    · ipureintro
      exact Hn
    · isplit
      · ipureintro
        exact Hr
      · iframe

end Weak

namespace Arc

variable [ArcG GF]
omit [RwLockG GF]

/-- Sequential view of `dropStrong_spec`, obtained by `atomicWP_seq_step`. -/
private theorem dropStrong_seq_spec (a x : Val) (n m : Nat) :
    ⊢@{IProp GF}
      ⦃ isArc γ a x ∗ arcAuth γ n m ⦄
        hl(&dropStrong &a)
      ⦃ RET hl_val(#(decide (n = 1)));
          (⌜n = 1⌝ ∗ arcAuth γ 0 (m + 1) ∗ isWeak γ a x) ∨
          (⌜n > 1⌝ ∗ arcAuth γ (n - 1) m) ⦄ := by
  iintro %Φ ⟨Harc, Hauth⟩ HΦ
  ihave Hspec := (dropStrong_spec (γ := γ) a x) $$ Harc
  iapply atomicWP_seq_step _ _ _ _ _ _ (by rfl) $$ Hspec %Φ %(⟨n, m, ⟨⟩⟩)
    [Hauth] [HΦ]
  · itele_reduce
    iframe Hauth
  · inext
    itele_reduce
    iintro Hβ
    iapply HΦ $$ Hβ

/-- **Derived composite `drop`.** `dropStrong` and `dropWeak` each carry their
own linearization point, so the composition only admits an ordinary Hoare
triple, against a privately owned `arcAuth`.

The payload destructor `dropT` and its precondition `Q` are parameters: this is
what replaces the former hard-wired `lastStrongResource`, so `Arc` no longer
mentions `RwLock`. The client only has to supply `Q` when the handle really is
the last strong reference, which is exactly `if n = 1 then Q else True`. -/
theorem drop_spec (dropT a x : Val) (n m : Nat) (Q : IProp GF) :
  ⊢@{IProp GF}
    (⦃ Q ⦄ hl(&dropT &x) ⦃ RET hl_val(#()); True ⦄) -∗
    ⦃ isArc γ a x ∗ arcAuth γ n m ∗ (if n = 1 then Q else True) ⦄
      hl(&drop &dropT &a)
    ⦃ RET hl_val(#()); arcAuth γ (n - 1) m ⦄ := by
  iintro HdropT %Φ ⟨Harc, Hauth, HQ⟩ HΦ
  icases isArc_copyRuntime γ a x $$ Harc with ⟨Hruntime, Harc⟩
  icases Hruntime with ⟨%ps, %pw, %Ha⟩
  subst a
  unfold drop
  wp_rec
  wp_pures
  wp_bind &dropStrong _
  ihave Hstage :
      (WP hl(&dropStrong &(hl_val(((#ps, #pw), &x)))) {{ r,
        ⌜r = hl_val(#(decide (n = 1)))⌝ ∗
        ((⌜n = 1⌝ ∗ arcAuth γ 0 (m + 1) ∗
            isWeak γ hl_val(((#ps, #pw), &x)) x) ∨
          (⌜n > 1⌝ ∗ arcAuth γ (n - 1) m)) }}) $$ [Harc Hauth]
  · iapply dropStrong_seq_spec _ x n m $$ [Harc Hauth]
    · isplitl [Harc] <;> iassumption
    iintro !> Hstage
    isplit
    · ipureintro
      rfl
    · iexact Hstage
  iapply wp_wand $$ Hstage
  iintro %r ⟨%Hr, Hstage⟩
  subst r
  icases Hstage with (Hlast | Hother)
  · icases Hlast with ⟨%Hn, Hauth, Hweak⟩
    subst n
    simp only [decide_true, if_true]
    wp_pures
    unfold closeLastStrong
    wp_rec
    wp_pures
    wp_bind (_ _)
    ihave Hpayload :
        (WP hl(&dropT &x) {{ _v, True }}) $$ [HdropT HQ]
    · iapply HdropT $$ HQ
      iintro !> -
      itrivial
    iapply wp_wand $$ Hpayload
    iintro %_ -
    wp_pures
    ihave Hdrop :
        (WP hl(&dropWeak &(hl_val(((#ps, #pw), &x)))) {{ v, Φ v }}) $$
          [Hweak Hauth HΦ]
    · iapply Weak.dropWeak_spec _ x 0 (m + 1) $$ [Hweak Hauth]
      · isplitl [Hweak] <;> iassumption
      simp only [Nat.add_sub_cancel]
      iexact HΦ
    iexact Hdrop
  · icases Hother with ⟨%Hn, Hauth⟩
    have Hdec : decide (n = 1) = false := by
      simp
      omega
    simp only [Hdec]
    wp_pures
    imodintro
    iapply HΦ
    iexact Hauth

end Arc

namespace RwLock

/-- The concrete coarse-grained RwLock implementation of `RwLock.API`. -/
@[implicit_reducible]
noncomputable def instAPI [HeapLangGS hlc GF] : API GF where
  new := new
  read_acquire := read_acquire
  write_acquire := write_acquire
  read_release := read_release
  write_release := write_release
  drop := drop
  name := GName
  isRwLock := Iris.Examples.HeapLang.isRwLock
  rwGuard := Iris.Examples.HeapLang.rwGuard
  rwGuardFrac := Iris.Examples.HeapLang.rwGuardFrac
  isRwLock_timeless γ l s x :=
    Iris.Examples.HeapLang.instIsRwLockTimeless γ l s x
  rwGuard_timeless γ mode :=
    Iris.Examples.HeapLang.instRwGuardTimeless γ mode
  rwGuardFrac_timeless γ mode q :=
    Iris.Examples.HeapLang.instRwGuardFracTimeless γ mode q
  rwGuard_eq _ _ := .rfl
  rwGuardFrac_split γ mode q₁ q₂ := rwGuardFrac_split γ mode q₁ q₂
  rwGuardFrac_valid γ l s x mode q := rwGuardFrac_valid γ l s x mode q
  isRwLock_valid γ l s x := isRwLock_valid γ l s x
  isRwLock_exclusive γ l s₁ s₂ x₁ x₂ :=
    isRwLock_exclusive γ l s₁ s₂ x₁ x₂
  rwGuard_valid γ l s x mode := rwGuard_valid γ l s x mode
  rwGuard_write_exclusive γ := rwGuard_write_exclusive γ
  rwGuard_write_read_exclusive γ := rwGuard_write_read_exclusive γ
  new_spec x := new_spec x
  ptr_drop_spec γ l x v := ptr_drop_spec γ l x v
  write_acquire_spec γ l x := write_acquire_spec γ l x
  write_release_spec γ l x := write_release_spec γ l x
  read_acquire_spec γ l x := read_acquire_spec γ l x
  read_release_spec γ l x := read_release_spec γ l x

end RwLock

namespace Arc

/-- The concrete exact-count Arc/Weak implementation of `Arc.API`. -/
@[implicit_reducible]
noncomputable def instAPI [HeapLangGS hlc GF] [ArcG GF] : API GF where
  new := new
  clone := clone
  get := get
  downgrade := downgrade
  drop_strong := dropStrong
  drop := drop
  weak_clone := Weak.clone
  weak_drop := Weak.drop
  weak_upgrade := Weak.upgrade
  name := GName
  arcAuth := Iris.Examples.HeapLang.arcAuth
  isArc := Iris.Examples.HeapLang.isArc
  isWeak := Iris.Examples.HeapLang.isWeak
  arcAuth_timeless γ n m :=
    Iris.Examples.HeapLang.instArcAuthTimeless γ n m
  isArc_timeless γ a x :=
    Iris.Examples.HeapLang.instIsArcTimeless γ a x
  isWeak_timeless γ w x :=
    Iris.Examples.HeapLang.instIsWeakTimeless γ w x
  arcAuth_exclusive γ n₁ m₁ n₂ m₂ :=
    arcAuth_exclusive γ n₁ m₁ n₂ m₂
  arcAuth_isArc_valid γ n m a x :=
    arcAuth_isArc_valid γ n m a x
  arcAuth_isWeak_valid γ n m w x :=
    arcAuth_isWeak_valid γ n m w x
  isArc_agree γ a₁ a₂ x₁ x₂ :=
    isArc_agree γ a₁ a₂ x₁ x₂
  isWeak_agree γ w₁ w₂ x₁ x₂ :=
    isWeak_agree γ w₁ w₂ x₁ x₂
  isArc_isWeak_agree γ a w x₁ x₂ :=
    isArc_isWeak_agree γ a w x₁ x₂
  new_spec x := new_spec x
  clone_spec γ a x := clone_spec (γ := γ) a x
  get_spec γ a x := get_spec (γ := γ) a x
  downgrade_spec γ a x := downgrade_spec (γ := γ) a x
  drop_strong_spec γ a x := dropStrong_spec (γ := γ) a x
  drop_spec γ dropT a x n m Q := drop_spec (γ := γ) dropT a x n m Q
  weak_clone_spec γ w x := Weak.clone_spec (γ := γ) w x
  weak_drop_spec γ w x := Weak.drop_spec (γ := γ) w x
  weak_upgrade_spec γ w x n m := Weak.upgrade_spec (γ := γ) w x n m

end Arc

end Iris.Examples.HeapLang
