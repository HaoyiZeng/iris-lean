module

public import Iris.Examples.Array

/-! # Weak-handle concurrent list

A variant of `Iris.Examples.Array` in which a client's handle on a cell is *weak*.
The sole strong reference to a cell is its predecessor's link, so revocation is the
last drop and reclaims memory whatever the client does with its handles.

Three things follow, and they are the point of the exercise.

* There is no revocation flag.  In `Array` a cell has to record that it has left
  the list, because a client holding a stale *strong* handle would otherwise find a
  perfectly good cell.  Here that client's upgrade simply fails.
* There is no "revoked but still alive" state, so no `retiredNodes`, no
  `retiredSlot`, and none of the machinery that goes with them.
* Every entry point takes a weak handle and upgrades it *inside* the platform lock,
  so a strong reference is either a link in the list or a temporary that cannot
  outlive one critical section.  Since revocation takes the platform lock
  exclusively, no strong reference is alive anywhere else while it runs — which is
  what makes the first two points true.

The root is still owned by a strong reference handed to the caller of `init`;
nothing inside the list owns it, so dropping it frees the whole list.

The abstract model (`Arr`, `Arr.insert`, `Arr.revoke`) is shared with `Array`
unchanged: `Arr.insert` already returns `none` exactly when the identifier is not
in the list, and "the upgrade failed" is precisely that case. -/

@[expose] public section
namespace Iris.Examples.HeapLang.WeakList

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Std PartialMap FracAgree
open CMRA OFE Auth Algebra

/-! ## Programs -/

def platformNew : Val := hl_val%
  λ _,
    let cell := ref(#());
    let lock := &RwLock.new cell;
    &Arc.new lock

def execute : Val := hl_val%
  λ platform exclusive f,
    let gate := &Arc.get(platform);
    if exclusive then
      let _ := &RwLock.write_acquire(gate);
      let result := f #();
      &RwLock.write_release(gate);
      result
    else
      let _ := &RwLock.read_acquire(gate);
      let result := f #();
      &RwLock.read_release(gate);
      result

/-- Allocate a cell.  Ownership of the successor link is *moved in*; the caller is
    left holding the only strong reference to the new cell. -/
def new : Val := hl_val%
  λ value next,
    let contents := ref((value, next));
    let lock := &RwLock.new contents;
    &Arc.new lock

def init : Val := hl_val%
  λ value, &new value (none())

/-- A weak handle on a cell the caller already owns. -/
def handle : Val := hl_val%
  λ node, &Arc.downgrade(node)

/-- Duplicate a handle.  `Weak::clone`, and like it needs no lock. -/
def cloneHandle : Val := hl_val%
  λ node, &Weak.clone(node)

/-- Splice a fresh cell in directly after `node`.

    The new cell is *not* cloned: its single strong reference becomes the link, and
    what the caller gets back is a weak handle. -/
def insert : Val := hl_val%
  λ platform node value,
    &execute platform #false (λ _,
      match &Weak.tryUpgrade(node) with
      | none() => none()
      | some(strong) =>
        let lock := &Arc.get(strong);
        let ptr := &RwLock.write_acquire(lock);
        let contents := !ptr;
        let oldValue := fst(contents);
        let oldNext := snd(contents);
        let newNode := &new value oldNext;
        let w := &Arc.downgrade(newNode);
        ptr ← (oldValue, some(newNode));
        &RwLock.write_release(lock);
        &Arc.drop &RwLock.drop strong;
        some(w))

/-- Free a detached chain.  Each cell's link is taken out before the cell is
    dropped, so the drop is always the last reference and the cell really is
    reclaimed. -/
def revokeSuffix : Val := hl_val%
  rec go current :=
    match current with
    | none() => #()
    | some(node) =>
      let lock := &Arc.get(node);
      let ptr := &RwLock.write_acquire(lock);
      let contents := !ptr;
      let value := fst(contents);
      let next := snd(contents);
      ptr ← (value, none());
      &RwLock.write_release(lock);
      &Arc.drop &RwLock.drop node;
      go next

def revoke : Val := hl_val%
  λ platform node,
    &execute platform #true (λ _,
      match &Weak.tryUpgrade(node) with
      | none() => none()
      | some(strong) =>
        let lock := &Arc.get(strong);
        let ptr := &RwLock.write_acquire(lock);
        let contents := !ptr;
        let value := fst(contents);
        let next := snd(contents);
        ptr ← (value, none());
        &RwLock.write_release(lock);
        &revokeSuffix next;
        &Arc.drop &RwLock.drop strong;
        some(#()))

/-- A weak handle on the successor, if there is one. -/
def getChild : Val := hl_val%
  λ platform node,
    &execute platform #false (λ _,
      match &Weak.tryUpgrade(node) with
      | none() => none()
      | some(strong) =>
        let lock := &Arc.get(strong);
        let ptr := &RwLock.write_acquire(lock);
        let contents := !ptr;
        let next := snd(contents);
        let result :=
          (match next with
           | none() => none()
           | some(child) => some(&Arc.downgrade(child)));
        &RwLock.write_release(lock);
        &Arc.drop &RwLock.drop strong;
        some(result))



/-! ## Ghost state

`Data` records the ghost names of one cell.  This file needs one more than
`Array` does — a shadow of the strong reference count — so it carries its own
metadata type, and with it its own metadata map and synchronisation variable.
Everything that is keyed by a bare ghost name (`cellAlive`, `cellDead`,
`arcHasStrong`, the fractions) is shared with `Array` unchanged. -/

section RA

variable {H : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H Nat]

/-- Shadow counter for a cell's strong references. -/
abbrev CntRF : COFE.OFunctorPre := AuthURF (constOF Credit)

/-- One cell's ghost names.  `cnt` is the shadow counter; the rest is `Data`. -/
structure WData extends Data where
  /-- Authority for the shadow reference count. -/
  cnt : GName
deriving DecidableEq, Repr

structure WState (H : Type → Type) where
  arr : Arr
  mmap : H WData

instance : OFE (WState H) := OFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete (WState H) := ⟨fun h => h⟩
instance : OFE.Leibniz (WState H) := ⟨fun h => h⟩

abbrev WStateRF (H : Type → Type) : COFE.OFunctorPre :=
  constOF (DFracAgreeR (WState H))

class WArrG (GF : BundledGFunctors) (H : outParam <| Type → Type)
    [LawfulFiniteMap H Nat] where
  [wMetaMapG : GhostMapG GF Nat WData H]
  [wStateG : ElemG GF (WStateRF H)]
  [cellG : ElemG GF CellRF]
  [cntG : ElemG GF CntRF]

attribute [reducible, instance] WArrG.wMetaMapG WArrG.wStateG WArrG.cellG WArrG.cntG

/-- The ghost names owned by the list itself. -/
structure WArrγ where
  /-- Metadata map: `id ↦ WData`. -/
  l : GName
  /-- Synchronisation variable pinning `(σ, M)` under one fraction. -/
  s : GName

section Defs
variable [WArrG GF H]

/-- The metadata map, held at a fraction.  Half stays pinned in the invariant at all
    times, the other half travels with the list content — so a thread holding the
    platform exclusively cannot register a cell behind the reference counters' back,
    and the counters always describe the map the list is actually using. -/
def wMetaMap (γ : GName) (q : Qp) (M : H WData) : IProp GF :=
  γ ↪●MAP{DFrac.own q} M
def wMetaAt (γ : GName) (id : Nat) (d : WData) : IProp GF :=
  γ ↪◯MAP[id]{.discard} d

def wStateVar (γ : GName) (q : Qp) (σ : Arr) (M : H WData) : IProp GF :=
  iOwn γ (F := WStateRF H) (FracAgree.Frac.mk q ⟨σ, M⟩)

/-- One unit of a cell's shadow count, owned by every holder of a strong reference.

    The point is *reachability*.  The strong reference belonging to the list itself
    sits in the predecessor's payload, which a thread holding the predecessor's
    write lock has taken away — so `arcAuth _ n _ ∗ isArc` is not a fact one can
    generally get at.  A `refTok` parked next to the chain entry, outside the lock,
    is. -/
def refTok (d : WData) : IProp GF := iOwn (F := CntRF) d.cnt (◯ (1 : Credit))

def refAuth (d : WData) (n : Nat) : IProp GF :=
  iOwn (F := CntRF) d.cnt (● ((n : Nat) : Credit))

instance instWMetaMapTimeless (γ : GName) (q : Qp) (M : H WData) :
    Timeless (wMetaMap (GF := GF) γ q M) := by unfold wMetaMap; infer_instance
instance instWMetaAtTimeless (γ : GName) (id : Nat) (d : WData) :
    Timeless (wMetaAt (GF := GF) γ id d) := by unfold wMetaAt; infer_instance
instance instWStateVarTimeless (γ : GName) (q : Qp) (σ : Arr) (M : H WData) :
    Timeless (wStateVar (GF := GF) γ q σ M) := by unfold wStateVar; infer_instance
instance instRefTokTimeless (d : WData) :
    Timeless (refTok (GF := GF) d) := by unfold refTok; infer_instance
instance instRefAuthTimeless (d : WData) (n : Nat) :
    Timeless (refAuth (GF := GF) d n) := by unfold refAuth; infer_instance

theorem wMetaMap_alloc : ⊢@{IProp GF} |==> ∃ γ, wMetaMap γ 1 (∅ : H WData) := by
  unfold wMetaMap
  iapply ghost_map_alloc_empty

theorem wMetaMap_split (γ : GName) (M : H WData) :
    wMetaMap (GF := GF) γ 1 M ⊣⊢ wMetaMap γ q1_2 M ∗ wMetaMap γ q1_2 M := by
  unfold wMetaMap ghost_map_auth
  have hq : DFrac.own (1 : Qp) = DFrac.own q1_2 • DFrac.own q1_2 := by
    show _ = DFrac.own (q1_2 + q1_2)
    rw [q1_2_add_q1_2]
  rw [hq]
  refine .trans (BI.equiv_iff.mp ?_) (iOwn_op (γ := γ))
  exact iOwn_ne.eqv HeapView.auth_dfrac_op_eqv

theorem wMetaMap_agree (γ : GName) (q₁ q₂ : Qp) (M₁ M₂ : H WData) :
    ⊢@{IProp GF} wMetaMap γ q₁ M₁ -∗ wMetaMap γ q₂ M₂ -∗ ⌜M₁ = M₂⌝ := by
  unfold wMetaMap
  iapply ghost_map_auth_agree

theorem wMetaMap_lookup (γ : GName) (q : Qp) (M : H WData) (id : Nat) (d : WData) :
    ⊢@{IProp GF} wMetaMap γ q M -∗ wMetaAt γ id d -∗
      ⌜get? M id = some d⌝ := by
  unfold wMetaMap wMetaAt
  iapply ghost_map_lookup

/-- `wMetaAt` uses the `.discard` fraction, so it is persistent — but `wMetaAt` is a
    `def`, which instance resolution cannot see through, so the instance has to be
    restated here (same situation as `cellDead_persistent`). -/
instance wMetaAt_persistent (γ : GName) (id : Nat) (d : WData) :
    Persistent (wMetaAt (GF := GF) (H := H) γ id d) := by
  unfold wMetaAt; infer_instance

theorem wMetaAt_agree (γ : GName) (id : Nat) (d₁ d₂ : WData) :
    ⊢@{IProp GF} wMetaAt γ id d₁ -∗ wMetaAt γ id d₂ -∗ ⌜d₁ = d₂⌝ := by
  unfold wMetaAt
  iintro H₁ H₂
  iapply ghost_map_elem_agree
  iframe

theorem wMetaMap_insert (γ : GName) (M : H WData) (id : Nat) (d : WData)
    (fresh : get? M id = none) :
    ⊢@{IProp GF} wMetaMap γ 1 M ==∗
      wMetaMap γ 1 (Std.insert M id d) ∗ wMetaAt γ id d := by
  unfold wMetaMap wMetaAt
  iapply ghost_map_insert_persist id d fresh

theorem wMetaMap_counter_fresh (M : H WData) (counter : Nat)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    get? M counter = none := by
  apply Option.not_isSome_iff_eq_none.mp
  intro hmem
  exact (Nat.lt_irrefl counter) ((hdom counter).mp hmem)

theorem wMetaMap_insert_counter_dom (M : H WData) (counter : Nat) (d : WData)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    ∀ id, dom (Std.insert M counter d) id ↔ id < counter + 1 := by
  intro id
  unfold dom
  by_cases h : counter = id
  · subst id
    simp [get?_insert_eq rfl]
  · rw [get?_insert_ne h]
    change dom M id ↔ _
    rw [hdom]
    omega

theorem wMetaMap_insert_counter (γ : GName) (M : H WData) (counter : Nat) (d : WData)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    ⊢@{IProp GF} wMetaMap γ 1 M ==∗
      wMetaMap γ 1 (Std.insert M counter d) ∗ wMetaAt γ counter d := by
  iapply wMetaMap_insert γ M counter d (wMetaMap_counter_fresh M counter hdom)

theorem wMetaMap_lookup_lt (γ : GName) (q : Qp) (M : H WData) (counter id : Nat) (d : WData)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    ⊢@{IProp GF} wMetaMap γ q M -∗ wMetaAt γ id d -∗ ⌜id < counter⌝ := by
  iintro HM Hid
  ihave %hlookup := wMetaMap_lookup γ q M id d $$ HM Hid
  ipureintro
  exact (hdom id).mp (by simp [dom, hlookup])

theorem wStateVar_agree (γ : GName) (q₁ q₂ : Qp) (σ₁ σ₂ : Arr) (M₁ M₂ : H WData) :
    wStateVar (GF := GF) γ q₁ σ₁ M₁ ∗ wStateVar γ q₂ σ₂ M₂ ⊢ ⌜σ₁ = σ₂ ∧ M₁ = M₂⌝ := by
  unfold wStateVar
  iintro ⟨H₁, H₂⟩
  ihave H := iOwn_cmraValid_op $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete $$ H with %Hvalid
  ipureintro
  have H := (FracAgree.Frac.op_valid_L.mp Hvalid).2
  exact ⟨congrArg WState.arr H, congrArg WState.mmap H⟩


/-- Two shares can only coexist if they fit inside one whole.  This is what makes
    the writer's `3/4` receipt incompatible with the `3/4` the invariant keeps while
    the platform lock is *not* write-held. -/
theorem wStateVar_frac_valid (γ : GName) (q₁ q₂ : Qp) (σ₁ σ₂ : Arr) (M₁ M₂ : H WData) :
    wStateVar (GF := GF) γ q₁ σ₁ M₁ ∗ wStateVar γ q₂ σ₂ M₂ ⊢ ⌜(q₁ + q₂).val ≤ 1⌝ := by
  unfold wStateVar
  iintro ⟨H₁, H₂⟩
  ihave H := iOwn_cmraValid_op $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete $$ H with %Hvalid
  ipureintro
  exact (FracAgree.Frac.op_valid_L.mp Hvalid).1

/-- The `1/4` (invariant side) / `3/4` (writer side) split, mirroring `cellAlive`. -/
theorem wStateVar_split (γ : GName) (σ : Arr) (M : H WData) :
    wStateVar (GF := GF) γ 1 σ M ⊣⊢ wStateVar γ q1_4 σ M ∗ wStateVar γ q3_4 σ M := by
  unfold wStateVar
  have h : (FracAgree.Frac.mk (1 : Qp) (⟨σ, M⟩ : WState H) : DFracAgreeR (WState H))
      = FracAgree.Frac.mk q1_4 (⟨σ, M⟩ : WState H)
        • FracAgree.Frac.mk q3_4 (⟨σ, M⟩ : WState H) := by
    rw [← q1_4_add_q3_4]; exact FracAgree.Frac.mk_op.to_eq
  rw [h]; exact iOwn_op

theorem wStateVar_full_update (γ : GName) (σ σ' : Arr) (M M' : H WData) :
    wStateVar (GF := GF) γ 1 σ M ⊢ |==> wStateVar γ 1 σ' M' := by
  unfold wStateVar FracAgree.Frac.mk
  exact iOwn_update (Update.exclusive ⟨DFrac.valid_own_one, Agree.toAgree_valid⟩)


theorem wStateVar_alloc (σ : Arr) (M : H WData) :
    ⊢@{IProp GF} |==> ∃ γ, wStateVar γ 1 σ M := by
  unfold wStateVar FracAgree.Frac.mk
  exact iOwn_alloc (F := WStateRF H) _ ⟨DFrac.valid_own_one, Agree.toAgree_valid⟩

/-! ### The shadow counter

Ported from the same construction in `Iris.Bench.Array`. -/

theorem refAllocUpdate (n : Nat) :
    (● ((n : Nat) : Credit) : Auth Credit) ~~>
      (● ((n + 1 : Nat) : Credit)) • ◯ (1 : Credit) := by
  apply Auth.auth_update_alloc
  have h := LocalUpdate.op_discrete ((n : Nat) : Credit) (CMRA.unit : Credit) (1 : Credit)
    (by intro _; trivial)
  have e1 : CMRA.op (1 : Credit) ((n : Nat) : Credit) = ((n + 1 : Nat) : Credit) := by
    show 1 + n = n + 1
    omega
  have e2 : CMRA.op (1 : Credit) (CMRA.unit : Credit) = (1 : Credit) := by
    show 1 + 0 = 1
    rfl
  rw [e1, e2] at h
  exact h

theorem refAuth_alloc (d : WData) (n : Nat) :
    refAuth (GF := GF) d n ⊢ |==> (refAuth d (n + 1) ∗ refTok d) := by
  unfold refAuth refTok
  exact (iOwn_update (F := CntRF) (γ := d.cnt) (refAllocUpdate n)).trans
    (bupd_mono (iOwn_op (F := CntRF) (γ := d.cnt)).mp)

theorem refTok_pos (d : WData) (n : Nat) :
    refAuth (GF := GF) d n ∗ refTok d ⊢ ⌜0 < n⌝ := by
  unfold refAuth refTok
  iintro ⟨H₁, H₂⟩
  ihave Hv := (iOwn_cmraValid_op (F := CntRF)
    (a1 := (● ((n : Nat) : Credit) : Auth Credit))
    (a2 := (◯ (1 : Credit) : Auth Credit))) $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete (A := Auth Credit) $$ Hv with %Hv
  ipureintro
  rcases (Auth.both_dfrac_valid_discrete.mp Hv).2.1 with ⟨c, hc⟩
  have h2 : n = 1 + c := eq_of_eqv hc
  omega

/-- Two units force a count of at least two: what a thread that has upgraded a weak
    handle needs in order to know that releasing its temporary reference is not the
    last drop. -/
theorem refTok_two (d : WData) (n : Nat) :
    refAuth (GF := GF) d n ∗ refTok d ∗ refTok d ⊢ ⌜2 ≤ n⌝ := by
  unfold refAuth refTok
  iintro ⟨H₁, H₂, H₃⟩
  ihave H₄ := (iOwn_op (F := CntRF) (γ := d.cnt)
    (a1 := (◯ (1 : Credit) : Auth Credit))
    (a2 := (◯ (1 : Credit) : Auth Credit))).mpr $$ [H₂ H₃]
  · isplitl [H₂] <;> iassumption
  ihave Hv := (iOwn_cmraValid_op (F := CntRF)
    (a1 := (● ((n : Nat) : Credit) : Auth Credit))
    (a2 := ((◯ (1 : Credit) : Auth Credit) • (◯ (1 : Credit) : Auth Credit)))) $$ [H₁ H₄]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete (A := Auth Credit) $$ Hv with %Hv
  ipureintro
  rw [← Auth.frag_op] at Hv
  rcases (Auth.both_dfrac_valid_discrete.mp Hv).2.1 with ⟨c, hc⟩
  have h2 : n = (1 + 1) + c := eq_of_eqv hc
  omega

/-- Allocate a cell's shadow counter at one, handing out the first unit. -/
theorem refAuth_alloc_one :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      iOwn (F := CntRF) γ (● ((1 : Nat) : Credit)) ∗ iOwn (F := CntRF) γ (◯ (1 : Credit)) := by
  ihave H := iOwn_alloc (F := CntRF)
      ((● ((1 : Nat) : Credit) : Auth Credit) • ◯ (1 : Credit))
      (Auth.auth_both_valid_2 (by trivial) ⟨0, by rfl⟩)
  imod H with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply (iOwn_op (F := CntRF) (γ := γ)).mp $$ H

end Defs

end RA

/-! ## Resources -/

section Resources

variable {H : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H Nat]
variable [HeapLangGS hlc GF] [RwLockG GF] [ArcG GF] [ArrG GF H] [WArrG GF H]

noncomputable section

/-- The array invariant's namespace. -/
def arrN : Namespace := ndot nroot "wlist"

/-- `k + 1` halves.  Used to size the read-permit deposit below; `Qp` is strictly
    positive, so there is no `0` case. -/
def qHalvesSucc : Nat → Qp
  | 0 => q1_2
  | k + 1 => qHalvesSucc k + q1_2

/-- The platform read credit parked in a cell's reference-count ledger: half a permit
    for every reference beyond the one the list itself holds.

    This is the crux of the design.  Reference counts have to live *outside* the
    platform lock, because duplicating a weak handle takes no lock at all.  But
    revocation has to know that the reference it drops is the last one, or it cannot
    claim the cell is freed.  A thread only ever holds a temporary strong reference
    from inside a platform *read* critical section, so it can afford to leave a
    receipt; revocation runs with the platform held *exclusively*, and a read permit
    is inconsistent with that.  The counts stay lock-free, yet are pinned by the lock
    exactly when it matters. -/
def arcDeposit (γP : GName) : Nat → IProp GF
  | 0 => iprop% emp
  | 1 => iprop% emp
  | k + 2 => rwGuardFrac γP RwLock.Mode.read (qHalvesSucc k)

instance instArcDepositTimeless (γP : GName) (n : Nat) :
    Timeless (arcDeposit (GF := GF) γP n) := by
  match n with
  | 0 => unfold arcDeposit; infer_instance
  | 1 => unfold arcDeposit; infer_instance
  | _ + 2 => unfold arcDeposit; infer_instance

/-- Taking on one more reference costs half a read permit — at every count at which a
    reference can actually be taken on. -/
theorem arcDeposit_succ (γP : GName) (n : Nat) (h : 1 ≤ n) :
    arcDeposit (GF := GF) γP (n + 1) ⊣⊢
      arcDeposit γP n ∗ rwGuardFrac γP RwLock.Mode.read q1_2 := by
  match n, h with
  | 1, _ =>
      simp only [arcDeposit, qHalvesSucc]
      exact (emp_sep (PROP := IProp GF)).symm
  | k + 2, _ =>
      simp only [arcDeposit, qHalvesSucc]
      exact RwLock.rwGuardFrac_split _ _ (qHalvesSucc k) q1_2

/-- Two or more references means somebody is holding the platform for reading. -/
theorem arcDeposit_read (γP : GName) (n : Nat) (h : 2 ≤ n) :
    arcDeposit (GF := GF) γP n ⊢ ∃ q : Qp, rwGuardFrac γP RwLock.Mode.read q := by
  match n, h with
  | k + 2, _ =>
      simp only [arcDeposit]
      iintro H
      iexists (qHalvesSucc k)
      iexact H

/-- One cell's reference-count ledger.

    `arcAuth γ 0 m` owns no memory, so this stays true after the cell is freed and
    nothing ever has to be torn down — which is what lets revocation actually
    deallocate.

    The disjunction is the ledger.  While the cell is in the list, the list's own
    reference is represented by the `refTok` held *here*; a thread holding a
    temporary reference holds a second one, so `refTok_two` tells it its drop is not
    the last.  Once the cell has been revoked the count is zero for good, and
    `cellDead` records that, so a stale weak handle can be shown to fail to
    upgrade. -/
def arcCell (γP : GName) (d : WData) : IProp GF := iprop%
  ∃ n m : Nat, arcAuth d.arc n m ∗ refAuth d n ∗
    ((refTok d ∗ arcDeposit γP n) ∨ (cellDead d.cell ∗ ⌜n = 0⌝))

instance instArcCellTimeless (γP : GName) (d : WData) :
    Timeless (arcCell (GF := GF) γP d) := by unfold arcCell; infer_instance

/-- Every allocated cell's ledger, indexed by the metadata map.

    This is the half of the array invariant that does **not** depend on the platform
    lock: duplicating a weak handle takes no lock, so the counts have to be reachable
    while another thread holds the platform exclusively.  Keeping it in the *same*
    invariant as the physical state is what makes `arcDeposit`'s argument work —
    opening the invariant once yields both the count and the platform's lock
    state. -/
def arcNodes (γP : GName) (M : H WData) : IProp GF := iprop%
  [∗map] id ↦ d ∈ M, arcCell γP d

instance instArcNodesTimeless (γP : GName) (M : H WData) :
    Timeless (arcNodes (GF := GF) (H := H) γP M) := by
  unfold arcNodes
  exact BigSepM.bigSepM_timeless (M := H)
    (Φ := fun (_ : Nat) (e : WData) => arcCell (GF := GF) γP e)
    (fun {_} {_} _ => inferInstance)

theorem arcNodes_acc (γP : GName) (M : H WData) (id : Nat) (d : WData)
    (hlookup : get? M id = some d) :
    arcNodes (GF := GF) γP M ⊢ arcCell γP d ∗ (arcCell γP d -∗ arcNodes γP M) :=
  (BigSepM.bigSepM_lookup_acc (M := H)
    (Φ := fun (_ : Nat) (e : WData) => arcCell (GF := GF) γP e) hlookup).mp

theorem arcNodes_insert (γP : GName) (M : H WData) (id : Nat) (d : WData)
    (hfresh : get? M id = none) :
    arcNodes (GF := GF) γP M ∗ arcCell γP d ⊢ arcNodes γP (Std.insert M id d) := by
  unfold arcNodes
  refine .trans ?_ (BigSepM.bigSepM_insert (M := H)
    (Φ := fun (_ : Nat) (e : WData) => arcCell (GF := GF) γP e) hfresh).mpr
  iintro ⟨H₁, H₂⟩
  iframe

theorem arcNodes_empty (γP : GName) :
    ⊢@{IProp GF} arcNodes (H := H) γP ∅ :=
  (BigSepM.bigSepM_eqv_empty (M := H)
    (Φ := fun (_ : Nat) (e : WData) => arcCell (GF := GF) γP e) rfl).mpr

/-- Cells that have left the list are dead.  Persistent, so unlike `Array`'s
    retired-cell table this costs nothing to carry around: a revoked cell leaves no
    resources behind, only the knowledge that it is gone. -/
def deadNodes (M : H WData) (cells : List (Nat × Int)) : IProp GF := iprop%
  [∗map] id ↦ d ∈ M, if id ∈ cells.map (·.1) then emp else cellDead d.cell

instance instDeadNodesPersistent (M : H WData) (cells : List (Nat × Int)) :
    Persistent (deadNodes (GF := GF) M cells) := by
  unfold deadNodes
  refine BigSepM.bigSepM_persistent (M := H) (Φ := fun (id : Nat) (d : WData) =>
    iprop% if id ∈ cells.map (·.1) then emp else cellDead (GF := GF) d.cell) ?_
  intro k x _
  by_cases h : k ∈ cells.map (·.1) <;> simp only [h, reduceIte] <;> infer_instance

instance instDeadNodesTimeless (M : H WData) (cells : List (Nat × Int)) :
    Timeless (deadNodes (GF := GF) M cells) := by
  unfold deadNodes
  refine BigSepM.bigSepM_timeless (M := H) (Φ := fun (id : Nat) (d : WData) =>
    iprop% if id ∈ cells.map (·.1) then emp else cellDead (GF := GF) d.cell) ?_
  intro k x _
  by_cases h : k ∈ cells.map (·.1) <;> simp only [h, reduceIte] <;> infer_instance

theorem deadNodes_empty (cells : List (Nat × Int)) :
    ⊢@{IProp GF} deadNodes (H := H) ∅ cells := by
  unfold deadNodes
  exact (BigSepM.bigSepM_eqv_empty (M := H) rfl).mpr

/-- Growing the live set only turns obligations into `emp`. -/
theorem deadNodes_grow (M : H WData) (cells cells' : List (Nat × Int))
    (h : ∀ i, i ∈ cells.map (·.1) → i ∈ cells'.map (·.1)) :
    deadNodes (GF := GF) M cells ⊢ deadNodes M cells' := by
  unfold deadNodes
  refine BigSepM.bigSepM_mono (M := H) ?_
  intro k v _
  by_cases h₁ : k ∈ cells.map (·.1)
  · rw [if_pos h₁, if_pos (h k h₁)]
    exact .rfl
  · rw [if_neg h₁]
    by_cases h₂ : k ∈ cells'.map (·.1)
    · rw [if_pos h₂]
      exact Affine.affine
    · rw [if_neg h₂]
      exact .rfl

/-- A fresh cell that joins the list adds nothing to the ledger. -/
theorem deadNodes_insert_live (M : H WData) (cells : List (Nat × Int))
    (id : Nat) (d : WData) (hfresh : get? M id = none) (hlive : id ∈ cells.map (·.1)) :
    deadNodes (GF := GF) M cells ⊢ deadNodes (Std.insert M id d) cells := by
  unfold deadNodes
  refine .trans ?_ (BigSepM.bigSepM_insert (M := H)
    (Φ := fun (i : Nat) (e : WData) =>
      iprop% if i ∈ cells.map (·.1) then emp else cellDead (GF := GF) e.cell)
    hfresh).mpr
  rw [if_pos hlive]
  exact (emp_sep (PROP := IProp GF)).mpr

theorem deadNodes_lookup (M : H WData) (cells : List (Nat × Int)) (id : Nat) (d : WData)
    (hlookup : get? M id = some d) (hgone : id ∉ cells.map (·.1)) :
    deadNodes (GF := GF) M cells ⊢ cellDead d.cell := by
  unfold deadNodes
  refine (BigSepM.bigSepM_lookup (M := H)
    (Φ := fun (id : Nat) (d : WData) =>
      iprop% if id ∈ cells.map (·.1) then emp else cellDead (GF := GF) d.cell)
    hlookup).trans ?_
  rw [if_neg hgone]
  exact .rfl

/-- A strong reference to the cell named `id`, as stored in a predecessor's link. -/
def wSuccRef (γ : GName) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ d : WData, wMetaAt γ id d ∗ isArc d.arc node d.mux

/-- The contents of a cell.  Unlike `Array` there is no revocation flag: a cell that
    has left the list has been freed, so no client can be looking at one. -/
def payload (γ : GName) (d : WData) : Option Nat → IProp GF
  | none => iprop%
      d.ptr ↦ hl_val((#d.val, none()))
  | some id => iprop%
      ∃ node : Val,
        d.ptr ↦ hl_val((#d.val, some(&node))) ∗ wSuccRef γ node id

instance instPayloadTimeless (γ : GName) (d : WData) (nxt : Option Nat) :
    Timeless (payload (GF := GF) (H := H) γ d nxt) := by
  cases nxt <;> (unfold payload wSuccRef; infer_instance)

/-- What a cell contributes to the list while the platform is held exclusively. -/
def nodeSlotExclusive (d : WData) (C : Qp → IProp GF) (P : IProp GF) : IProp GF := iprop%
  isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗ C 1 ∗ P

/-- The same under a platform read lock, where another reader may be part-way
    through a write on this cell.  The `rwGuardFrac` it leaves behind is what proves
    the list is quiescent again once the platform lock is released. -/
def nodeSlotSharedBody (γP : GName) (C : Qp → IProp GF) (P : IProp GF) :
    RwLock.State → IProp GF
  | .write  => iprop% rwGuardFrac γP RwLock.Mode.read q1_2 ∗ C q1_4
  | .read _ => iprop% False
  | .free   => iprop% P ∗ C 1

def nodeSlotShared (γP : GName) (d : WData) (C : Qp → IProp GF) (P : IProp GF) :
    IProp GF := iprop%
  ∃ s : RwLock.State, isRwLock d.rw d.mux s hl_val(#d.ptr) ∗ nodeSlotSharedBody γP C P s

abbrev Slot (GF : BundledGFunctors) [HeapLangGS hlc GF] [ArcG GF] [ArrG GF H] [WArrG GF H] :=
  WData → (Qp → IProp GF) → IProp GF → IProp GF

abbrev aliveSlot (slot : Slot (H := H) GF) (γ : GName) (d : WData) (nxt : Option Nat) :
    IProp GF :=
  slot d (fun q => cellAlive d.cell q nxt) (payload γ d nxt)

/-- The chain.  There is no companion big-op over retired cells: a cell that leaves
    the list is freed, and all that remains of it is `arcAuth _ 0 _` inside its own
    invariant. -/
def isGhostHelp (slot : Slot (H := H) GF) (γ : GName)
    (tail : Option Nat) : List (Nat × Int) → IProp GF
  | [] => iprop% emp
  | (id, x) :: cells => iprop%
      ∃ d : WData,
        ⌜x = d.val⌝ ∗ wMetaAt γ id d ∗
        aliveSlot slot γ d (nextIdOr cells tail) ∗
        isGhostHelp slot γ tail cells

def isGhost (slot : Slot (H := H) GF) (γ : GName)
    (cells : List (Nat × Int)) : IProp GF :=
  isGhostHelp slot γ none cells

/-- "This slot interpretation is timeless whenever the resources it is applied to
    are."  Has to be a class: Lean's instance search does not look through a `∀`. -/
class SlotTimeless (slot : Slot (H := H) GF) : Prop where
  out : ∀ (d : WData) (C : Qp → IProp GF) (P : IProp GF),
    (∀ q, Timeless (C q)) → Timeless P → Timeless (slot d C P)

instance instNodeSlotSharedBodyTimeless (γP : GName) (C : Qp → IProp GF) (P : IProp GF)
    [∀ q, Timeless (C q)] [Timeless P] (s : RwLock.State) :
    Timeless (nodeSlotSharedBody (GF := GF) γP C P s) := by
  cases s <;> simp only [nodeSlotSharedBody] <;> infer_instance

instance instNodeSlotSharedTimeless (γP : GName) (d : WData)
    (C : Qp → IProp GF) (P : IProp GF) [∀ q, Timeless (C q)] [Timeless P] :
    Timeless (nodeSlotShared (GF := GF) γP d C P) := by
  unfold nodeSlotShared; infer_instance

instance instNodeSlotExclusiveTimeless (d : WData)
    (C : Qp → IProp GF) (P : IProp GF) [∀ q, Timeless (C q)] [Timeless P] :
    Timeless (nodeSlotExclusive (GF := GF) d C P) := by
  unfold nodeSlotExclusive; infer_instance

instance instNodeSlotSharedSlotTimeless (γP : GName) :
    SlotTimeless (H := H) (nodeSlotShared (GF := GF) γP) :=
  ⟨fun _ _ _ hC hP => by haveI := hC; haveI := hP; infer_instance⟩

instance instNodeSlotExclusiveSlotTimeless :
    SlotTimeless (GF := GF) (H := H) nodeSlotExclusive :=
  ⟨fun _ _ _ hC hP => by haveI := hC; haveI := hP; infer_instance⟩

instance instAliveSlotTimeless (slot : Slot (H := H) GF) [inst : SlotTimeless slot]
    (γ : GName) (d : WData) (nxt : Option Nat) :
    Timeless (aliveSlot slot γ d nxt) :=
  inst.out d _ _ (fun _ => inferInstance) inferInstance

instance instIsGhostHelpTimeless (slot : Slot (H := H) GF)
    [inst : SlotTimeless slot] (γ : GName) (tail : Option Nat) :
    ∀ cells, Timeless (isGhostHelp slot γ tail cells)
  | [] => by unfold isGhostHelp; infer_instance
  | (_, _) :: cs => by
      have := instIsGhostHelpTimeless slot (inst := inst) γ tail cs
      unfold isGhostHelp
      infer_instance

instance instIsGhostTimeless (slot : Slot (H := H) GF)
    [inst : SlotTimeless slot] (γ : GName) (cells : List (Nat × Int)) :
    Timeless (isGhost slot γ cells) := by
  unfold isGhost
  exact instIsGhostHelpTimeless slot (inst := inst) γ none cells

def arrContentAt (γ : WArrγ) (M : H WData) (σ : Arr) : IProp GF := iprop%
  wMetaMap γ.l q1_2 M ∗ ⌜σ.wellFormed⌝ ∗ ⌜∀ id, dom M id ↔ id < σ.counter⌝ ∗
  deadNodes M σ.cells ∗ isGhost nodeSlotExclusive γ.l σ.cells

def arrContent (γ : WArrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H WData, arrContentAt γ M σ

def arrShared (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr) : IProp GF := iprop%
  wMetaMap γ.l q1_2 M ∗ ⌜σ.wellFormed⌝ ∗ ⌜∀ id, dom M id ↔ id < σ.counter⌝ ∗
  deadNodes M σ.cells ∗ isGhost (nodeSlotShared γp) γ.l σ.cells

def isPhysical (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr) :
    RwLock.State → IProp GF
  | .write  => iprop% emp
  | .read _ => iprop% arrShared γ γp M σ ∗ wStateVar γ.s q3_4 σ M
  | .free   => iprop% arrContentAt γ M σ ∗ wStateVar γ.s q3_4 σ M

def isPlatform (ρ : GName) (s : RwLock.State) (platform : Val) : IProp GF := iprop%
  ∃ α : GName, ∃ gate : Val, ∃ cell : Loc,
    arcHasStrong α ∗ isArc α platform gate ∗
    isRwLock ρ gate s hl_val(#cell) ∗ cell ↦ hl_val(#())

instance instArrContentAtTimeless (γ : WArrγ) (M : H WData) (σ : Arr) :
    Timeless (arrContentAt (GF := GF) γ M σ) := by unfold arrContentAt; infer_instance
instance instArrContentTimeless (γ : WArrγ) (σ : Arr) :
    Timeless (arrContent (GF := GF) γ σ) := by unfold arrContent; infer_instance
instance instArrSharedTimeless (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr) :
    Timeless (arrShared (GF := GF) γ γp M σ) := by unfold arrShared; infer_instance
instance instIsPhysicalTimeless (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr)
    (s : RwLock.State) :
    Timeless (isPhysical (GF := GF) γ γp M σ s) := by
  cases s <;> simp only [isPhysical] <;> infer_instance
instance instIsPlatformTimeless (ρ : GName) (s : RwLock.State) (platform : Val) :
    Timeless (isPlatform (GF := GF) ρ s platform) := by unfold isPlatform; infer_instance

/-- The half of the invariant the platform lock does not touch. -/
def arcPart (γ : WArrγ) (γP : GName) : IProp GF := iprop%
  ∃ M : H WData, wMetaMap γ.l q1_2 M ∗ arcNodes γP M

/-- …and the half it does. -/
def arrPhysPart (γ : WArrγ) (γp : GName) (platform : Val) : IProp GF := iprop%
  ∃ s : RwLock.State, ∃ M : H WData, ∃ σ : Arr,
    isPlatform γp s platform ∗ isPhysical γ γp M σ s

/-- Splitting the body vertically rather than putting the counts in an invariant of
    their own is what keeps everything timeless — an invariant nested inside an
    invariant body is not, and `aacc_inv` needs it to be. -/
def arrInvBody (γ : WArrγ) (γp : GName) (platform : Val) : IProp GF := iprop%
  arcPart γ γp ∗ arrPhysPart γ γp platform

instance instArcPartTimeless (γ : WArrγ) (γP : GName) :
    Timeless (arcPart (GF := GF) γ γP) := by unfold arcPart; infer_instance
instance instArrPhysPartTimeless (γ : WArrγ) (γp : GName) (platform : Val) :
    Timeless (arrPhysPart (GF := GF) γ γp platform) := by unfold arrPhysPart; infer_instance
instance instArrInvBodyTimeless (γ : WArrγ) (γp : GName) (platform : Val) :
    Timeless (arrInvBody (GF := GF) γ γp platform) := by unfold arrInvBody; infer_instance

def isArrInv (γ : WArrγ) (γp : GName) (platform : Val) : IProp GF :=
  inv arrN (arrInvBody γ γp platform)

instance instIsArrInvPersistent (γ : WArrγ) (γp : GName) (platform : Val) :
    Persistent (isArrInv (GF := GF) (H := H) γ γp platform) := by
  unfold isArrInv; infer_instance

def arrFrag (γ : WArrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H WData, wStateVar γ.s q1_4 σ M

/-- A list that has not been handed to a platform yet. -/
def Arr.isList (γ : WArrγ) (γP : GName) (σ : Arr) : IProp GF := iprop%
  ∃ M : H WData,
    wMetaMap γ.l q1_2 M ∗ arcNodes γP M ∗ arrContentAt γ M σ ∗ wStateVar γ.s 1 σ M

/-- Persistent knowledge that `id` names the cell described by `d`. -/
def Arr.isNode (γ : WArrγ) (id : Nat) (d : WData) : IProp GF := iprop%
  wMetaAt γ.l id d

instance instIsNodePersistent (γ : WArrγ) (id : Nat) (d : WData) :
    Persistent (Arr.isNode (GF := GF) (H := H) γ id d) := by
  unfold Arr.isNode; infer_instance

/-- A client's handle: **weak**.  Holding one does not keep the cell alive, which is
    exactly why revocation can free it. -/
def Arr.isId (γ : WArrγ) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ d : WData, Arr.isNode γ id d ∗ isWeak d.arc node d.mux

/-- The strong reference to the root, held by whoever called `init`.  Nothing inside
    the list owns it: dropping it frees the whole list. -/
def Arr.isRoot (γ : WArrγ) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ d : WData, Arr.isNode γ id d ∗ isArc d.arc node d.mux

end

end Resources


/-! ## Specifications -/

section Specs

variable {H : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H Nat]
variable [HeapLangGS hlc GF] [RwLockG GF] [ArcG GF] [ArrG GF H] [WArrG GF H]

theorem platformNew_spec :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&platformNew #())
    ⦃ platform, RET platform;
      ∃ γp, isPlatform γp .free platform ⦄ := by
  iintro %Φ - HΦ
  unfold platformNew
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %cell Hcell
  wp_pures
  wp_bind &RwLock.new _
  iapply RwLock.new_spec hl_val(#cell)
  · itrivial
  iintro %gate !> ⟨%γrw, Hlock⟩
  wp_pures
  iapply Arc.new_spec gate
  · itrivial
  iintro %platform !> ⟨%α, Hauth, Harc⟩
  iapply HΦ
  iexists γrw
  unfold isPlatform
  iexists α, gate, cell
  iframe Harc Hlock Hcell
  unfold arcHasStrong
  iexists 1, 0
  iframe Hauth
  ipureintro
  omega

/-- Allocate a cell.  Ownership of the successor link is moved in; what comes back
    holds the only strong reference to the new cell, and its ledger entry, ready to
    be added to `arcNodes`. -/
theorem new_spec (γ : GName) (γP : GName) (x : Int) (next : Val) (nxt : Option Nat) :
  ⊢@{IProp GF}
    ⦃ match nxt with
      | none => iprop% ⌜next = hl_val(none())⌝
      | some i => iprop% ∃ v : Val, ⌜next = hl_val(some(&v))⌝ ∗ wSuccRef γ v i ⦄
      hl(&new #x &next)
    ⦃ node, RET node;
      ∃ d : WData,
        ⌜x = d.val⌝ ∗
        arcCell γP d ∗
        isArc d.arc node d.mux ∗
        isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗
        cellAlive d.cell 1 nxt ∗
        payload γ d nxt ⦄ := by
  iintro %Φ Hpre HΦ
  iapply wp_fupd
  unfold new
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %p Hp
  wp_pures
  wp_bind &RwLock.new _
  iapply RwLock.new_spec hl_val(#p)
  · itrivial
  iintro %l !> ⟨%γrw, Hlock⟩
  wp_pures
  iapply Arc.new_spec l
  · itrivial
  iintro %a !> ⟨%γarc, Hauth, Harc⟩
  imod cellAlive_alloc nxt with ⟨%γcell, Hcell⟩
  imod refAuth_alloc_one with ⟨%γcnt, Hcnt, Htok⟩
  ihave Hbody : arcCell γP ⟨⟨γarc, γrw, γcell, l, p, x⟩, γcnt⟩ $$ [Hauth Hcnt Htok]
  · unfold arcCell refAuth refTok
    iexists 1, 0
    iframe Hauth Hcnt
    ileft
    isplitl [Htok]
    · iexact Htok
    · unfold arcDeposit
      itrivial
  imodintro
  iapply HΦ
  iexists ⟨⟨γarc, γrw, γcell, l, p, x⟩, γcnt⟩
  isplit
  · ipureintro; rfl
  isplitl [Hbody]
  · iexact Hbody
  isplitl [Harc]
  · iexact Harc
  iframe Hlock Hcell
  unfold payload
  cases nxt with
  | none =>
      icases Hpre with %hnext
      subst hnext
      iexact Hp
  | some i =>
      icases Hpre with ⟨%v, %hnext, Hsucc⟩
      subst hnext
      iexists v
      iframe

/-- `γP` is a parameter: the reference-count invariant mentions the platform's
    ghost name, but nothing in `init` touches the platform, so the specification
    holds for whichever platform the list is later bound to. -/
theorem init_spec (γP : GName) (x : Int) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&init #x)
    ⦃ root, RET root;
      ∃ γ : WArrγ, Arr.isList γ γP (Arr.init x) ∗ Arr.isRoot γ root 0 ⦄ := by
  iintro %Φ - HΦ
  iapply wp_fupd
  unfold init
  wp_pures
  imod wMetaMap_alloc with ⟨%γl, HM⟩
  iapply new_spec γl γP x hl_val(none()) none
  · ipureintro; rfl
  iintro %root !> ⟨%d, %hval, Hcnt, Harc, Hlock, Hcell, Hpay⟩
  subst hval
  imod wMetaMap_insert γl (∅ : H WData) 0 d (by simp [get?_empty]) $$ HM with ⟨HM, #Hat⟩
  imod wStateVar_alloc (Arr.init d.val) (Std.insert (∅ : H WData) 0 d) with ⟨%γs, Hstate⟩
  imodintro
  iapply HΦ
  iexists ⟨γl, γs⟩
  icases (wMetaMap_split γl (Std.insert (∅ : H WData) 0 d)).mp $$ HM with ⟨HM₁, HM₂⟩
  isplitl [HM₁ HM₂ Hstate Hcnt Hlock Hcell Hpay]
  · unfold Arr.isList arrContentAt Arr.init
    iexists (Std.insert (∅ : H WData) 0 d)
    iframe HM₁
    isplitl [Hcnt]
    · iapply arcNodes_insert γP (∅ : H WData) 0 d (get?_empty 0)
      isplitl []
      · iapply arcNodes_empty
      · iexact Hcnt
    isplitl [HM₂ Hlock Hcell Hpay]
    · iframe HM₂
      isplit
      · ipureintro; exact Arr.init_wellFormed d.val
      isplit
      · ipureintro
        exact wMetaMap_insert_counter_dom (∅ : H WData) 0 d
          (by intro id; unfold dom; simp [get?_empty])
      isplitl []
      · iapply deadNodes_insert_live (∅ : H WData) [(0, d.val)] 0 d (get?_empty 0) (by simp)
        iapply deadNodes_empty
      · unfold isGhost isGhostHelp
        iexists d
        isplit
        · ipureintro; rfl
        iframe Hat
        isplitl [Hlock Hcell Hpay]
        · unfold aliveSlot nodeSlotExclusive nextIdOr
          iframe Hlock Hcell Hpay
        · unfold isGhostHelp
          itrivial
    · iframe Hstate
  · unfold Arr.isRoot Arr.isNode
    dsimp only []
    iexists d
    iframe Harc
    iexact Hat

/-- Reach one cell's ledger through the invariant body.  `Arr.isNode` is persistent
    and the map is half-pinned in the invariant, so this needs nothing but the
    handle. -/
theorem arcPart_acc (γ : WArrγ) (γP : GName) (id : Nat) (d : WData) :
  ⊢@{IProp GF}
    arcPart γ γP -∗ Arr.isNode γ id d -∗
      arcCell γP d ∗ (arcCell γP d -∗ arcPart γ γP) := by
  iintro Hpart #Hnode
  iunfold arcPart at Hpart
  icases Hpart with ⟨%M, HM, Hnodes⟩
  iunfold Arr.isNode at Hnode
  ihave #Hlookup : ⌜get? M id = some d⌝ $$ [HM Hnode]
  · iapply wMetaMap_lookup γ.l q1_2 M id d $$ HM Hnode
  icases Hlookup with %hlookup
  icases arcNodes_acc γP M id d hlookup $$ Hnodes with ⟨Hcell, Hback⟩
  iframe Hcell
  iintro Hcell
  unfold arcPart
  iexists M
  iframe HM
  iapply Hback $$ Hcell

/-- Reassemble the invariant body from its two halves. -/
theorem arrInvBody_intro (γ : WArrγ) (γP : GName) (platform : Val) :
  ⊢@{IProp GF}
    arcPart γ γP -∗ arrPhysPart γ γP platform -∗ arrInvBody γ γP platform := by
  iintro H₁ H₂
  unfold arrInvBody
  iframe

/-- Take a weak handle on a cell the caller owns outright.  No *platform* lock is
    involved: the counts sit in the half of the invariant the platform lock does not
    govern, so this works even while another thread holds the list exclusively. -/
theorem handle_spec (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    ⦃ Arr.isRoot γ node id ⦄
      hl(&handle &node)
    ⦃ w, RET w;
      Arr.isRoot γ node id ∗ Arr.isId γ w id ⦄ := by
  iintro #Hinv %Φ Hroot HΦ
  iunfold Arr.isRoot at Hroot
  icases Hroot with ⟨%d, #Hnode, Harc⟩
  unfold handle
  wp_pures
  iapply Arc.downgrade_spec (γ := d.arc) node d.mux $$ Harc
  iunfold isArrInv at Hinv
  iauintro
  iinv Hinv as Hbody
  iunfold arrInvBody at Hbody
  icases Hbody with ⟨Hpart, Hphys⟩
  icases arcPart_acc γ γP id d $$ Hpart Hnode with ⟨Hcell, Hback⟩
  iunfold arcCell at Hcell
  icases Hcell with ⟨%n, %m, Hauth, Hcnt, Hled⟩
  iaaccintro' with Hauth
  · iintro Hauth
    imodintro
    isplitl [Hauth Hcnt Hled Hback Hphys]
    · iapply arrInvBody_intro γ γP platform $$ [Hback Hauth Hcnt Hled] Hphys
      iapply Hback
      unfold arcCell
      iexists n, m
      iframe
    · iframe
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro ⟨Hauth, Harc, Hweak⟩
    imodintro
    isplitl [Hauth Hcnt Hled Hback Hphys]
    · iapply arrInvBody_intro γ γP platform $$ [Hback Hauth Hcnt Hled] Hphys
      iapply Hback
      unfold arcCell
      iexists n, (m + 1)
      iframe
    · iapply HΦ
      isplitl [Harc]
      · unfold Arr.isRoot
        iexists d
        iframe Harc
        iexact Hnode
      · unfold Arr.isId
        iexists d
        iframe Hweak
        iexact Hnode


/-! ### Logically atomic specifications

`Arr.insert σ id x` already returns `none` exactly when `id` is not in the list, and
"the upgrade failed" is precisely that case — so the abstract model needs no change
at all.  What *does* need justifying, and is the subject of the review below, is the
implication in the other direction: that a handle on a cell which is still in the
list can always be upgraded. -/

section Atomic

variable {H : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H Nat]
variable [HeapLangGS hlc GF] [RwLockG GF] [ArcG GF] [ArrG GF H] [WArrG GF H]

/-! ### Moving the chain between the exclusive and the shared view

A cell's slot looks different depending on whether the platform is held exclusively
(nobody else can be part-way through anything) or shared (somebody might be).  These
lemmas are the two directions; the interesting one is `…Upgrade`, which uses the
platform lock itself to rule out the intermediate states. -/

theorem nodeSlotSharedUpgrade (γP : GName) (d : WData) (C : Qp → IProp GF) (P : IProp GF)
    (mux ptr : Val) :
  ⊢@{IProp GF}
    nodeSlotShared γP d C P -∗ isRwLock γP mux .free ptr -∗
      nodeSlotExclusive d C P ∗ isRwLock γP mux .free ptr := by
  iintro Hslot Hlock
  unfold nodeSlotShared nodeSlotExclusive
  icases Hslot with ⟨%s, H1, H2⟩
  rcases s with ⟨h1 | h2 | h3⟩ <;> dsimp only [nodeSlotSharedBody]
  · icases H2 with ⟨HP, HC⟩
    iframe
  · iframe
    iexfalso
    itrivial
  · icases H2 with ⟨Hg, HC⟩
    ihave Hf := (RwLock.rwGuardFrac_valid) $$ [Hlock Hg]
    iframe Hlock Hg
    icases Hf with %Hf
    cases Hf

theorem isGhostHelpUpgrade (γP : GName) (γ : GName) (tail : Option Nat)
    (mux ptr : Val) (cells : List (Nat × Int)) :
  ⊢@{IProp GF}
    isGhostHelp (nodeSlotShared γP) γ tail cells -∗
    isRwLock γP mux .free ptr -∗
      isGhostHelp nodeSlotExclusive γ tail cells ∗ isRwLock γP mux .free ptr := by
  induction cells with
  | nil =>
      simp only [isGhostHelp]
      iintro Hempty Hlock
      iframe
  | cons cell cells ih =>
      simp only [isGhostHelp]
      iintro Hghost Hlock
      icases Hghost with ⟨%d, Hd, Hmeta, Hslot, Hrest⟩
      ihave Hslot' := nodeSlotSharedUpgrade γP d _ _ mux ptr $$ Hslot Hlock
      icases Hslot' with ⟨Hslot, Hlock⟩
      ihave Hrest' := ih $$ Hrest Hlock
      icases Hrest' with ⟨Hrest, Hlock⟩
      iframe
      iexists d
      iframe

theorem nodeSlotExclusiveDowngrad (γP : GName) (d : WData) (C : Qp → IProp GF) (P : IProp GF) :
    nodeSlotExclusive d C P ⊢@{IProp GF} nodeSlotShared γP d C P := by
  unfold nodeSlotExclusive nodeSlotShared
  iintro H
  icases H with ⟨Hlock, HC, HP⟩
  iexists .free
  dsimp only [nodeSlotSharedBody]
  iframe

theorem isGhostHelpDowngrad (γP : GName) (γ : GName) (tail : Option Nat)
    (cells : List (Nat × Int)) :
    isGhostHelp (H := H) nodeSlotExclusive γ tail cells ⊢@{IProp GF}
      isGhostHelp (nodeSlotShared γP) γ tail cells := by
  induction cells with
  | nil => simp only [isGhostHelp]; iintro H; iexact H
  | cons cell cells ih =>
      simp only [isGhostHelp]
      iintro H
      icases H with ⟨%d, Hd, Hmeta, Hslot, Hrest⟩
      iexists d
      iframe
      isplitl [Hslot]
      · iapply nodeSlotExclusiveDowngrad γP $$ Hslot
      · iapply ih $$ Hrest

theorem arrSharedUpgrade (γ : WArrγ) (γP : GName) (M : H WData) (σ : Arr) (mux ptr : Val) :
  ⊢@{IProp GF}
    arrShared γ γP M σ -∗ isRwLock γP mux .free ptr -∗
      arrContentAt γ M σ ∗ isRwLock γP mux .free ptr := by
  unfold arrShared arrContentAt isGhost
  iintro H Hlock
  icases H with ⟨HM, %hwf, %hdom, #Hdead, Hghost⟩
  ihave Hres := isGhostHelpUpgrade γP γ.l none mux ptr σ.cells $$ Hghost Hlock
  icases Hres with ⟨Hghost, Hlock⟩
  iframe HM Hlock Hghost Hdead
  isplit
  · ipureintro; exact hwf
  · ipureintro; exact hdom

theorem arrContentAtDowngrad (γ : WArrγ) (γP : GName) (M : H WData) (σ : Arr) :
    arrContentAt γ M σ ⊢@{IProp GF} arrShared γ γP M σ := by
  unfold arrShared arrContentAt isGhost
  iintro H
  icases H with ⟨HM, %hwf, %hdom, #Hdead, Hghost⟩
  iframe HM Hdead
  isplit
  · ipureintro; exact hwf
  isplit
  · ipureintro; exact hdom
  · iapply isGhostHelpDowngrad γP γ.l none σ.cells $$ Hghost

theorem isGhostHelpAccIn (γ : GName) (d : WData)
    (slot : Slot (H := H) GF)
    (tail : Option Nat) (id : Nat) :
    ∀ cells : List (Nat × Int), id ∈ cells.map (·.1) →
    wMetaAt γ id d ⊢@{IProp GF} isGhostHelp slot γ tail cells -∗
      ∃ nxt : Option Nat,
        aliveSlot slot γ d nxt ∗
        (aliveSlot slot γ d nxt -∗
          isGhostHelp slot γ tail cells) := by
  intro cells
  induction cells with
  | nil => intro h; exact absurd h (by simp)
  | cons c cells ih =>
    rcases c with ⟨id', x⟩
    intro hin
    iintro #Hmeta Hlist
    simp only [isGhostHelp]
    icases Hlist with ⟨%d', %hval, #Hmeta', Hslot, Hrest⟩
    by_cases hhead : id' = id
    · subst hhead
      ihave %hd := wMetaAt_agree $$ Hmeta' Hmeta
      subst hd
      iexists (nextIdOr cells tail)
      iframe Hslot
      iintro Hslot
      iexists d'
      iframe Hmeta' Hslot Hrest
      ipureintro
      exact hval
    · have hin' : id ∈ cells.map (·.1) := by
        simp only [List.map_cons, List.mem_cons] at hin
        rcases hin with h | h
        · exact absurd h.symm hhead
        · exact h
      ihave Hacc := ih hin' $$ Hmeta Hrest
      icases Hacc with ⟨%nxt, Hslot', Hback⟩
      iexists nxt
      iframe Hslot'
      iintro Hslot'
      ihave Hrest' := Hback $$ Hslot'
      iexists d'
      iframe Hmeta' Hslot Hrest'
      ipureintro
      exact hval

/-- `isGhost` is `isGhostHelp` at `tail = none`. -/
theorem isGhostAccIn (γ : GName) (d : WData)
    (slot : Slot (H := H) GF)
    (id : Nat) (cells : List (Nat × Int)) (hin : id ∈ cells.map (·.1)) :
    wMetaAt γ id d ⊢@{IProp GF} isGhost slot γ cells -∗
      ∃ nxt : Option Nat,
        aliveSlot slot γ d nxt ∗
        (aliveSlot slot γ d nxt -∗
          isGhost slot γ cells) :=
  isGhostHelpAccIn γ d slot none id cells hin

theorem isGhostHelpAccInsert (γ : GName) (d : WData) (slot : Slot (H := H) GF)
    (tail : Option Nat) (id : Nat) (x : Int) (post : List (Nat × Int)) :
    ∀ pre : List (Nat × Int),
    wMetaAt γ id d ⊢@{IProp GF}
      isGhostHelp slot γ tail (pre ++ (id, x) :: post) -∗
        aliveSlot slot γ d (nextIdOr post tail) ∗
        ((aliveSlot slot γ d (nextIdOr post tail) -∗
            isGhostHelp slot γ tail (pre ++ (id, x) :: post)) ∧
         (∀ nid : Nat, ∀ v : Int, ∀ dNew : WData, ⌜v = dNew.val⌝ -∗ wMetaAt γ nid dNew -∗
            aliveSlot slot γ d (some nid) -∗
            aliveSlot slot γ dNew (nextIdOr post tail) -∗
            isGhostHelp slot γ tail (pre ++ (id, x) :: (nid, v) :: post))) := by
  intro pre
  induction pre with
  | nil =>
      iintro #Hmeta Hlist
      simp only [List.nil_append, isGhostHelp]
      icases Hlist with ⟨%d', %hval, #Hmeta', Hslot, Hrest⟩
      ihave %hd := wMetaAt_agree $$ Hmeta' Hmeta
      subst hd
      iframe Hslot
      isplit
      · iintro Hd
        iexists d'
        isplit
        · ipureintro; exact hval
        iframe Hmeta' Hd Hrest
      · iintro %nid %v %dNew %hv #HmetaN Hd Hnew
        simp only [nextIdOr]
        iexists d'
        isplit
        · ipureintro; exact hval
        iframe Hmeta' Hd
        iexists dNew
        isplit
        · ipureintro; exact hv
        iframe HmetaN Hnew Hrest
  | cons c pre ih =>
      rcases c with ⟨id', x'⟩
      iintro #Hmeta Hlist
      simp only [List.cons_append, isGhostHelp]
      icases Hlist with ⟨%d', %hval, #Hmeta', Hslot, Hrest⟩
      ihave Hacc := ih $$ Hmeta Hrest
      icases Hacc with ⟨Hslot', Hboth⟩
      iframe Hslot'
      isplit
      · iintro Hd
        icases Hboth with ⟨Hsame, -⟩
        ihave Hrest' := Hsame $$ Hd
        iexists d'
        isplit
        · ipureintro; exact hval
        iframe Hmeta' Hrest' Hslot
      · iintro %nid %v %dNew %hv #HmetaN Hd Hnew
        icases Hboth with ⟨-, Hback⟩
        ihave Hrest' := Hback $$ %nid %v %dNew %hv HmetaN Hd Hnew
        iexists d'
        isplit
        · ipureintro; exact hval
        iframe Hmeta' Hrest'
        cases pre with
        | nil => simp only [List.nil_append, nextIdOr]; iexact Hslot
        | cons c' pre' => simp only [List.cons_append, nextIdOr]; iexact Hslot


/-- The mirror image, for revoke: hand out the slot at `id` *and* the whole chain
    that follows it, and take back a chain that stops at `id`.  What comes out as
    `isGhostHelp … post` is what `Impl.revokeSuffix` walks. -/
theorem isGhostHelpAccTruncate (γ : GName) (d : WData) (slot : Slot (H := H) GF)
    (tail : Option Nat) (id : Nat) (x : Int) (post : List (Nat × Int)) :
    ∀ pre : List (Nat × Int),
    wMetaAt γ id d ⊢@{IProp GF}
      isGhostHelp slot γ tail (pre ++ (id, x) :: post) -∗
        aliveSlot slot γ d (nextIdOr post tail) ∗
        isGhostHelp slot γ tail post ∗
        (aliveSlot slot γ d tail -∗ isGhostHelp slot γ tail (pre ++ [(id, x)])) := by
  intro pre
  induction pre with
  | nil =>
      iintro #Hmeta Hlist
      simp only [List.nil_append, isGhostHelp]
      icases Hlist with ⟨%d', %hval, #Hmeta', Hslot, Hrest⟩
      ihave %hd := wMetaAt_agree $$ Hmeta' Hmeta
      subst hd
      iframe Hslot Hrest
      iintro Hd
      simp only [nextIdOr]
      iexists d'
      isplit
      · ipureintro; exact hval
      iframe Hmeta' Hd
  | cons c pre ih =>
      rcases c with ⟨id', x'⟩
      iintro #Hmeta Hlist
      simp only [List.cons_append, isGhostHelp]
      icases Hlist with ⟨%d', %hval, #Hmeta', Hslot, Hrest⟩
      ihave Hacc := ih $$ Hmeta Hrest
      icases Hacc with ⟨Hslot', Hpost, Hback⟩
      iframe Hslot' Hpost
      iintro Hd
      ihave Hrest' := Hback $$ Hd
      iexists d'
      isplit
      · ipureintro; exact hval
      iframe Hmeta' Hrest'
      cases pre with
      | nil => simp only [List.nil_append, nextIdOr]; iexact Hslot
      | cons c' pre' => simp only [List.cons_append, nextIdOr]; iexact Hslot


/-! ### Reading a cell's status off the persistent dead witness

`deadNodes` is persistent, so unlike `Array` this direction costs nothing to keep
around; and a live slot carries `cellAlive` in *every* lock state (at `1` when free,
at `1/4` when write-locked), so the refutation always lands. -/

theorem cellDead_not_mem (γP : GName) (γ : GName) (σ : Arr) (d : WData) (id : Nat) :
  ⊢@{IProp GF}
    wMetaAt γ id d -∗ cellDead d.cell -∗ isGhost (nodeSlotShared γP) γ σ.cells -∗
      ⌜id ∉ σ.cells.map (·.1)⌝ := by
  iintro #Hmeta #Hcd Hghost
  by_cases hin : id ∈ σ.cells.map (·.1)
  · ihave Hacc := isGhostAccIn γ d (nodeSlotShared γP) id σ.cells hin $$ Hmeta Hghost
    icases Hacc with ⟨%nxt, Hslot, -⟩
    iunfold nodeSlotShared at Hslot
    icases Hslot with ⟨%s, -, Hstate⟩
    iexfalso
    rcases s with ⟨h1 | h2 | h3⟩ <;> dsimp only [nodeSlotSharedBody]
    · icases Hstate with ⟨-, Halive⟩
      iapply cellAlive_dead_False d.cell 1 nxt
      isplitl [Halive] <;> iassumption
    · iexact Hstate
    · icases Hstate with ⟨-, Halive⟩
      iapply cellAlive_dead_False d.cell q1_4 nxt
      isplitl [Halive] <;> iassumption
  · ipureintro
    exact hin

theorem cellDead_not_mem_exclusive (γ : GName) (σ : Arr) (d : WData) (id : Nat) :
  ⊢@{IProp GF}
    wMetaAt γ id d -∗ cellDead d.cell -∗ isGhost nodeSlotExclusive γ σ.cells -∗
      ⌜id ∉ σ.cells.map (·.1)⌝ := by
  iintro #Hmeta #Hcd Hghost
  by_cases hin : id ∈ σ.cells.map (·.1)
  · ihave Hacc := isGhostAccIn γ d nodeSlotExclusive id σ.cells hin $$ Hmeta Hghost
    icases Hacc with ⟨%nxt, Hslot, -⟩
    iunfold nodeSlotExclusive at Hslot
    icases Hslot with ⟨-, Halive, -⟩
    iexfalso
    iapply cellAlive_dead_False d.cell 1 nxt
    isplitl [Halive] <;> iassumption
  · ipureintro
    exact hin

/-! ### The platform lock's effect on the invariant body -/

theorem isPhysical_read_acquire_first (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr) :
    isPhysical γ γp M σ .free ⊢@{IProp GF} isPhysical γ γp M σ (.read 1) := by
  simp only [isPhysical]
  iintro H
  icases H with ⟨Hcontent, Hstate⟩
  iframe Hstate
  iapply arrContentAtDowngrad γ γp M σ $$ Hcontent

theorem isPhysical_read_acquire_more (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr) (n : Nat) :
    isPhysical γ γp M σ (.read n) ⊢@{IProp GF} isPhysical γ γp M σ (.read (n + 1)) := .rfl

theorem isPhysical_read_release_nonlast (γ : WArrγ) (γp : GName) (M : H WData)
    (σ : Arr) (n : Nat) :
    isPhysical γ γp M σ (.read (n + 1)) ⊢@{IProp GF} isPhysical γ γp M σ (.read n) := .rfl

theorem isPhysical_read_release_last (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr)
    (mux ptr : Val) :
  ⊢@{IProp GF}
    isPhysical γ γp M σ (.read 1) -∗ isRwLock γp mux .free ptr -∗
      isPhysical γ γp M σ .free ∗ isRwLock γp mux .free ptr := by
  simp only [isPhysical]
  iintro H Hlock
  icases H with ⟨Hshared, Hstate⟩
  ihave Hres := arrSharedUpgrade γ γp M σ mux ptr $$ Hshared Hlock
  icases Hres with ⟨Hcontent, Hlock⟩
  iframe

theorem isPhysical_write_acquire (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr) :
    isPhysical γ γp M σ .free ⊢@{IProp GF}
      (arrContentAt γ M σ ∗ wStateVar γ.s q3_4 σ M) ∗ isPhysical γ γp M σ .write := by
  simp only [isPhysical]
  iintro H
  iframe

/-- Releasing the platform write lock is the linearisation point: the writer's `3/4`
    receipt only becomes a whole once the client's `1/4` arrives through the atomic
    update, and only a whole can advance the abstract state. -/
theorem isPhysical_write_release (γ : WArrγ) (γp : GName)
    (M M' : H WData) (σ σ' : Arr) :
  ⊢@{IProp GF}
    arrContentAt γ M' σ' -∗ wStateVar γ.s q3_4 σ M -∗ arrFrag γ σ ==∗
      isPhysical γ γp M' σ' .free ∗ arrFrag γ σ' := by
  simp only [isPhysical]
  iintro Hview Hout Hfrag
  iunfold arrFrag at Hfrag
  icases Hfrag with ⟨%M₀, Hinv⟩
  ihave #hag : ⌜σ = σ ∧ M₀ = M⌝ $$ [Hinv Hout]
  · iapply wStateVar_agree γ.s q1_4 q3_4 σ σ M₀ M
    isplitl [Hinv] <;> iassumption
  icases hag with ⟨-, %hM⟩
  subst hM
  ihave Hfull := (wStateVar_split γ.s σ M₀).mpr $$ [Hinv Hout]
  · isplitl [Hinv] <;> iassumption
  ihave Hupd := wStateVar_full_update γ.s σ σ' M₀ M' $$ Hfull
  imod Hupd with Hfull
  icases (wStateVar_split γ.s σ' M').mp $$ Hfull with ⟨Hinv', Hout'⟩
  imodintro
  iframe Hview Hout'
  unfold arrFrag
  iexists M'
  iframe

theorem arrFrag_agree (γ : WArrγ) (σ σ' : Arr) (M : H WData) :
    arrFrag γ σ ∗ wStateVar γ.s q3_4 σ' M ⊢@{IProp GF} ⌜σ = σ'⌝ := by
  unfold arrFrag
  iintro ⟨⟨%M₀, Hfrag⟩, Hout⟩
  icases wStateVar_agree γ.s q1_4 q3_4 σ σ' M₀ M $$ [Hfrag Hout] with %h
  · isplitl [Hfrag] <;> iassumption
  ipureintro
  exact h.1

/-- The `3/4` share is the platform write lock's receipt: no other lock state leaves
    that much of `wStateVar` unclaimed. -/
theorem isPhysical_write_pinned (γ : WArrγ) (γp : GName) (M M' : H WData)
    (σ σ' : Arr) (s : RwLock.State) :
    isPhysical γ γp M σ s ∗ wStateVar γ.s q3_4 σ' M' ⊢@{IProp GF} ⌜s = .write⌝ := by
  cases s <;> simp only [isPhysical] <;> iintro ⟨Hphys, Hout⟩
  · iexfalso
    icases Hphys with ⟨-, Hstate⟩
    icases wStateVar_frac_valid γ.s q3_4 q3_4 σ σ' M M' $$ [Hstate Hout] with %h
    · isplitl [Hstate] <;> iassumption
    exact absurd h q3_4_add_q3_4_invalid
  · iexfalso
    icases Hphys with ⟨-, Hstate⟩
    icases wStateVar_frac_valid γ.s q3_4 q3_4 σ σ' M M' $$ [Hstate Hout] with %h
    · isplitl [Hstate] <;> iassumption
    exact absurd h q3_4_add_q3_4_invalid
  · ipureintro; trivial

/-- A positive read credit says the platform is read-held.  Borrowed, not consumed:
    the conclusion is pure. -/
theorem isPlatform_read_guard_valid (ρ : GName) (s : RwLock.State) (platform : Val) (q : Qp) :
    isPlatform ρ s platform ∗ rwGuardFrac ρ RwLock.Mode.read q ⊢@{IProp GF}
      ⌜∃ n, s = .read (n + 1)⌝ := by
  unfold isPlatform
  iintro H
  icases H with ⟨Hplatform, Hguard⟩
  icases Hplatform with ⟨%α, %gate, %cell, Harc, Hhandle, Hlock, Hcell⟩
  ihave #Hcompat : ⌜RwLock.GuardCompatible s .read⌝ $$ [Hlock Hguard]
  · iapply RwLock.rwGuardFrac_valid _ _ _ _ _ q
    isplitl [Hlock] <;> iassumption
  icases Hcompat with %Hvalid
  ipureintro
  cases Hvalid with
  | read n => exact ⟨n, rfl⟩

theorem rwGuard_toFrac (γ : GName) :
    ⊢@{IProp GF} rwGuard γ RwLock.Mode.read -∗ rwGuardFrac γ RwLock.Mode.read 1 := by
  iintro H
  rw [← rwGuard_eq γ RwLock.Mode.read]
  iexact H

/-! ### Working the ledger

These four are where the design pays off.  Each turns a fact about the *lock* into a
fact about a *reference count*, or the other way round. -/

/-- **Gap 1.**  A cell that is still in the list has a positive count, so a weak
    handle on it upgrades successfully.  The evidence is the `refTok` the ledger
    itself holds while the cell is live. -/
theorem arcCell_live_pos (γP : GName) (d : WData) (n m : Nat) :
    arcAuth (GF := GF) d.arc n m ∗ refAuth d n ∗
      ((refTok d ∗ arcDeposit γP n) ∨ (cellDead d.cell ∗ ⌜n = 0⌝)) ∗
      cellAlive d.cell q1_4 nxt ⊢ ⌜0 < n⌝ := by
  iintro ⟨-, Hcnt, Hled, Halive⟩
  icases Hled with (⟨Htok, -⟩ | ⟨#Hcd, -⟩)
  · iapply refTok_pos d n
    isplitl [Hcnt] <;> iassumption
  · iexfalso
    iapply cellAlive_dead_False d.cell q1_4 nxt
    isplitl [Halive] <;> iassumption

/-- **Gap 2.**  A thread that has upgraded a weak handle holds a `refTok` of its own,
    so the ledger's copy proves the count is at least two and its own drop is not the
    last one. -/
theorem arcCell_two (γP : GName) (d : WData) (n : Nat) :
    refAuth (GF := GF) d n ∗
      ((refTok d ∗ arcDeposit γP n) ∨ (cellDead d.cell ∗ ⌜n = 0⌝)) ∗ refTok d ⊢
      ⌜2 ≤ n⌝ ∗ refAuth d n ∗ refTok d ∗ arcDeposit γP n ∗ refTok d := by
  iintro ⟨Hcnt, Hled, Hmine⟩
  icases Hled with (⟨Htok, Hdep⟩ | ⟨-, %hz⟩)
  · ihave #Hge : ⌜2 ≤ n⌝ $$ [Hcnt Htok Hmine]
    · iapply refTok_two d n
      isplitl [Hcnt]
      · iassumption
      isplitl [Htok] <;> iassumption
    iframe Hge Hcnt Htok Hdep Hmine
  · subst hz
    iexfalso
    icases refTok_pos d 0 $$ [Hcnt Hmine] with %h
    · isplitl [Hcnt] <;> iassumption
    exact absurd h (Nat.lt_irrefl 0)

/-- **Gap 3**, the one `Array` never closes.  Under the platform *write* lock there
    can be no read permit anywhere, so the deposit forces the count down to exactly
    one: the reference revocation is about to drop really is the last. -/
theorem arcCell_write_last (γP : GName) (d : WData) (n : Nat) (platform : Val) :
    isPlatform (GF := GF) γP .write platform ∗ refAuth d n ∗
      ((refTok d ∗ arcDeposit γP n) ∨ (cellDead d.cell ∗ ⌜n = 0⌝)) ∗ refTok d ⊢
      ⌜n = 1⌝ ∗ isPlatform γP .write platform ∗ refAuth d n ∗ refTok d ∗ refTok d := by
  iintro ⟨Hplat, Hcnt, Hled, Hmine⟩
  icases Hled with (⟨Htok, Hdep⟩ | ⟨-, %hz⟩)
  · ihave #Hpos : ⌜0 < n⌝ $$ [Hcnt Htok]
    · iapply refTok_pos d n
      isplitl [Hcnt] <;> iassumption
    icases Hpos with %hpos
    ihave #Hle : ⌜n < 2⌝ $$ [Hplat Hdep]
    · by_cases hn : 2 ≤ n
      · iexfalso
        icases arcDeposit_read γP n hn $$ Hdep with ⟨%q, Hq⟩
        icases isPlatform_read_guard_valid γP .write platform q $$ [Hplat Hq] with %hcontra
        · isplitl [Hplat] <;> iassumption
        rcases hcontra with ⟨k, hk⟩
        exact absurd hk (by simp)
      · ipureintro; omega
    icases Hle with %hle
    isplit
    · ipureintro; omega
    iframe Hplat Hcnt Htok Hmine
  · subst hz
    iexfalso
    icases refTok_pos d 0 $$ [Hcnt Hmine] with %h
    · isplitl [Hcnt] <;> iassumption
    exact absurd h (Nat.lt_irrefl 0)

/-- Handing out a reference costs a `refTok` and, above the first, half a read
    permit — which the taker can afford, because it is inside a platform read
    critical section. -/
theorem refAuth_take (d : WData) (n : Nat) :
    refAuth (GF := GF) d n ⊢ |==> (refAuth d (n + 1) ∗ refTok d) :=
  refAuth_alloc d n

/-- Giving one back.  `Credit` is cancellable, so the authority really does go
    down. -/
theorem refDeallocUpdate (n : Nat) :
    ((● ((n + 1 : Nat) : Credit) : Auth Credit) • ◯ (1 : Credit)) ~~>
      (● ((n : Nat) : Credit)) := by
  apply Auth.auth_update_dealloc
  have h := cancel_local_update_unit (1 : Credit) ((n : Nat) : Credit)
  have e1 : CMRA.op (1 : Credit) ((n : Nat) : Credit) = ((n + 1 : Nat) : Credit) := by
    show 1 + n = n + 1
    omega
  rw [e1] at h
  exact h

theorem refAuth_give (d : WData) (n : Nat) :
    refAuth (GF := GF) d (n + 1) ∗ refTok d ⊢ |==> refAuth d n := by
  unfold refAuth refTok
  refine .trans (iOwn_op (F := CntRF) (γ := d.cnt)).mpr ?_
  exact iOwn_update (F := CntRF) (γ := d.cnt) (refDeallocUpdate n)

/-- Reassembling the physical half while the platform lock is read-held. -/
theorem arrPhysPart_read (γ : WArrγ) (γp : GName) (platform : Val) (n : Nat)
    (M : H WData) (σ : Arr) :
  ⊢@{IProp GF}
    isPlatform γp (.read (n + 1)) platform -∗ arrShared γ γp M σ -∗
      wStateVar γ.s q3_4 σ M -∗ arrPhysPart γ γp platform := by
  iintro Hplat Hshared Hstate
  unfold arrPhysPart
  iexists (RwLock.State.read (n + 1)), M, σ
  simp only [isPhysical]
  iframe

theorem Arr.isId_lookup (γ : WArrγ) (q : Qp) (M : H WData) (node : Val) (id : Nat) :
    wMetaMap γ.l q M ∗ Arr.isId γ node id ⊢@{IProp GF}
      wMetaMap γ.l q M ∗
      ∃ d : WData,
        ⌜get? M id = some d⌝ ∗ Arr.isNode γ id d ∗ isWeak d.arc node d.mux := by
  unfold Arr.isId
  iintro H
  icases H with ⟨HM, Hid⟩
  icases Hid with ⟨%d, #Hnode, Hweak⟩
  ihave #Hmeta : wMetaAt γ.l id d $$ [Hnode]
  · iunfold Arr.isNode at Hnode
    iexact Hnode
  ihave #Hlookup : ⌜get? M id = some d⌝ $$ [HM Hmeta]
  · iapply wMetaMap_lookup γ.l q M id d $$ HM Hmeta
  icases Hlookup with %hlookup
  isplitl [HM]
  · iexact HM
  · iexists d
    iframe Hweak %hlookup
    iexact Hnode

/-- Run `f` under the platform read lock.  Identical to `Array`'s, except that
    there is no retired-cell view to carry along. -/
theorem execute_shared_spec
    (γ : WArrγ) (γP : GName) (platform f : Val) (Q : Arr → Arr → Val → IProp GF) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    (isArrInv γ γP platform -∗ rwGuard γP .read -∗
       ⟪ ∀ σ, arrFrag γ σ ⟫
         hl(&f #()) @ ↑arrN
       ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r ∗ rwGuard γP .read | RET r ⟫) -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&execute &platform #false &f) @ ↑arrN
    ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r | RET r ⟫ := by
  iintro #Hinv Hf %Φ HAU
  ihave #Hinvraw : inv arrN (arrInvBody γ γP platform) $$ [Hinv]
  · iunfold isArrInv at Hinv
    iexact Hinv
  have Hfull : (↑arrN : CoPset) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  have Hfull' : (↑arrN : CoPset) ⊆ ((⊤ : CoPset) \ (∅ : CoPset)) :=
    fun _ _ => CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.mem_empty⟩
  iapply fupd_wp
  imod inv_acc Hfull $$ Hinvraw with ⟨>HI, Hcl⟩
  iunfold arrInvBody at HI
  icases HI with ⟨Hpart, HP⟩
  iunfold arrPhysPart at HP
  icases HP with ⟨%s0, %M0, %σ0, Hplat, Hphys⟩
  iunfold isPlatform at Hplat
  icases Hplat with ⟨%α, %gate, %cell, Hstrong, Harc, Hlock, Hcell⟩
  ihave #hshape : ⌜∃ ps pw p c : Loc, platform = hl_val(((#ps, #pw), (#p, #c)))⌝ $$ [Harc Hlock]
  · icases Arc.isArc_copyRuntime α platform gate $$ Harc with ⟨⟨%ps, %pw, %hp⟩, -⟩
    icases RwLock.isRwLock_copyRuntime γP gate hl_val(#cell) s0 $$ Hlock with ⟨⟨%p, %hg⟩, -⟩
    ipureintro
    exact ⟨ps, pw, p, cell, by rw [hp, hg]⟩
  ihave HI : arrInvBody γ γP platform $$ [Hpart Hphys Hstrong Harc Hlock Hcell]
  · unfold arrInvBody arrPhysPart isPlatform
    iframe Hpart
    iexists s0, M0, σ0
    isplitl [Hstrong Harc Hlock Hcell]
    · iexists α, gate, cell
      iframe
    · iframe
  imod Hcl $$ HI with -
  imodintro
  icases hshape with ⟨%ps, %pw, %p, %c, %hplat⟩
  subst hplat
  unfold execute Arc.get
  wp_pures
  wp_bind &RwLock.read_acquire _
  iapply RwLock.read_acquire_spec γP hl_val((#p, #c)) hl_val(#c)
  iauintro
  iapply aacc_inv _ _ _ _ Hfull' $$ Hinvraw
  iintro HI
  iunfold arrInvBody at HI
  icases HI with ⟨Hpart, HP⟩
  iunfold arrPhysPart at HP
  icases HP with ⟨%s1, %M1, %σ1, Hplat, Hphys⟩
  iunfold isPlatform at Hplat
  icases Hplat with ⟨%α1, %gate1, %cell1, Hstrong, Harc, Hlock, Hcell⟩
  ihave #hg1 : ⌜gate1 = hl_val((#p, #c)) ∧ cell1 = c⌝ $$ [Harc Hlock]
  · icases Arc.isArc_copyRuntime α1 hl_val(((#ps, #pw), (#p, #c))) gate1 $$ Harc
      with ⟨⟨%u1, %u2, %hu⟩, -⟩
    icases RwLock.isRwLock_copyRuntime γP gate1 hl_val(#cell1) s1 $$ Hlock with ⟨⟨%u3, %hv⟩, -⟩
    ipureintro
    simp only [Val.pair.injEq, Val.lit.injEq] at hu hv
    grind
  icases hg1 with ⟨%hg1a, %hg1b⟩
  subst hg1a
  subst cell1
  ihave Hα : isRwLock γP hl_val((#p, #c)) s1 hl_val(#c) $$ [Hlock]
  · iframe
  iaaccintro' with Hα
  · iintro Hlock
    imodintro
    isplitl [Hpart Hstrong Harc Hlock Hcell Hphys]
    · unfold arrInvBody arrPhysPart isPlatform
      iframe Hpart
      iexists s1, M1, σ1
      isplitl [Hstrong Harc Hlock Hcell]
      · iexists α1, hl_val((#p, #c)), c
        iframe
      · iframe
    · iframe
      isplitl []
      · imodintro; iexact Hinv
      · imodintro; iexact Hinvraw
  · itele_reduce
    iintro Hpost
    icases Hpost with ⟨Hguard, Hcases⟩
    ihave Hres : ∃ m : Nat,
        isRwLock γP hl_val((#p, #c)) (.read (m + 1)) hl_val(#c) ∗
        isPhysical γ γP M1 σ1 (.read (m + 1)) $$ [Hcases Hphys]
    · icases Hcases with (⟨Hlock, %hs⟩ | ⟨%n, Hlock, %hs⟩)
      · subst hs
        iexists 0
        iframe Hlock
        iapply isPhysical_read_acquire_first γ γP M1 σ1
        iexact Hphys
      · subst hs
        iexists n
        iframe Hlock
        iapply isPhysical_read_acquire_more γ γP M1 σ1 n
        iexact Hphys
    icases Hres with ⟨%m, Hlock, Hphys⟩
    imodintro
    isplitl [Hpart Hstrong Harc Hlock Hcell Hphys]
    · unfold arrInvBody arrPhysPart isPlatform
      iframe Hpart
      iexists (RwLock.State.read (m + 1)), M1, σ1
      isplitl [Hstrong Harc Hlock Hcell]
      · iexists α1, hl_val((#p, #c)), c
        iframe
      · iframe
    · itele_reduce
      wp_pures
      wp_bind &f _
      iapply Hf $$ Hinv Hguard
      iauintro
      simp only [atomicAcc]
      iauopen HAU with ⟨%σc, Hfrag, Hclose⟩
      imodintro
      iexists σc
      isplitl [Hfrag]
      · iexact Hfrag
      · isplit
        · iintro Hfrag
          icases Hclose with ⟨Habort, -⟩
          imod Habort $$ Hfrag with HAU
          imodintro
          iframe
          isplitl []
          · imodintro; iexact Hinv
          · imodintro; iexact Hinvraw
        · itele_reduce
          iintro %r Hbeta
          icases Hbeta with ⟨%σ', Hfrag', HQ, Hguard⟩
          icases Hclose with ⟨-, Hcommit⟩
          ihave Hbeta : ∃ σ'', arrFrag γ σ'' ∗ Q σc σ'' r $$ [Hfrag' HQ]
          · iexists σ'
            iframe
          imod Hcommit $$ Hbeta with HΦ
          imodintro
          wp_pures
          wp_bind &RwLock.read_release _
          iapply RwLock.read_release_spec γP hl_val((#p, #c)) hl_val(#c) $$ Hguard
          iauintro
          iapply aacc_inv _ _ _ _ Hfull' $$ Hinvraw
          iintro HI
          iunfold arrInvBody at HI
          icases HI with ⟨Hpart, HP⟩
          iunfold arrPhysPart at HP
          icases HP with ⟨%s2, %M2, %σ2, Hplat, Hphys⟩
          iunfold isPlatform at Hplat
          icases Hplat with ⟨%α2, %gate2, %cell2, Hstrong, Harc, Hlock, Hcell⟩
          ihave #hg2 : ⌜gate2 = hl_val((#p, #c)) ∧ cell2 = c⌝ $$ [Harc Hlock]
          · icases Arc.isArc_copyRuntime α2 hl_val(((#ps, #pw), (#p, #c))) gate2 $$ Harc
              with ⟨⟨%w1, %w2, %hw1⟩, -⟩
            icases RwLock.isRwLock_copyRuntime γP gate2 hl_val(#cell2) s2 $$ Hlock
              with ⟨⟨%w3, %hw2⟩, -⟩
            ipureintro
            simp only [Val.pair.injEq, Val.lit.injEq] at hw1 hw2
            grind
          icases hg2 with ⟨%hg2a, %hg2b⟩
          subst hg2a
          subst cell2
          ihave Hα : isRwLock γP hl_val((#p, #c)) s2 hl_val(#c) $$ [Hlock]
          · iframe
          iaaccintro' with Hα
          · iintro Hlock
            imodintro
            isplitl [Hpart Hstrong Harc Hlock Hcell Hphys]
            · unfold arrInvBody arrPhysPart isPlatform
              iframe Hpart
              iexists s2, M2, σ2
              isplitl [Hstrong Harc Hlock Hcell]
              · iexists α2, hl_val((#p, #c)), c
                iframe
              · iframe
            · iframe
              isplitl []
              · imodintro; iexact Hinv
              · imodintro; iexact Hinvraw
          · itele_reduce
            iintro %k Hpost
            icases Hpost with ⟨%hs2, Hcases⟩
            subst hs2
            ihave Hres : ∃ s' : RwLock.State,
                isRwLock γP hl_val((#p, #c)) s' hl_val(#c) ∗
                isPhysical γ γP M2 σ2 s' $$ [Hcases Hphys]
            · icases Hcases with (⟨Hlock, %hk⟩ | ⟨Hlock, %hk⟩)
              · subst hk
                iexists RwLock.State.free
                ihave Hres := isPhysical_read_release_last γ γP M2 σ2
                  hl_val((#p, #c)) hl_val(#c) $$ Hphys Hlock
                icases Hres with ⟨Hphys, Hlock⟩
                iframe
              · iexists (RwLock.State.read k)
                iframe Hlock
                iapply isPhysical_read_release_nonlast γ γP M2 σ2 k
                iexact Hphys
            icases Hres with ⟨%s', Hlock, Hphys⟩
            imodintro
            isplitl [Hpart Hstrong Harc Hlock Hcell Hphys]
            · unfold arrInvBody arrPhysPart isPlatform
              iframe Hpart
              iexists s', M2, σ2
              isplitl [Hstrong Harc Hlock Hcell]
              · iexists α2, hl_val((#p, #c)), c
                iframe
              · iframe
            · itele_reduce
              wp_pures
              iexact HΦ

/-- Run `f` under the platform write lock.  The body is an ordinary Hoare triple on
    `arrContent`: it has the whole list to itself. -/
theorem execute_exclusive_spec
    (γ : WArrγ) (γP : GName) (platform f : Val) (Q : Arr → Arr → Val → IProp GF) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    (∀ σ,
       ⦃ arrContent γ σ ⦄
         hl(&f #())
       ⦃ r, RET r; ∃ σ', arrContent γ σ' ∗ Q σ σ' r ⦄) -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&execute &platform #true &f) @ ↑arrN
    ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r | RET r ⟫ := by
  sorry

/-- Splice a cell in after `node`.

    The handle is weak, so the return value can in principle be `none` because the
    cell was freed rather than because it was never there — but those are the same
    thing: a cell leaves the list exactly by being freed.  So the postcondition is
    still indexed by `Arr.insert` alone, with no extra failure case. -/
theorem insert_spec
    (γ : WArrγ) (γp : GName) (platform node : Val) (id : Nat) (x : Int) :
  ⊢@{IProp GF}
    isArrInv γ γp platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&insert &platform &node #x) @ ↑arrN
    ⟪ ∃ ret,
        arrFrag γ (Arr.insert σ id x).1 ∗
        Arr.isId γ node id ∗
        match (Arr.insert σ id x).2 with
        | none => iprop% ⌜ret = hl_val(none())⌝
        | some nid => iprop%
            ∃ newNode : Val,
              ⌜ret = hl_val(some(&newNode))⌝ ∗
              Arr.isId γ newNode nid
      | RET ret
    ⟫ := by
  sorry

/-- Detach and free everything strictly after `node`.

    Unlike `Array`'s, this postcondition says nothing about surviving cells, because
    there are none: the handles a client holds on the revoked suffix all go stale. -/
theorem revoke_spec
    (γ : WArrγ) (γp : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv γ γp platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&revoke &platform &node) @ ↑arrN
    ⟪ arrFrag γ (Arr.revoke σ id).1 ∗ Arr.isId γ node id
      | RET match (Arr.revoke σ id).2 with
            | none => hl_val(none())
            | some _ => hl_val(some(#()))
    ⟫ := by
  sorry

/-- A handle on the successor.  Reading the list does not move it, so `σ` is
    unchanged and the result is read off `σ.cells` directly. -/
theorem getChild_spec
    (γ : WArrγ) (γp : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv γ γp platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&getChild &platform &node) @ ↑arrN
    ⟪ ∃ ret,
        arrFrag γ σ ∗ Arr.isId γ node id ∗
        (⌜ret = hl_val(none())⌝ ∨
         ∃ (w : Val) (cid : Nat),
           ⌜ret = hl_val(some(&w))⌝ ∗ Arr.isId γ w cid)
      | RET ret ⟫ := by
  sorry

/-- Duplicating a handle: no platform lock, because the reference counts are not
    under it.  This is what `Array` cannot offer — there `arcAuth` lives under the
    platform lock and vanishes entirely while a writer holds it. -/
theorem isId_clone_spec (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    ⦃ Arr.isId γ node id ⦄
      hl(&cloneHandle &node)
    ⦃ w, RET w;
      ⌜w = node⌝ ∗ Arr.isId γ node id ∗ Arr.isId γ w id ⦄ := by
  iintro #Hinv %Φ Hid HΦ
  iunfold Arr.isId at Hid
  icases Hid with ⟨%d, #Hnode, Hweak⟩
  unfold cloneHandle
  wp_pures
  iapply Weak.clone_spec (γ := d.arc) node d.mux $$ Hweak
  iunfold isArrInv at Hinv
  iauintro
  iinv Hinv as Hbody
  iunfold arrInvBody at Hbody
  icases Hbody with ⟨Hpart, Hphys⟩
  icases arcPart_acc γ γP id d $$ Hpart Hnode with ⟨Hcell, Hback⟩
  iunfold arcCell at Hcell
  icases Hcell with ⟨%n, %m, Hauth, Hcnt, Hled⟩
  iaaccintro' with Hauth
  · iintro Hauth
    imodintro
    isplitl [Hauth Hcnt Hled Hback Hphys]
    · iapply arrInvBody_intro γ γP platform $$ [Hback Hauth Hcnt Hled] Hphys
      iapply Hback
      unfold arcCell
      iexists n, m
      iframe
    · iframe
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro ⟨Hauth, Hw1, Hw2⟩
    imodintro
    isplitl [Hauth Hcnt Hled Hback Hphys]
    · iapply arrInvBody_intro γ γP platform $$ [Hback Hauth Hcnt Hled] Hphys
      iapply Hback
      unfold arcCell
      iexists n, (m + 1)
      iframe
    · iapply HΦ
      isplitl []
      · itrivial
      isplitl [Hw1]
      · unfold Arr.isId
        iexists d
        iframe Hw1
        iexact Hnode
      · unfold Arr.isId
        iexists d
        iframe Hw2
        iexact Hnode

end Atomic

end Specs

end Iris.Examples.HeapLang.WeakList
