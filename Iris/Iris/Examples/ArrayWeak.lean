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

omit [RwLockG GF] [ArcG GF] [WArrG GF H] in
/-- A generic split of the live witness, so the chain and the ledger can hold
    complementary shares of it. -/
theorem cellAlive_split_gen (γ : GName) (q₁ q₂ : Qp) (n : Option Nat) :
    cellAlive (GF := GF) γ (q₁ + q₂) n ⊣⊢ cellAlive γ q₁ n ∗ cellAlive γ q₂ n := by
  unfold cellAlive
  have h : (FracAgree.mk (DFrac.own (q₁ + q₂)) (Cell.alive n) : DFracAgreeR Cell)
      = FracAgree.mk (DFrac.own q₁) (Cell.alive n)
        • FracAgree.mk (DFrac.own q₂) (Cell.alive n) := by
    rw [show DFrac.own (q₁ + q₂) = DFrac.own q₁ • DFrac.own q₂ from rfl]
    exact FracAgree.mk_op.to_eq
  rw [h]
  exact iOwn_op (F := CellRF)

theorem q1_4_add_q1_2 : q1_4 + q1_2 = q3_4 := by
  apply Subtype.ext
  show (q1_4 : Qp).val + (q1_2 : Qp).val = (q3_4 : Qp).val
  simp [q1_4, q1_2, q3_4, Qp.half]
  grind

omit [RwLockG GF] [ArcG GF] [WArrG GF H] in
/-- Two shares of the live witness cannot exceed the whole.  This is the arithmetic
    behind the exclusive-mode receipt: a thread holding the chain's `3/4` refutes a
    ledger claiming `1/2`. -/
theorem cellAlive_frac_valid (γ : GName) (q₁ q₂ : Qp) (n₁ n₂ : Option Nat) :
    cellAlive (GF := GF) γ q₁ n₁ ∗ cellAlive γ q₂ n₂ ⊢ ⌜(q₁ + q₂).val ≤ 1⌝ := by
  unfold cellAlive
  iintro ⟨H₁, H₂⟩
  ihave H := iOwn_cmraValid_op $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete $$ H with %Hvalid
  ipureintro
  have h := (FracAgree.op_valid_L.mp Hvalid).1
  have he : (DFrac.own q₁ • DFrac.own q₂) = DFrac.own (q₁ + q₂) := rfl
  rw [he] at h
  exact DFrac.valid_own.mp h

/-- Full ownership of the live witness excludes any other share.  This is what makes
    the exclusive-mode deposit below work: a writer holding the chain owns `1` of
    every live cell, so a ledger claiming a quarter of one is a contradiction. -/
theorem cellAlive_full_excl (γ : GName) (q : Qp) (n₁ n₂ : Option Nat) :
    cellAlive (GF := GF) γ 1 n₁ ∗ cellAlive γ q n₂ ⊢ False := by
  unfold cellAlive
  iintro ⟨H₁, H₂⟩
  ihave H := iOwn_cmraValid_op $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete $$ H with %Hvalid
  iexfalso
  ipureintro
  have hd := (FracAgree.op_valid_L.mp Hvalid).1
  have hq := q.2
  have hone : (1 : Qp).val = 1 := rfl
  have := DFrac.valid_own_op hd
  grind

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
    `cellDead` records that, so a stale weak handle can be shown to fail to upgrade.

    The middle case is the *exclusive-mode* borrow, and it exists because `revoke`
    upgrades a handle while holding the platform for writing, where a read-permit
    deposit is impossible.  What it leaves instead is a quarter of the cell's live
    witness — which only a thread holding the whole chain can afford, and which is
    therefore unavailable for any *other* cell, since that thread still owns `1` of
    each.  That is exactly the discrimination the read-permit deposit cannot make: it
    says not merely "somebody is writing" but "somebody is writing *this* cell". -/
def arcCell (γP : GName) (d : WData) : IProp GF := iprop%
  ∃ n m : Nat, arcAuth d.arc n m ∗ refAuth d n ∗
    ((refTok d ∗ arcDeposit γP n ∗ ∃ nxt : Option Nat, cellAlive d.cell q1_4 nxt)
     ∨ (refTok d ∗ ⌜n = 2⌝ ∗ (∃ nxt : Option Nat, cellAlive d.cell q1_2 nxt) ∗
          rwGuardFrac γP RwLock.Mode.write q1_2)
     ∨ (cellDead d.cell ∗ ⌜n = 0⌝))

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
  isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗ C q3_4 ∗ P

/-- The same under a platform read lock, where another reader may be part-way
    through a write on this cell.  The `rwGuardFrac` it leaves behind is what proves
    the list is quiescent again once the platform lock is released. -/
def nodeSlotSharedBody (γP : GName) (C : Qp → IProp GF) (P : IProp GF) :
    RwLock.State → IProp GF
  | .write  => iprop% rwGuardFrac γP RwLock.Mode.read q1_4 ∗ C q1_4
  | .read _ => iprop% False
  | .free   => iprop% P ∗ C q3_4

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
        cellAlive d.cell q3_4 nxt ∗
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
  ihave Hcell : cellAlive γcell (q1_4 + q3_4) nxt $$ [Hcell]
  · rw [q1_4_add_q3_4]
    iexact Hcell
  icases (cellAlive_split_gen γcell q1_4 q3_4 nxt).mp $$ Hcell with ⟨Hq4, Hcell⟩
  ihave Hbody : arcCell γP ⟨⟨γarc, γrw, γcell, l, p, x⟩, γcnt⟩ $$ [Hauth Hcnt Htok Hq4]
  · unfold arcCell refAuth refTok
    iexists 1, 0
    iframe Hauth Hcnt
    ileft
    iframe Htok
    isplitl []
    · unfold arcDeposit
      itrivial
    · iexists nxt
      iexact Hq4
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
      iapply cellAlive_dead_False d.cell q3_4 nxt
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
    iapply cellAlive_dead_False d.cell q3_4 nxt
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

/-- The write permit identifies the lock state, which is what lets the body of an
    exclusive `execute` reason about the ledger: `arcCell_write_last` needs to know
    the platform really is write-held, and the permit is the only evidence of that
    which survives being handed to a client-supplied function. -/
theorem isPlatform_write_guard_valid (ρ : GName) (s : RwLock.State) (platform : Val) :
    isPlatform (GF := GF) ρ s platform ∗ rwGuard ρ RwLock.Mode.write ⊢ ⌜s = .write⌝ := by
  unfold isPlatform
  iintro H
  icases H with ⟨Hplatform, Hguard⟩
  icases Hplatform with ⟨%α, %gate, %cell, Harc, Hhandle, Hlock, Hcell⟩
  ihave #Hcompat : ⌜RwLock.GuardCompatible s .write⌝ $$ [Hlock Hguard]
  · iapply RwLock.rwGuard_valid
    isplitl [Hlock] <;> iassumption
  icases Hcompat with %Hvalid
  ipureintro
  cases Hvalid
  rfl

theorem rwGuard_toFrac (γ : GName) :
    ⊢@{IProp GF} rwGuard γ RwLock.Mode.read -∗ rwGuardFrac γ RwLock.Mode.read 1 := by
  iintro H
  rw [← rwGuard_eq γ RwLock.Mode.read]
  iexact H

/-! ### Working the ledger

These are where the design pays off.  Each turns a fact about a *lock* into a fact
about a *reference count*, or the other way round.  They are stated on the unpacked
ledger so that a caller which has just opened `arcCell` can use them without
repacking.

The ledger holds a quarter of the cell's live witness while the cell is in the list.
That quarter does three jobs at once: it makes the tombstone case *decidable* from
`cellDead` alone, it is what the exclusive-mode borrower hands over as a receipt, and
it is the piece a revocation needs in order to reach full ownership and retire the
cell. -/

abbrev arcAliveTok (d : WData) (q : Qp) : IProp GF := iprop%
  ∃ nxt : Option Nat, cellAlive d.cell q nxt

abbrev arcLedger (γP : GName) (d : WData) (n : Nat) : IProp GF := iprop%
  (refTok d ∗ arcDeposit γP n ∗ arcAliveTok d q1_4)
  ∨ (refTok d ∗ ⌜n = 2⌝ ∗ arcAliveTok d q1_2 ∗ rwGuardFrac γP RwLock.Mode.write q1_2)
  ∨ (cellDead d.cell ∗ ⌜n = 0⌝)

theorem arcCell_unpack (γP : GName) (d : WData) :
    arcCell (GF := GF) γP d ⊢
      ∃ n m : Nat, arcAuth d.arc n m ∗ refAuth d n ∗ arcLedger γP d n := by
  unfold arcCell arcLedger arcAliveTok
  iintro H
  iexact H

theorem arcCell_pack (γP : GName) (d : WData) (n m : Nat) :
    arcAuth (GF := GF) d.arc n m ∗ refAuth d n ∗ arcLedger γP d n ⊢ arcCell γP d := by
  unfold arcCell arcLedger arcAliveTok
  iintro ⟨H₁, H₂, H₃⟩
  iexists n, m
  iframe

/-- **Gap 1.**  A cell that is still in the list has a positive count, so a weak
    handle on it upgrades successfully — and, read the other way, a cell that has
    been retired has count zero, so a stale handle provably fails.

    The retired direction is the one that matters: it is what turns `deadNodes`, a
    fact about the *abstract* list, into a fact about the *physical* counter. -/
theorem arcLedger_dead_zero (γP : GName) (d : WData) (n : Nat) :
    cellDead (GF := GF) d.cell ∗ arcLedger γP d n ⊢ ⌜n = 0⌝ ∗ arcLedger γP d n := by
  unfold arcLedger arcAliveTok
  iintro ⟨#Hcd, Hled⟩
  icases Hled with (⟨Htok, Hdep, %nxt, Hq⟩ | ⟨-, -, ⟨%nxt, Hq⟩, -⟩ | ⟨-, %hz⟩)
  · iexfalso
    iapply cellAlive_dead_False d.cell q1_4 nxt
    isplitl [Hq] <;> iassumption
  · iexfalso
    iapply cellAlive_dead_False d.cell q1_2 nxt
    isplitl [Hq] <;> iassumption
  · isplit
    · ipureintro; exact hz
    iright; iright
    isplitl []
    · iexact Hcd
    · ipureintro; exact hz

/-- **Gap 2.**  A thread that has upgraded a weak handle holds a `refTok` of its own,
    so the ledger's copy proves the count is at least two and its own drop is not the
    last one. -/
theorem arcCell_two (γP : GName) (d : WData) (n : Nat) :
    refAuth (GF := GF) d n ∗ arcLedger γP d n ∗ refTok d ⊢
      ⌜2 ≤ n⌝ ∗ refAuth d n ∗ arcLedger γP d n ∗ refTok d := by
  unfold arcLedger
  iintro ⟨Hcnt, Hled, Hmine⟩
  icases Hled with (⟨Htok, Hrest⟩ | ⟨Htok, %hn, Hrest⟩ | ⟨-, %hz⟩)
  · ihave #Hge : ⌜2 ≤ n⌝ $$ [Hcnt Htok Hmine]
    · iapply refTok_two d n
      isplitl [Hcnt]
      · iassumption
      isplitl [Htok] <;> iassumption
    iframe Hge Hcnt Hmine
    ileft
    iframe
  · iframe Hcnt Hmine
    isplit
    · ipureintro; omega
    iright; ileft
    iframe Htok Hrest
    ipureintro; exact hn
  · subst hz
    iexfalso
    icases refTok_pos d 0 $$ [Hcnt Hmine] with %h
    · isplitl [Hcnt] <;> iassumption
    exact absurd h (Nat.lt_irrefl 0)

/-- **Gap 3**, the one `Array` never closes.

    A thread holding the chain owns `3/4` of every live cell's witness, and the
    platform being write-held means no read permit exists anywhere.  Between them the
    two deposits are excluded, so the count is at most one: the reference revocation
    is about to drop really is the last, and the cell really is freed. -/
theorem arcCell_write_last (γP : GName) (d : WData) (n : Nat) (platform : Val)
    (nxt : Option Nat) :
    isPlatform (GF := GF) γP .write platform ∗ refAuth d n ∗ arcLedger γP d n ∗
      cellAlive d.cell q3_4 nxt ⊢
      ⌜n ≤ 1⌝ ∗ isPlatform γP .write platform ∗ refAuth d n ∗ arcLedger γP d n ∗
        cellAlive d.cell q3_4 nxt := by
  unfold arcLedger arcAliveTok
  iintro ⟨Hplat, Hcnt, Hled, Halive⟩
  icases Hled with (⟨Htok, Hdep, Hq⟩ | ⟨-, %hn, ⟨%nxt', Hq⟩, -⟩ | ⟨#Hcd, %hz⟩)
  · ihave #Hle : ⌜n ≤ 1⌝ $$ [Hplat Hdep]
    · by_cases hn : 2 ≤ n
      · iexfalso
        icases arcDeposit_read γP n hn $$ Hdep with ⟨%q, Hq'⟩
        icases isPlatform_read_guard_valid γP .write platform q $$ [Hplat Hq'] with %hcontra
        · isplitl [Hplat] <;> iassumption
        rcases hcontra with ⟨k, hk⟩
        exact absurd hk (by simp)
      · ipureintro; omega
    iframe Hle Hplat Hcnt Halive
    ileft
    iframe
  · iexfalso
    icases cellAlive_frac_valid d.cell q3_4 q1_2 nxt nxt' $$ [Halive Hq] with %hv
    · isplitl [Halive] <;> iassumption
    ipureintro
    have h34 : (q3_4 : Qp).val = 3/4 := by simp [q3_4, Qp.half]; grind
    have h12 : (q1_2 : Qp).val = 1/2 := by simp [q1_2, Qp.half]
    rw [Qp.val_add, h34, h12] at hv
    grind
  · subst hz
    iframe Hplat Hcnt Halive
    isplit
    · ipureintro; omega
    iright; iright
    isplitl []
    · iexact Hcd
    · ipureintro; rfl

/-- A reader inside a platform read critical section can rule out the exclusive-mode
    borrow: it needs the platform write-held, and a read permit says otherwise. -/
theorem arcLedger_no_write_borrow (γP : GName) (d : WData) (n : Nat)
    (s : RwLock.State) (platform : Val) (q : Qp) :
    isPlatform (GF := GF) γP s platform ∗ rwGuardFrac γP RwLock.Mode.read q ∗
      arcLedger γP d n ⊢
      isPlatform γP s platform ∗ rwGuardFrac γP RwLock.Mode.read q ∗
      ((refTok d ∗ arcDeposit γP n ∗ arcAliveTok d q1_4) ∨ (cellDead d.cell ∗ ⌜n = 0⌝)) := by
  unfold arcLedger isPlatform
  iintro ⟨Hplat, Hread, Hled⟩
  icases Hled with (Hleft | ⟨-, -, -, Hwrite⟩ | Hright)
  · iframe Hplat Hread
    ileft; iexact Hleft
  · iexfalso
    icases Hplat with ⟨%α, %gate, %cell, -, -, Hlock, -⟩
    ihave #Hr : ⌜RwLock.GuardCompatible s .read⌝ $$ [Hlock Hread]
    · iapply RwLock.rwGuardFrac_valid _ _ _ _ _ q
      isplitl [Hlock] <;> iassumption
    ihave #Hw : ⌜RwLock.GuardCompatible s .write⌝ $$ [Hlock Hwrite]
    · iapply RwLock.rwGuardFrac_valid _ _ _ _ _ q1_2
      isplitl [Hlock] <;> iassumption
    icases Hr with %hr
    icases Hw with %hw
    ipureintro
    cases hr
    cases hw
  · iframe Hplat Hread
    iright; iexact Hright

/-- Handing out a reference costs a `refTok` and, above the first, half a read
    permit — which the taker can afford, because it is inside a platform read
    critical section. -/
theorem refAuth_take (d : WData) (n : Nat) :
    refAuth (GF := GF) d n ⊢ |==> (refAuth d (n + 1) ∗ refTok d) :=
  refAuth_alloc d n

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

/-- Giving one back.  `Credit` is cancellable, so the authority really does go
    down. -/
theorem refAuth_give (d : WData) (n : Nat) :
    refAuth (GF := GF) d (n + 1) ∗ refTok d ⊢ |==> refAuth d n := by
  unfold refAuth refTok
  refine .trans (iOwn_op (F := CntRF) (γ := d.cnt)).mpr ?_
  exact iOwn_update (F := CntRF) (γ := d.cnt) (refDeallocUpdate n)

/-- Retiring a cell's ledger: the count is zero for good, and the tombstone is
    persistent, so a stale weak handle can still be shown to fail. -/
theorem arcLedger_kill (γP : GName) (d : WData) (nxt : Option Nat) :
    refAuth (GF := GF) d 1 ∗ arcLedger γP d 1 ∗ cellAlive d.cell 1 nxt ⊢
      |==> (refAuth d 0 ∗ arcLedger γP d 0 ∗ cellDead d.cell) := by
  unfold arcLedger
  iintro ⟨Hcnt, Hled, Halive⟩
  icases Hled with (⟨Htok, -⟩ | ⟨-, %hn, -, -⟩ | ⟨-, %hz⟩)
  · imod refAuth_give d 0 $$ [Hcnt Htok] with Hcnt
    · isplitl [Hcnt] <;> iassumption
    imod cellAlive_full_kill d.cell nxt $$ Halive with #Hcd
    imodintro
    iframe Hcnt
    isplitl []
    · iright; iright
      isplitl []
      · iexact Hcd
      ipureintro; rfl
    · iexact Hcd
  · exact absurd hn (by simp)
  · exact absurd hz (by simp)

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

/-- Run `f` under the platform read lock.

    The read permit is *not* part of `f`'s atomic postcondition; it is the separate,
    non-atomic `POST`.  That is forced by the deposit: at `f`'s linearisation point
    half the permit is still sitting in a cell's ledger, backing a strong reference
    that has not been dropped yet, so `f` simply does not have the whole permit to
    hand over there.  It gets it back once the borrow is returned, which is strictly
    after the linearisation point.

    `Array` never notices this, because it has no deposit: its only parked fraction
    belongs to a locked cell and comes back at exactly the release which *is* its
    linearisation point.  The deposit is the price of keeping reference counts
    outside the platform lock, and this is where that price is paid. -/
theorem execute_shared_spec
    (γ : WArrγ) (γP : GName) (platform f : Val) (Q : Arr → Arr → Val → IProp GF) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    (isArrInv γ γP platform -∗ rwGuard γP .read -∗
       ⟪ ∀ σ, arrFrag γ σ ⟫
         hl(&f #()) @ ↑arrN
       ⟪ ∃ r, (∃ σ', arrFrag γ σ' ∗ Q σ σ' r)
         | z, RET z; rwGuard γP RwLock.Mode.read ∗ ⌜z = r⌝ ⟫) -∗
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
          icases Hbeta with ⟨%σ', Hfrag', HQ⟩
          icases Hclose with ⟨-, Hcommit⟩
          ihave Hbeta : ∃ σ'', arrFrag γ σ'' ∗ Q σc σ'' r $$ [Hfrag' HQ]
          · iexists σ'
            iframe
          imod Hcommit $$ Hbeta with HΦ
          imodintro
          iintro %z
          simp only [wandM]
          iintro ⟨Hguard, %hz⟩
          subst hz
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
    `arrContent`: it has the whole list to itself.

    The write permit is *lent* to `f` and taken back.  `execute` holds it only across
    `f`'s execution anyway, so this costs nothing, and it is what lets `f` prove the
    platform is write-held — which the reference-count ledger needs. -/
theorem execute_exclusive_spec
    (γ : WArrγ) (γP : GName) (platform f : Val) (Q : Arr → Arr → Val → IProp GF) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    (∀ σ,
       ⦃ arrContent γ σ ∗ rwGuard γP RwLock.Mode.write ⦄
         hl(&f #())
       ⦃ r, RET r;
         ∃ σ', arrContent γ σ' ∗ rwGuard γP RwLock.Mode.write ∗ Q σ σ' r ⦄) -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&execute &platform #true &f) @ ↑arrN
    ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r | RET r ⟫ := by
  iintro #Hinv Hf %Φ HAU
  iunfold isArrInv at Hinv
  have Hfull : (↑arrN : CoPset) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  have Hfull' : (↑arrN : CoPset) ⊆ ((⊤ : CoPset) \ (∅ : CoPset)) :=
    fun _ _ => CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.mem_empty⟩
  iapply fupd_wp
  imod inv_acc Hfull $$ Hinv with ⟨>HI, Hcl⟩
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
  wp_bind &RwLock.write_acquire _
  iapply RwLock.write_acquire_spec γP hl_val((#p, #c)) hl_val(#c)
  iauintro
  iapply aacc_inv _ _ _ _ Hfull' $$ Hinv
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
      imodintro
      iexact Hinv
  · itele_reduce
    iintro Hpost
    icases Hpost with ⟨Hlock, Hguard, %hs1⟩
    subst hs1
    imodintro
    icases isPhysical_write_acquire γ γP M1 σ1 $$ Hphys with ⟨⟨Hcontent, Hout⟩, Hphys⟩
    isplitl [Hpart Hstrong Harc Hlock Hcell Hphys]
    · unfold arrInvBody arrPhysPart isPlatform
      iframe Hpart
      iexists RwLock.State.write, M1, σ1
      isplitl [Hstrong Harc Hlock Hcell]
      · iexists α1, hl_val((#p, #c)), c
        iframe
      · iframe
    · itele_reduce
      wp_pures
      wp_bind &f _
      ihave Hcontent : arrContent γ σ1 $$ [Hcontent]
      · unfold arrContent
        iexists M1
        iexact Hcontent
      iapply Hf $$ [Hcontent Hguard]
      · iframe
      iintro %r !> Hres
      icases Hres with ⟨%σ2, Hcontent2, Hguard, HQ⟩
      iunfold arrContent at Hcontent2
      icases Hcontent2 with ⟨%M2, Hcontent2⟩
      wp_pures
      wp_bind &RwLock.write_release _
      iapply RwLock.write_release_spec γP hl_val((#p, #c)) hl_val(#c) $$ Hguard
      iauintro
      iapply aacc_inv _ _ _ _ Hfull' $$ Hinv
      iintro HI
      iunfold arrInvBody at HI
      icases HI with ⟨Hpart, HP⟩
      iunfold arrPhysPart at HP
      icases HP with ⟨%s3, %M3, %σ3, Hplat, Hphys⟩
      ihave #hw : ⌜s3 = .write⌝ $$ [Hphys Hout]
      · iapply isPhysical_write_pinned γ γP M3 M1 σ3 σ1 s3
        isplitl [Hphys] <;> iassumption
      icases hw with %hw
      subst hw
      iunfold isPlatform at Hplat
      icases Hplat with ⟨%α3, %gate3, %cell3, Hstrong, Harc, Hlock, Hcell⟩
      ihave #hg3 : ⌜gate3 = hl_val((#p, #c)) ∧ cell3 = c⌝ $$ [Harc Hlock]
      · icases Arc.isArc_copyRuntime α3 hl_val(((#ps, #pw), (#p, #c))) gate3 $$ Harc
          with ⟨⟨%v1, %v2, %hv1⟩, -⟩
        icases RwLock.isRwLock_copyRuntime γP gate3 hl_val(#cell3) .write $$ Hlock
          with ⟨⟨%v3, %hv2⟩, -⟩
        ipureintro
        simp only [Val.pair.injEq, Val.lit.injEq] at hv1 hv2
        grind
      icases hg3 with ⟨%hg3a, %hg3b⟩
      subst hg3a
      subst cell3
      ihave Hα : isRwLock γP hl_val((#p, #c)) .write hl_val(#c) $$ [Hlock]
      · iframe
      iaaccintro' with Hα
      · iintro Hlock
        imodintro
        isplitl [Hpart Hstrong Harc Hlock Hcell Hphys]
        · unfold arrInvBody arrPhysPart isPlatform
          iframe Hpart
          iexists RwLock.State.write, M3, σ3
          isplitl [Hstrong Harc Hlock Hcell]
          · iexists α3, hl_val((#p, #c)), c
            iframe
          · iframe
        · iframe
          imodintro
          iexact Hinv
      · itele_reduce
        iintro Hlock
        iauopen HAU with ⟨%σc, Hfrag, Hclose⟩
        ihave #hac : ⌜σc = σ1⌝ $$ [Hfrag Hout]
        · iapply arrFrag_agree γ σc σ1 M1
          isplitl [Hfrag] <;> iassumption
        icases hac with %hac
        subst hac
        ihave Hupd := isPhysical_write_release γ γP M1 M2 σc σ2 $$ Hcontent2 Hout Hfrag
        imod Hupd with ⟨Hphys', Hfrag'⟩
        icases Hclose with ⟨-, Hcommit⟩
        ihave Hbeta : ∃ σ', arrFrag γ σ' ∗ Q σc σ' r $$ [Hfrag' HQ]
        · iexists σ2
          iframe
        imod Hcommit $$ Hbeta with HΦ
        imodintro
        isplitl [Hpart Hstrong Harc Hlock Hcell Hphys']
        · unfold arrInvBody arrPhysPart isPlatform
          iframe Hpart
          iexists RwLock.State.free, M2, σ2
          isplitl [Hstrong Harc Hlock Hcell]
          · iexists α3, hl_val((#p, #c)), c
            iframe
          · iframe
        · itele_reduce
          wp_pures
          iexact HΦ

/-- The successor of `id` in the abstract list, if any.  Matches what the chain
    records, so a `getChild` can be specified against `σ` alone. -/
def Arr.succOf : List (Nat × Int) → Nat → Option Nat
  | [], _ => none
  | (id', _) :: cs, id => if id' = id then nextIdOr cs none else Arr.succOf cs id

/-- The chain accessor, with the successor pinned down rather than existential. -/
theorem isGhostHelpAccSucc (γ : GName) (d : WData) (slot : Slot (H := H) GF)
    (id : Nat) :
    ∀ cells : List (Nat × Int), id ∈ cells.map (·.1) →
    wMetaAt γ id d ⊢@{IProp GF} isGhostHelp slot γ none cells -∗
      aliveSlot slot γ d (Arr.succOf cells id) ∗
      (aliveSlot slot γ d (Arr.succOf cells id) -∗ isGhostHelp slot γ none cells) := by
  intro cells
  induction cells with
  | nil => intro h; exact absurd h (by simp)
  | cons c cells ih =>
    rcases c with ⟨id', x⟩
    intro hin
    iintro #Hmeta Hlist
    simp only [isGhostHelp, Arr.succOf]
    icases Hlist with ⟨%d', %hval, #Hmeta', Hslot, Hrest⟩
    by_cases hhead : id' = id
    · subst hhead
      ihave %hd := wMetaAt_agree $$ Hmeta' Hmeta
      subst hd
      rw [if_pos rfl]
      iframe Hslot
      iintro Hslot
      iexists d'
      iframe Hmeta' Hslot Hrest
      ipureintro
      exact hval
    · rw [if_neg hhead]
      have hin' : id ∈ cells.map (·.1) := by
        simp only [List.map_cons, List.mem_cons] at hin
        rcases hin with h | h
        · exact absurd h.symm hhead
        · exact h
      ihave Hacc := ih hin' $$ Hmeta Hrest
      icases Hacc with ⟨Hslot', Hback⟩
      iframe Hslot'
      iintro Hslot'
      ihave Hrest' := Hback $$ Hslot'
      iexists d'
      iframe Hmeta' Hslot Hrest'
      ipureintro
      exact hval

/-- Holding a strong reference proves the cell is still in the abstract list.

    This is the direction that needs the ledger's share of the live witness: without
    it, "the cell has been retired" and "the counter is positive" would be
    independent facts and the two views could drift apart. -/
theorem isArc_mem (γ : WArrγ) (γP : GName) (M : H WData) (σ : Arr) (node : Val)
    (id : Nat) (d : WData) (hlookup : get? M id = some d) :
  ⊢@{IProp GF}
    arcPart γ γP -∗ Arr.isNode γ id d -∗ deadNodes M σ.cells -∗
    isArc d.arc node d.mux -∗
      ⌜id ∈ σ.cells.map (·.1)⌝ ∗ arcPart γ γP ∗ isArc d.arc node d.mux := by
  iintro Hpart #Hnode #Hdead Harc
  by_cases hin : id ∈ σ.cells.map (·.1)
  · iframe Hpart Harc
    ipureintro; exact hin
  · iexfalso
    ihave #Hcd : cellDead d.cell $$ [Hdead]
    · iapply deadNodes_lookup M σ.cells id d hlookup hin
      iexact Hdead
    icases arcPart_acc γ γP id d $$ Hpart Hnode with ⟨Hcell, -⟩
    icases arcCell_unpack γP d $$ Hcell with ⟨%n, %m, Hauth, -, Hled⟩
    icases arcLedger_dead_zero γP d n $$ [Hcd Hled] with ⟨%hz, -⟩
    · isplitl [] <;> iassumption
    subst hz
    icases Arc.arcAuth_isArc_valid (γ := d.arc) 0 m node d.mux $$ [Hauth Harc] with %h
    · isplitl [Hauth] <;> iassumption
    exact absurd h (Nat.lt_irrefl 0)

/-- Open the invariant body under a platform read lock.

    A quarter of the read permit is enough to pin the lock state, which is what makes
    the shared view available; it is handed straight back, so this costs nothing.
    Both `insert` and `revoke` do this repeatedly, so it is worth naming. -/
theorem arrInvOpenRead (γ : WArrγ) (γP : GName) (platform : Val) :
  ⊢@{IProp GF}
    arrInvBody γ γP platform -∗ rwGuardFrac γP RwLock.Mode.read q1_4 -∗
      ∃ (np : Nat) (M : H WData) (σ : Arr),
        ⌜σ.wellFormed⌝ ∗ ⌜∀ i, dom M i ↔ i < σ.counter⌝ ∗
        arcPart γ γP ∗ isPlatform γP (.read (np + 1)) platform ∗
        wMetaMap γ.l q1_2 M ∗ deadNodes M σ.cells ∗
        isGhost (nodeSlotShared γP) γ.l σ.cells ∗ wStateVar γ.s q3_4 σ M ∗
        rwGuardFrac γP RwLock.Mode.read q1_4 := by
  iintro HI Hkeep
  iunfold arrInvBody at HI
  icases HI with ⟨Hpart, Hphys⟩
  iunfold arrPhysPart at Hphys
  icases Hphys with ⟨%s, %M, %σ, Hplat, Hrest⟩
  icases isPlatform_read_guard_valid γP s platform q1_4 $$ [Hplat Hkeep] with %hs
  · isplitl [Hplat] <;> iassumption
  rcases hs with ⟨np, hsr⟩
  subst hsr
  simp only [isPhysical] at *
  icases Hrest with ⟨Hshared, Hstate⟩
  iunfold arrShared at Hshared
  icases Hshared with ⟨HM, %hwf, %hdom, #Hdead, Hghost⟩
  iexists np, M, σ
  iframe Hpart Hplat HM Hdead Hghost Hstate Hkeep
  isplit
  · ipureintro; exact hwf
  · ipureintro; exact hdom

/-- …and close it again, possibly at a different abstract state. -/
theorem arrInvCloseRead (γ : WArrγ) (γP : GName) (platform : Val) (np : Nat)
    (M : H WData) (σ : Arr) (hwf : σ.wellFormed)
    (hdom : ∀ i, dom M i ↔ i < σ.counter) :
  ⊢@{IProp GF}
    arcPart γ γP -∗ isPlatform γP (.read (np + 1)) platform -∗
    wMetaMap γ.l q1_2 M -∗ deadNodes M σ.cells -∗
    isGhost (nodeSlotShared γP) γ.l σ.cells -∗ wStateVar γ.s q3_4 σ M -∗
      arrInvBody γ γP platform := by
  iintro Hpart Hplat HM #Hdead Hghost Hstate
  unfold arrInvBody arrPhysPart
  iframe Hpart
  iexists (RwLock.State.read (np + 1)), M, σ
  iframe Hplat
  simp only [isPhysical]
  iframe Hstate
  unfold arrShared
  iframe HM Hdead Hghost
  isplit
  · ipureintro; exact hwf
  · ipureintro; exact hdom

/-- A stale handle names nothing.

    This is the payoff of the whole design, and the one statement `Array` cannot
    make.  There a client's handle is strong, so a revoked cell is still allocated
    and still reachable, and the best a specification can say is "the cell is
    revoked" — a state that has to be modelled, carried in the invariant, and
    reasoned about at every step.  Here the failed upgrade is *equivalent* to
    absence from `σ`, so the abstract model needs no revoked state at all.

    Both directions of that equivalence are needed and both are here:
    `isArc_mem` gives live ⟹ present, this gives dead ⟹ absent. -/
theorem arrPhysPart_frag_dead (γ : WArrγ) (γP : GName) (platform : Val)
    (σc : Arr) (d : WData) (id : Nat) (q : Qp) :
  ⊢@{IProp GF}
    arrPhysPart γ γP platform -∗ arrFrag γ σc -∗ Arr.isNode γ id d -∗
    cellDead d.cell -∗ rwGuardFrac γP RwLock.Mode.read q -∗
      ⌜id ∉ σc.cells.map (·.1)⌝ ∗ arrPhysPart γ γP platform ∗ arrFrag γ σc ∗
      rwGuardFrac γP RwLock.Mode.read q := by
  iintro Hphys Hfrag #Hnode #Hcd Hkeep
  iunfold arrPhysPart at Hphys
  icases Hphys with ⟨%s, %M, %σ, Hplat, Hrest⟩
  icases isPlatform_read_guard_valid γP s platform q $$ [Hplat Hkeep] with %hs
  · isplitl [Hplat] <;> iassumption
  rcases hs with ⟨np, hsr⟩
  subst hsr
  simp only [isPhysical] at *
  icases Hrest with ⟨Hshared, Hstate⟩
  -- the client's quarter and the invariant's three quarters must agree on `σ`
  icases arrFrag_agree γ σc σ M $$ [Hfrag Hstate] with %hσ
  · isplitl [Hfrag] <;> iassumption
  subst hσ
  iunfold arrShared at Hshared
  icases Hshared with ⟨HM, %hwf, %hdom, #Hdead, Hghost⟩
  ihave #Hmeta : wMetaAt γ.l id d $$ [Hnode]
  · iunfold Arr.isNode at Hnode
    iexact Hnode
  ihave #hnin : ⌜id ∉ σc.cells.map (·.1)⌝ $$ [Hghost]
  · iapply cellDead_not_mem γP γ.l σc d id $$ Hmeta Hcd Hghost
  icases hnin with %hnin
  iframe Hfrag Hkeep
  isplit
  · ipureintro; exact hnin
  unfold arrPhysPart
  iexists (RwLock.State.read (np + 1)), M, σc
  iframe Hplat
  simp only [isPhysical]
  iframe Hstate
  unfold arrShared
  iframe HM Hdead Hghost
  isplit
  · ipureintro; exact hwf
  · ipureintro; exact hdom

/-! ### Borrowing a strong reference through a weak handle

Every operation on a cell starts by upgrading the client's weak handle and ends by
dropping the result.  Both halves have to go through the invariant — the counts live
there — so they are packaged here once and reused.

The read permit is the currency: a borrow costs half of it, a return gives it back.
That is the whole content of the deposit, and it is what a thread holding the
platform exclusively can observe the absence of. -/

/-- Take a temporary strong reference.  Fails exactly when the cell has been
    revoked, and then says so persistently. -/
theorem borrow_read_spec
    (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) (d : WData) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    Arr.isNode γ id d -∗
    isWeak d.arc node d.mux -∗
    rwGuardFrac γP RwLock.Mode.read q1_2 -∗
    rwGuardFrac γP RwLock.Mode.read q1_4 -∗
    WP hl(&Weak.tryUpgrade &node)
      {{ r,
        rwGuardFrac γP RwLock.Mode.read q1_4 ∗ isWeak d.arc node d.mux ∗
        ((⌜r = hl_val(none())⌝ ∗ cellDead d.cell ∗
            rwGuardFrac γP RwLock.Mode.read q1_2) ∨
         (⌜r = hl_val(some(&node))⌝ ∗ isArc d.arc node d.mux ∗ refTok d)) }} := by
  iintro #Hinv #Hnode Hweak Hdep Hkeep
  iapply Weak.tryUpgrade_atomic_spec (γ := d.arc) node d.mux $$ Hweak
  iunfold isArrInv at Hinv
  iauintro
  iinv Hinv as Hbody
  iunfold arrInvBody at Hbody
  icases Hbody with ⟨Hpart, Hphys⟩
  icases arcPart_acc γ γP id d $$ Hpart Hnode with ⟨Hcell, Hback⟩
  icases arcCell_unpack γP d $$ Hcell with ⟨%n, %m, Hauth, Hcnt, Hled⟩
  iunfold arrPhysPart at Hphys
  icases Hphys with ⟨%s, %M, %σ, Hplat, Hrest⟩
  icases arcLedger_no_write_borrow γP d n s platform q1_4 $$ [Hplat Hkeep Hled]
    with ⟨Hplat, Hkeep, Hled⟩
  · isplitl [Hplat]
    · iassumption
    · isplitl [Hkeep] <;> iassumption
  iaaccintro' with Hauth
  · iintro Hauth
    imodintro
    isplitl [Hauth Hcnt Hled Hback Hplat Hrest]
    · unfold arrInvBody arrPhysPart
      isplitl [Hback Hauth Hcnt Hled]
      · iapply Hback
        iapply arcCell_pack γP d n m
        iframe Hauth Hcnt
        unfold arcLedger
        icases Hled with (H | H)
        · ileft; iexact H
        · iright; iright; iexact H
      · iexists s, M, σ
        iframe
    · iframe Hdep Hkeep
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro %r ⟨Hweak, Hcases⟩
    icases Hcases with (⟨%hz, %hr, Hauth⟩ | ⟨%hpos, %hr, Hauth, Harc⟩)
    · subst hz
      ihave ⟨Hcnt, #Hcd⟩ : (refAuth d 0 ∗ cellDead d.cell) $$ [Hcnt Hled]
      · icases Hled with (⟨Htok, -⟩ | ⟨Hcd, -⟩)
        · iexfalso
          icases refTok_pos d 0 $$ [Hcnt Htok] with %h
          · isplitl [Hcnt] <;> iassumption
          exact absurd h (Nat.lt_irrefl 0)
        · iframe Hcnt Hcd
      imodintro
      isplitl [Hauth Hcnt Hback Hplat Hrest]
      · unfold arrInvBody arrPhysPart
        isplitl [Hback Hauth Hcnt]
        · iapply Hback
          iapply arcCell_pack γP d 0 m
          iframe Hauth Hcnt
          unfold arcLedger
          iright; iright
          isplitl []
          · iexact Hcd
          · ipureintro; rfl
        · iexists s, M, σ
          iframe
      · iframe Hkeep Hweak
        ileft
        iframe Hdep
        isplit
        · ipureintro; exact hr
        · iexact Hcd
    · ihave Hled : (refAuth d n ∗ refTok d ∗ arcDeposit γP n ∗ arcAliveTok d q1_4 ∗
          ⌜1 ≤ n⌝) $$ [Hcnt Hled]
      · icases Hled with (⟨Htok, Hdep', Hq⟩ | ⟨-, %hz⟩)
        · iframe Hcnt Htok Hdep' Hq
          ipureintro; omega
        · exact absurd hz (by omega)
      icases Hled with ⟨Hcnt, Htok, Hdep', Hq, %hge⟩
      imod refAuth_take d n $$ Hcnt with ⟨Hcnt, Hmine⟩
      imodintro
      isplitl [Hauth Hcnt Htok Hdep' Hdep Hq Hback Hplat Hrest]
      · unfold arrInvBody arrPhysPart
        isplitl [Hback Hauth Hcnt Htok Hdep' Hdep Hq]
        · iapply Hback
          iapply arcCell_pack γP d (n + 1) m
          iframe Hauth Hcnt
          unfold arcLedger
          ileft
          iframe Htok Hq
          iapply (arcDeposit_succ γP n hge).mpr
          iframe Hdep' Hdep
        · iexists s, M, σ
          iframe
      · iframe Hkeep Hweak
        iright
        iframe Harc Hmine
        ipureintro; exact hr

/-- Give the temporary reference back and recover the half permit.  The drop is
    never the last one, so no cell is freed here. -/
theorem return_read_spec
    (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) (d : WData) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    Arr.isNode γ id d -∗
    isArc d.arc node d.mux -∗
    refTok d -∗
    rwGuardFrac γP RwLock.Mode.read q1_4 -∗
    WP hl(&Arc.drop &RwLock.drop &node)
      {{ _r,
        rwGuardFrac γP RwLock.Mode.read q1_2 ∗
        rwGuardFrac γP RwLock.Mode.read q1_4 }} := by
  iintro #Hinv #Hnode Harc Hmine Hkeep
  iapply Arc.drop_nonlast_spec (γ := d.arc) hl_val(&RwLock.drop) node d.mux $$ Harc
  iunfold isArrInv at Hinv
  iauintro
  iinv Hinv as Hbody
  iunfold arrInvBody at Hbody
  icases Hbody with ⟨Hpart, Hphys⟩
  icases arcPart_acc γ γP id d $$ Hpart Hnode with ⟨Hcell, Hback⟩
  icases arcCell_unpack γP d $$ Hcell with ⟨%n, %m, Hauth, Hcnt, Hled⟩
  iunfold arrPhysPart at Hphys
  icases Hphys with ⟨%s, %M, %σ, Hplat, Hrest⟩
  icases arcLedger_no_write_borrow γP d n s platform q1_4 $$ [Hplat Hkeep Hled]
    with ⟨Hplat, Hkeep, Hled⟩
  · isplitl [Hplat]
    · iassumption
    · isplitl [Hkeep] <;> iassumption
  ihave ⟨Hcnt, Hmine, Htok, Hdep', Hq, %hge⟩ :
      (refAuth d n ∗ refTok d ∗ refTok d ∗ arcDeposit γP n ∗ arcAliveTok d q1_4 ∗
        ⌜2 ≤ n⌝)
      $$ [Hcnt Hled Hmine]
  · icases Hled with (⟨Htok, Hdep', Hq⟩ | ⟨-, %hz⟩)
    · ihave #Hge : ⌜2 ≤ n⌝ $$ [Hcnt Htok Hmine]
      · iapply refTok_two d n
        isplitl [Hcnt]
        · iassumption
        isplitl [Htok] <;> iassumption
      iframe Hcnt Hmine Htok Hdep' Hq Hge
    · subst hz
      iexfalso
      icases refTok_pos d 0 $$ [Hcnt Hmine] with %h
      · isplitl [Hcnt] <;> iassumption
      exact absurd h (Nat.lt_irrefl 0)
  ihave Hpre : (arcAuth d.arc n m ∗ ⌜2 ≤ n⌝) $$ [Hauth]
  · iframe Hauth
    ipureintro; exact hge
  iaaccintro' with Hpre
  · iintro Hpre
    icases Hpre with ⟨Hauth, -⟩
    imodintro
    isplitl [Hauth Hcnt Htok Hdep' Hq Hback Hplat Hrest]
    · unfold arrInvBody arrPhysPart
      isplitl [Hback Hauth Hcnt Htok Hdep' Hq]
      · iapply Hback
        iapply arcCell_pack γP d n m
        iframe Hauth Hcnt
        unfold arcLedger
        ileft
        iframe
      · iexists s, M, σ
        iframe
    · iframe Hmine Hkeep
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro Hauth
    imod refAuth_give d (n - 1) $$ [Hcnt Hmine] with Hcnt
    · rw [Nat.sub_add_cancel (by omega)]
      isplitl [Hcnt] <;> iassumption
    ihave ⟨Hdep', Hback'⟩ :
        (arcDeposit γP (n - 1) ∗ rwGuardFrac γP RwLock.Mode.read q1_2) $$ [Hdep']
    · iapply (arcDeposit_succ γP (n - 1) (by omega)).mp
      rw [Nat.sub_add_cancel (by omega)]
      iexact Hdep'
    imodintro
    isplitl [Hauth Hcnt Htok Hdep' Hq Hback Hplat Hrest]
    · unfold arrInvBody arrPhysPart
      isplitl [Hback Hauth Hcnt Htok Hdep' Hq]
      · iapply Hback
        iapply arcCell_pack γP d (n - 1) m
        iframe Hauth Hcnt
        unfold arcLedger
        ileft
        iframe
      · iexists s, M, σ
        iframe
    · iframe Hback' Hkeep

theorem q1_2_add_q1_4_add_q1_4 : q1_2 + (q1_4 + q1_4) = 1 := by
  apply Subtype.ext
  show (q1_2 : Qp).val + ((q1_4 : Qp).val + (q1_4 : Qp).val) = (1 : Qp).val
  simp [q1_2, q1_4, Qp.half]
  grind

/-- The read permit splits three ways: half is the borrow deposit, a quarter is
    parked in the cell's slot while it is locked, and a quarter stays in hand to
    witness that the platform really is read-held. -/
theorem rwGuard_split3 (γP : GName) :
  ⊢@{IProp GF}
    rwGuard γP RwLock.Mode.read -∗
      rwGuardFrac γP RwLock.Mode.read q1_2 ∗
      rwGuardFrac γP RwLock.Mode.read q1_4 ∗
      rwGuardFrac γP RwLock.Mode.read q1_4 := by
  rw [rwGuard_eq γP RwLock.Mode.read, ← q1_2_add_q1_4_add_q1_4]
  iintro H
  icases (RwLock.rwGuardFrac_split γP RwLock.Mode.read q1_2 (q1_4 + q1_4)).mp $$ H
    with ⟨H₁, H₂⟩
  iframe H₁
  iapply (RwLock.rwGuardFrac_split γP RwLock.Mode.read q1_4 q1_4).mp $$ H₂

theorem rwGuard_join3 (γP : GName) :
  ⊢@{IProp GF}
    rwGuardFrac γP RwLock.Mode.read q1_2 -∗
    rwGuardFrac γP RwLock.Mode.read q1_4 -∗
    rwGuardFrac γP RwLock.Mode.read q1_4 -∗
      rwGuard γP RwLock.Mode.read := by
  rw [rwGuard_eq γP RwLock.Mode.read, ← q1_2_add_q1_4_add_q1_4]
  iintro H₁ H₂ H₃
  iapply (RwLock.rwGuardFrac_split γP RwLock.Mode.read q1_2 (q1_4 + q1_4)).mpr
  iframe H₁
  iapply (RwLock.rwGuardFrac_split γP RwLock.Mode.read q1_4 q1_4).mpr
  iframe

/-- Downgrade the successor link to a handle for the caller.  The link itself is the
    list's own strong reference and is put straight back, so the cell's strong count
    does not move — only the weak count. -/
theorem downgrade_child_spec
    (γ : WArrγ) (γP : GName) (platform child : Val) (cid : Nat) (d' : WData) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    Arr.isNode γ cid d' -∗
    isArc d'.arc child d'.mux -∗
    WP hl(&Arc.downgrade &child)
      {{ w, ⌜w = child⌝ ∗ isArc d'.arc child d'.mux ∗ isWeak d'.arc child d'.mux }} := by
  iintro #Hinv #Hnode Harc
  iapply Arc.downgrade_spec (γ := d'.arc) child d'.mux $$ Harc
  iunfold isArrInv at Hinv
  iauintro
  iinv Hinv as Hbody
  iunfold arrInvBody at Hbody
  icases Hbody with ⟨Hpart, Hphys⟩
  icases arcPart_acc γ γP cid d' $$ Hpart Hnode with ⟨Hcell, Hback⟩
  icases arcCell_unpack γP d' $$ Hcell with ⟨%n, %m, Hauth, Hcnt, Hled⟩
  iaaccintro' with Hauth
  · iintro Hauth
    imodintro
    isplitl [Hauth Hcnt Hled Hback Hphys]
    · iapply arrInvBody_intro γ γP platform $$ [Hback Hauth Hcnt Hled] Hphys
      iapply Hback
      iapply arcCell_pack γP d' n m
      iframe
    · iframe
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro ⟨Hauth, Harc, Hweak⟩
    imodintro
    isplitl [Hauth Hcnt Hled Hback Hphys]
    · iapply arrInvBody_intro γ γP platform $$ [Hback Hauth Hcnt Hled] Hphys
      iapply Hback
      iapply arcCell_pack γP d' n (m + 1)
      iframe
    · iframe Harc Hweak
      itrivial

/-! ### Taking and releasing a cell's own lock

Under the platform read lock the chain is shared, so a cell's slot has to be reached
through the invariant.  Acquiring parks a quarter of the platform read permit in the
slot; releasing takes it back.  That parked quarter is what stops a thread from
leaving the platform read critical section while it still holds a cell locked. -/

theorem node_acquire_spec
    (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) (d : WData) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    Arr.isNode γ id d -∗
    isArc d.arc node d.mux -∗
    rwGuardFrac γP RwLock.Mode.read q1_4 -∗
    rwGuardFrac γP RwLock.Mode.read q1_4 -∗
    WP hl(&RwLock.write_acquire &(d.mux))
      {{ r,
        ⌜r = hl_val(#d.ptr)⌝ ∗
        rwGuardFrac γP RwLock.Mode.read q1_4 ∗
        isArc d.arc node d.mux ∗
        rwGuard d.rw RwLock.Mode.write ∗
        ∃ nxt : Option Nat, cellAlive d.cell q1_2 nxt ∗ payload γ.l d nxt }} := by
  iintro #Hinv #Hnode Harc Hpay Hkeep
  iapply RwLock.write_acquire_spec d.rw d.mux hl_val(#d.ptr)
  iunfold isArrInv at Hinv
  iauintro
  iinv Hinv as Hbody
  iunfold arrInvBody at Hbody
  icases Hbody with ⟨Hpart, Hphys⟩
  iunfold arrPhysPart at Hphys
  icases Hphys with ⟨%s, %M, %σ, Hplat, Hrest⟩
  -- the platform is read-held, so the shared view is available
  icases isPlatform_read_guard_valid γP s platform q1_4 $$ [Hplat Hkeep] with %hs
  · isplitl [Hplat] <;> iassumption
  rcases hs with ⟨np, hsr⟩
  subst hsr
  simp only [isPhysical] at *
  icases Hrest with ⟨Hshared, Hstate⟩
  iunfold arrShared at Hshared
  icases Hshared with ⟨HM, %hwf, %hdom, #Hdead, Hghost⟩
  ihave #hlookup : ⌜get? M id = some d⌝ $$ [HM Hnode]
  · iunfold Arr.isNode at Hnode
    iapply wMetaMap_lookup γ.l q1_2 M id d $$ HM Hnode
  icases hlookup with %hlookup
  icases isArc_mem γ γP M σ node id d hlookup $$ Hpart Hnode Hdead Harc
    with ⟨%hin, Hpart, Harc⟩
  ihave #Hmeta : wMetaAt γ.l id d $$ [Hnode]
  · iunfold Arr.isNode at Hnode
    iexact Hnode
  iunfold isGhost at Hghost
  ihave ⟨Hslot, Hback⟩ := isGhostHelpAccSucc γ.l d (nodeSlotShared γP) id σ.cells hin
    $$ Hmeta Hghost
  iunfold nodeSlotShared at Hslot
  icases Hslot with ⟨%sn, Hlock, Hstaten⟩
  iaaccintro' with Hlock
  · iintro Hlock
    imodintro
    isplitl [Hpart HM Hstate Hlock Hstaten Hback Hplat]
    · unfold arrInvBody arrPhysPart
      iframe Hpart
      iexists (RwLock.State.read (np + 1)), M, σ
      iframe Hplat
      simp only [isPhysical]
      iframe Hstate
      unfold arrShared isGhost
      iframe HM Hdead
      isplit
      · ipureintro; exact hwf
      isplit
      · ipureintro; exact hdom
      iapply Hback
      unfold aliveSlot nodeSlotShared
      iexists sn
      iframe
    · iframe Harc Hpay Hkeep
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro ⟨Hlock, Hguard, %hsn⟩
    subst hsn
    -- the slot was free, so the payload comes out and the parked quarter goes in
    ihave ⟨Hpayload, Hcellfull⟩ :
        (payload γ.l d (Arr.succOf σ.cells id) ∗
          cellAlive d.cell q3_4 (Arr.succOf σ.cells id)) $$ [Hstaten]
    · dsimp only [nodeSlotSharedBody]
      icases Hstaten with ⟨Hp, Hc⟩
      iframe Hp Hc
    ihave ⟨Hq4, Hq2⟩ : (cellAlive d.cell q1_4 (Arr.succOf σ.cells id) ∗
        cellAlive d.cell q1_2 (Arr.succOf σ.cells id)) $$ [Hcellfull]
    · iapply (cellAlive_split_gen d.cell q1_4 q1_2 (Arr.succOf σ.cells id)).mp
      rw [q1_4_add_q1_2]
      iexact Hcellfull
    imodintro
    isplitl [Hpart HM Hstate Hlock Hpay Hq4 Hback Hplat]
    · unfold arrInvBody arrPhysPart
      iframe Hpart
      iexists (RwLock.State.read (np + 1)), M, σ
      iframe Hplat
      simp only [isPhysical]
      iframe Hstate
      unfold arrShared isGhost
      iframe HM Hdead
      isplit
      · ipureintro; exact hwf
      isplit
      · ipureintro; exact hdom
      iapply Hback
      unfold aliveSlot nodeSlotShared
      iexists RwLock.State.write
      iframe Hlock
      dsimp only [nodeSlotSharedBody]
      iframe Hpay Hq4
    · itele_reduce
      isplitl []
      · itrivial
      iframe Harc Hkeep Hguard
      iexists (Arr.succOf σ.cells id)
      iframe Hq2
      iexact Hpayload

/-- Release a cell's lock, taking the parked quarter of the read permit back.  The
    successor may have been rewired in the meantime, which is why `nxt` is a
    parameter rather than being read off `σ`. -/
theorem node_release_spec
    (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) (d : WData)
    (nxt : Option Nat) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    Arr.isNode γ id d -∗
    rwGuard d.rw RwLock.Mode.write -∗
    cellAlive d.cell q1_2 nxt -∗
    payload γ.l d nxt -∗
    rwGuardFrac γP RwLock.Mode.read q1_4 -∗
    WP hl(&RwLock.write_release &(d.mux))
      {{ _r,
        rwGuardFrac γP RwLock.Mode.read q1_4 ∗
        rwGuardFrac γP RwLock.Mode.read q1_4 }} := by
  iintro #Hinv #Hnode Hguard Hq2 Hpayload Hkeep
  iapply RwLock.write_release_spec d.rw d.mux hl_val(#d.ptr) $$ Hguard
  iunfold isArrInv at Hinv
  iauintro
  iinv Hinv as Hbody
  iunfold arrInvBody at Hbody
  icases Hbody with ⟨Hpart, Hphys⟩
  iunfold arrPhysPart at Hphys
  icases Hphys with ⟨%s, %M, %σ, Hplat, Hrest⟩
  icases isPlatform_read_guard_valid γP s platform q1_4 $$ [Hplat Hkeep] with %hs
  · isplitl [Hplat] <;> iassumption
  rcases hs with ⟨np, hsr⟩
  subst hsr
  simp only [isPhysical] at *
  icases Hrest with ⟨Hshared, Hstate⟩
  iunfold arrShared at Hshared
  icases Hshared with ⟨HM, %hwf, %hdom, #Hdead, Hghost⟩
  ihave #Hmeta : wMetaAt γ.l id d $$ [Hnode]
  · iunfold Arr.isNode at Hnode
    iexact Hnode
  -- the cell is still in the list: we hold half its live witness
  ihave #hin : ⌜id ∈ σ.cells.map (·.1)⌝ $$ [Hq2 Hdead HM Hmeta]
  · by_cases hin : id ∈ σ.cells.map (·.1)
    · ipureintro; exact hin
    · iexfalso
      ihave #hlookup : ⌜get? M id = some d⌝ $$ [HM Hmeta]
      · iapply wMetaMap_lookup γ.l q1_2 M id d $$ HM Hmeta
      icases hlookup with %hlookup
      ihave #Hcd : cellDead d.cell $$ [Hdead]
      · iapply deadNodes_lookup M σ.cells id d hlookup hin
        iexact Hdead
      iapply cellAlive_dead_False d.cell q1_2 nxt
      isplitl [Hq2] <;> iassumption
  icases hin with %hin
  ihave ⟨%nxt0, Hslot, Hback⟩ := isGhostAccIn γ.l d (nodeSlotShared γP) id σ.cells hin
    $$ Hmeta Hghost
  iunfold nodeSlotShared at Hslot
  icases Hslot with ⟨%sn, Hlock, Hstaten⟩
  -- our own write permit says the slot is in the `write` state
  ihave ⟨%hsn, Hlock, Hpark, Hq4, Hq2⟩ :
      (⌜sn = RwLock.State.write⌝ ∗ isRwLock d.rw d.mux sn hl_val(#d.ptr) ∗
        rwGuardFrac γP RwLock.Mode.read q1_4 ∗ cellAlive d.cell q1_4 nxt0 ∗
        cellAlive d.cell q1_2 nxt) $$ [Hlock Hstaten Hq2]
  · rcases sn with ⟨h1 | h2 | h3⟩ <;> dsimp only [nodeSlotSharedBody] at *
    · icases Hstaten with ⟨-, Halive⟩
      iexfalso
      icases cellAlive_frac_valid d.cell q1_2 q3_4 nxt nxt0 $$ [Hq2 Halive] with %hv
      · isplitl [Hq2] <;> iassumption
      ipureintro
      have h34 : (q3_4 : Qp).val = 3/4 := by simp [q3_4, Qp.half]; grind
      have h12 : (q1_2 : Qp).val = 1/2 := by simp [q1_2, Qp.half]
      rw [Qp.val_add, h12, h34] at hv
      grind
    · iexfalso; iexact Hstaten
    · icases Hstaten with ⟨Hpark, Halive⟩
      iframe Hlock Hpark Halive Hq2
      ipureintro; rfl
  subst hsn
  ihave %hnxt := cellAlive_agree d.cell q1_2 q1_4 nxt nxt0 $$ [Hq2 Hq4]
  · isplitl [Hq2] <;> iassumption
  subst hnxt
  iaaccintro' with Hlock
  · iintro Hlock
    imodintro
    isplitl [Hpart HM Hstate Hlock Hpark Hq4 Hback Hplat]
    · unfold arrInvBody arrPhysPart
      iframe Hpart
      iexists (RwLock.State.read (np + 1)), M, σ
      iframe Hplat
      simp only [isPhysical]
      iframe Hstate
      unfold arrShared isGhost
      iframe HM Hdead
      isplit
      · ipureintro; exact hwf
      isplit
      · ipureintro; exact hdom
      iapply Hback
      unfold aliveSlot nodeSlotShared
      iexists RwLock.State.write
      iframe Hlock
      dsimp only [nodeSlotSharedBody]
      iframe Hpark Hq4
    · iframe Hq2 Hpayload Hkeep
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro Hlock
    -- put the payload and the full chain share back, and reclaim the parked quarter
    ihave Hfull : cellAlive d.cell q3_4 nxt $$ [Hq4 Hq2]
    · rw [← q1_4_add_q1_2]
      iapply (cellAlive_split_gen d.cell q1_4 q1_2 nxt).mpr
      iframe
    imodintro
    isplitl [Hpart HM Hstate Hlock Hfull Hpayload Hback Hplat]
    · unfold arrInvBody arrPhysPart
      iframe Hpart
      iexists (RwLock.State.read (np + 1)), M, σ
      iframe Hplat
      simp only [isPhysical]
      iframe Hstate
      unfold arrShared isGhost
      iframe HM Hdead
      isplit
      · ipureintro; exact hwf
      isplit
      · ipureintro; exact hdom
      iapply Hback
      unfold aliveSlot nodeSlotShared
      iexists RwLock.State.free
      iframe Hlock
      dsimp only [nodeSlotSharedBody]
      iframe Hpayload Hfull
    · itele_reduce
      iframe Hpark Hkeep

/-! ### What is left, and why it is not a matter of more proof script

`getChild` goes through because it does not move the abstract state: its
linearisation point can sit at the very end, after both deposits have been reclaimed
and the whole read permit is back in hand.

`insert` and `revoke` cannot do that.  Their linearisation point is forced to the
step that physically rewires the chain — the store, respectively the truncation —
because the invariant ties `σ.cells` to the physical links through `cellAlive`, and
that share can only be moved with the invariant open.  At that step half the read
permit is still sitting in the ledger, backing a strong reference that is only
dropped later, so the thread does *not* hold the whole permit there.

That is why `execute_shared_spec` above hands the permit back through the *non-atomic*
`POST` of `⟪ β | z, RET z; POST ⟫` rather than through `β`: everything in an atomic
postcondition has to be produced at the linearisation point, and the permit is not
shared state — it is the caller's private receipt.

`Array` never runs into this, and the reason is instructive: it has no deposit at
all.  Its only parked fraction belongs to a locked cell and comes back at exactly
the release that *is* its linearisation point.  The deposit is the price of keeping
reference counts outside the platform lock, and this is where that price is paid.

What remains for the two specifications below is then the ordinary work: `insert`
has to grow `M` (both halves of `wMetaMap` are inside the invariant under a read
lock, so one opening suffices), splice with `isGhostHelpAccInsert`, and advance the
abstract state at the store; `revoke` has to truncate with `isGhostHelpAccTruncate`
and, because it frees cells, needs a placeholder in `arcNodes` so that the freeing
thread can take `arcAuth` out of the invariant across the non-atomic `Arc.drop`. -/

omit [RwLockG GF] [ArcG GF] in
/-- A handle that fails to upgrade names a cell that is not in the list, and the
    abstract insert on such an `id` is a no-op. -/
theorem Arr.insert_of_not_mem (σ : Arr) (id : Nat) (x : Int)
    (h : id ∉ σ.cells.map (·.1)) : Arr.insert σ id x = (σ, none) := by
  unfold Arr.insert
  rw [if_neg]
  intro hany
  rw [List.any_eq_true] at hany
  obtain ⟨p, hp, hpid⟩ := hany
  exact h (List.mem_map.mpr ⟨p, hp, of_decide_eq_true hpid⟩)

/-- What `insert`'s body achieves, in the shape `execute_shared_spec` wants. -/
def insertQ (γ : WArrγ) (node : Val) (id : Nat) (x : Int)
    (σ σ' : Arr) (ret : Val) : IProp GF := iprop%
  ⌜σ' = (Arr.insert σ id x).1⌝ ∗ Arr.isId γ node id ∗
  match (Arr.insert σ id x).2 with
  | none => iprop% ⌜ret = hl_val(none())⌝
  | some nid => iprop%
      ∃ newNode : Val, ⌜ret = hl_val(some(&newNode))⌝ ∗ Arr.isId γ newNode nid

set_option maxRecDepth 8000 in
/-- Splice a cell in after `node`.

    The handle is weak, so the return value can be `none` because the cell was freed
    rather than because it was never there — but those are the same thing here: a
    cell leaves the list exactly by being freed.  So the postcondition is indexed by
    `Arr.insert` alone, with no extra failure case, which is precisely what `Array`
    cannot do. -/
theorem insert_spec
    (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) (x : Int) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&insert &platform &node #x) @ ↑arrN
    ⟪ ∃ ret, ∃ σ', arrFrag γ σ' ∗ insertQ γ node id x σ σ' ret | RET ret ⟫ := by
  iintro #Hinv Hid %Φ HAU
  unfold insert
  wp_pures
  have Hfull : (↑arrN : CoPset) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  have Hsub : ((⊤ : CoPset) \ (↑arrN : CoPset)) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  iapply execute_shared_spec γ γP platform _ (insertQ γ node id x) $$ Hinv [Hid]
  · iintro #Hinv' Hguard %Φ' HAU'
    iunfold Arr.isId at Hid
    icases Hid with ⟨%d, #Hnode, Hweak⟩
    wp_pures
    icases rwGuard_split3 γP $$ Hguard with ⟨Hdep, Hpay, Hkeep⟩
    wp_bind &Weak.tryUpgrade _
    iapply wp_wand $$ [Hnode Hweak Hdep Hkeep]
    · iapply borrow_read_spec γ γP platform node id d $$ Hinv' Hnode Hweak Hdep Hkeep
    iintro %r ⟨Hkeep, Hweak, Hcases⟩
    icases Hcases with (⟨%hr, #Hcd, Hdep⟩ | ⟨%hr, Harc, Hmine⟩)
    · -- the handle was stale: the cell has left the list, so the insert is a no-op
      subst hr
      wp_pures
      ihave #Hinvraw : inv arrN (arrInvBody γ γP platform) $$ [Hinv']
      · iunfold isArrInv at Hinv'
        iexact Hinv'
      imod inv_acc Hfull $$ Hinvraw with ⟨>HI, Hcl⟩
      iunfold arrInvBody at HI
      icases HI with ⟨Hpart, Hphys⟩
      iauopen HAU' with ⟨%σc, Hfrag, Hclose⟩
      icases arrPhysPart_frag_dead γ γP platform σc d id q1_4
          $$ Hphys Hfrag Hnode Hcd Hkeep with ⟨%hnin, Hphys, Hfrag, Hkeep⟩
      icases Hclose with ⟨-, Hcommit⟩
      have hins := Arr.insert_of_not_mem σc id x hnin
      ihave Hbeta : (∃ σ', arrFrag γ σ' ∗ insertQ γ node id x σc σ' hl_val(none()))
          $$ [Hfrag Hweak]
      · iexists (Arr.insert σc id x).1
        rw [hins]
        iframe Hfrag
        unfold insertQ
        rw [hins]
        isplit
        · ipureintro; rfl
        isplitl [Hweak]
        · unfold Arr.isId
          iexists d
          iframe Hweak
          iexact Hnode
        · ipureintro; rfl
      imod Hcommit $$ Hbeta with HΦ
      imod Hcl $$ [Hpart Hphys] with -
      · unfold arrInvBody
        iframe
      imodintro
      simp only [wandM]
      iapply HΦ
      isplitl [Hdep Hpay Hkeep]
      · iapply rwGuard_join3 γP $$ Hdep Hpay Hkeep
      · ipureintro; rfl
    · -- the handle was live: allocate, link, and splice at the release
      subst hr
      wp_pures
      wp_bind &Arc.get _
      iapply Arc.get_spec (γ := d.arc) node d.mux $$ Harc
      iintro !> Harc
      wp_pures
      wp_bind &RwLock.write_acquire _
      iapply wp_wand $$ [Hnode Harc Hpay Hkeep]
      · iapply node_acquire_spec γ γP platform node id d $$ Hinv' Hnode Harc Hpay Hkeep
      iintro %ptr ⟨%hptr, Hkeep, Harc, Hwguard, %nxt, Hcell, Hpayload⟩
      subst hptr
      wp_pures
      -- split the payload into the raw cell and exactly `new`'s precondition
      ihave ⟨%nv, Hptr, Hpre⟩ :
          (∃ nv : Val, d.ptr ↦ hl_val((#d.val, &nv)) ∗
            (match nxt with
             | none => iprop% ⌜nv = hl_val(none())⌝
             | some i => iprop% ∃ v : Val, ⌜nv = hl_val(some(&v))⌝ ∗ wSuccRef γ.l v i))
          $$ [Hpayload]
      · cases nxt with
        | none =>
            iunfold payload at Hpayload
            iexists hl_val(none())
            iframe Hpayload
            itrivial
        | some i =>
            iunfold payload at Hpayload
            icases Hpayload with ⟨%v, Hp, Hsucc⟩
            iexists hl_val(some(&v))
            iframe Hp
            iexists v
            iframe Hsucc
            itrivial
      wp_bind !_
      iapply wp_load $$ Hptr
      iintro !> Hptr
      wp_pures
      wp_bind &new _ _
      iapply new_spec γ.l γP x nv nxt $$ Hpre
      iintro %newNode !> ⟨%dNew, %hxval, HcellNew, HarcNew, HlockNew, HaliveNew, HpayNew⟩
      wp_pures
      wp_bind &Arc.downgrade _
      icases arcCell_unpack γP dNew $$ HcellNew with ⟨%nN, %mN, HauthN, HcntN, HledN⟩
      iapply Arc.downgrade_seq_spec (γ := dNew.arc) newNode dNew.mux nN mN
        $$ [HarcNew HauthN]
      · iframe
      iintro !> ⟨HauthN, HarcNew, HweakNew⟩
      wp_pures
      wp_bind (_ ← _)
      iapply wp_store $$ Hptr
      iintro !> Hptr
      wp_pures
      -- releasing the cell's lock is the linearisation point: the new cell becomes
      -- visible and the abstract state moves, both at this one step
      wp_bind &RwLock.write_release _
      ihave #Hinvraw : inv arrN (arrInvBody γ γP platform) $$ [Hinv']
      · iunfold isArrInv at Hinv'
        iexact Hinv'
      have Hfull' : (↑arrN : CoPset) ⊆ ((⊤ : CoPset) \ (∅ : CoPset)) :=
        fun _ _ => CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.mem_empty⟩
      iapply RwLock.write_release_spec d.rw d.mux hl_val(#d.ptr) $$ Hwguard
      iauintro
      iapply aacc_inv _ _ _ _ Hfull' $$ Hinvraw
      iintro HI
      icases arrInvOpenRead γ γP platform $$ HI Hkeep
        with ⟨%np, %M, %σ, %hwf, %hdom, Hpart, Hplat, HM, #Hdead, Hghost, Hstate, Hkeep⟩
      ihave #hlookup : ⌜get? M id = some d⌝ $$ [HM Hnode]
      · iunfold Arr.isNode at Hnode
        iapply wMetaMap_lookup γ.l q1_2 M id d $$ HM Hnode
      icases hlookup with %hlookup
      icases isArc_mem γ γP M σ node id d hlookup $$ Hpart Hnode Hdead Harc
        with ⟨%hin, Hpart, Harc⟩
      obtain ⟨pre, xv, post, hsplit⟩ := Arr.exists_split_id hin
      iunfold isGhost at Hghost
      ihave Hghost : isGhostHelp (nodeSlotShared γP) γ.l none (pre ++ (id, xv) :: post)
          $$ [Hghost]
      · rw [← hsplit]
        iexact Hghost
      ihave #Hmeta : wMetaAt γ.l id d $$ [Hnode]
      · iunfold Arr.isNode at Hnode
        iexact Hnode
      ihave ⟨Hslot, Hback⟩ :=
        isGhostHelpAccInsert γ.l d (nodeSlotShared γP) none id xv post pre $$ Hmeta Hghost
      iunfold aliveSlot at Hslot
      iunfold nodeSlotShared at Hslot
      icases Hslot with ⟨%sn, Hlock, Hstaten⟩
      -- the payload is in our hands, so the slot is neither free nor read-held
      ihave ⟨%hsn, Hlock, Hpark, Hq4, Hcell⟩ :
          (⌜sn = RwLock.State.write⌝ ∗ isRwLock d.rw d.mux sn hl_val(#d.ptr) ∗
            rwGuardFrac γP RwLock.Mode.read q1_4 ∗
            cellAlive d.cell q1_4 (nextIdOr post none) ∗
            cellAlive d.cell q1_2 nxt) $$ [Hlock Hstaten Hcell]
      · rcases sn with ⟨h1 | h2 | h3⟩ <;> dsimp only [nodeSlotSharedBody] at *
        · icases Hstaten with ⟨-, Halive⟩
          iexfalso
          icases cellAlive_frac_valid d.cell q1_2 q3_4 nxt (nextIdOr post none)
            $$ [Hcell Halive] with %hv
          · isplitl [Hcell] <;> iassumption
          ipureintro
          have h34 : (q3_4 : Qp).val = 3/4 := by simp [q3_4, Qp.half]; grind
          have h12 : (q1_2 : Qp).val = 1/2 := by simp [q1_2, Qp.half]
          rw [Qp.val_add, h12, h34] at hv
          grind
        · iexfalso; iexact Hstaten
        · icases Hstaten with ⟨Hpark, Halive⟩
          iframe Hlock Hpark Halive Hcell
          ipureintro; rfl
      subst hsn
      ihave %hnx := cellAlive_agree d.cell q1_2 q1_4 nxt (nextIdOr post none) $$ [Hcell Hq4]
      · isplitl [Hcell] <;> iassumption
      subst hnx
      iaaccintro' with Hlock
      · -- abort: park the slot back exactly as we found it
        iintro Hlock
        imodintro
        ihave Hslot : aliveSlot (nodeSlotShared γP) γ.l d (nextIdOr post none)
            $$ [Hlock Hpark Hq4]
        · unfold aliveSlot nodeSlotShared
          iexists RwLock.State.write
          iframe Hlock
          dsimp only [nodeSlotSharedBody]
          iframe Hpark Hq4
        icases Hback with ⟨Hsame, -⟩
        ihave Hghost := Hsame $$ Hslot
        ihave Hghost : isGhost (nodeSlotShared γP) γ.l σ.cells $$ [Hghost]
        · unfold isGhost
          rw [hsplit]
          iexact Hghost
        ihave HIb := arrInvCloseRead γ γP platform np M σ hwf hdom
          $$ Hpart Hplat HM Hdead Hghost Hstate
        iframe HIb HAU' Harc Hmine Hweak Hcell Hptr Hkeep
        iframe HauthN HcntN HledN HarcNew HweakNew HlockNew HaliveNew HpayNew
        repeat' first | (imodintro; iassumption) | isplitl []
      · sorry
  · iexact HAU

/-- Detach and free everything strictly after `node`.

    Unlike `Array`'s, this postcondition says nothing about surviving cells, because
    there are none: the handles a client holds on the revoked suffix all go stale. -/
theorem revoke_spec
    (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&revoke &platform &node) @ ↑arrN
    ⟪ arrFrag γ (Arr.revoke σ id).1 ∗ Arr.isId γ node id
      | RET match (Arr.revoke σ id).2 with
            | none => hl_val(none())
            | some _ => hl_val(some(#()))
    ⟫ := by
  sorry

/-- What `getChild`'s body achieves, in the shape `execute_shared_spec` wants. -/
def getChildQ (γ : WArrγ) (node : Val) (id : Nat)
    (σ σ' : Arr) (ret : Val) : IProp GF := iprop%
  ⌜σ' = σ⌝ ∗ Arr.isId γ node id ∗
  ((⌜ret = hl_val(none())⌝ ∗ ⌜id ∉ σ.cells.map (·.1)⌝) ∨
   ⌜ret = hl_val(some(none()))⌝ ∨
   (∃ (w : Val) (cid : Nat), ⌜ret = hl_val(some(some(&w)))⌝ ∗ Arr.isId γ w cid))

set_option maxRecDepth 8000 in
/-- A handle on the successor.  Reading the list does not move it, so `σ` does not
    change; the outer `option` distinguishes "the handle was stale" from "there is no
    successor".

    The stale case is where the weak handle shows its hand: `Array` would have to
    hand back a live-but-revoked cell, whereas here the answer is exactly
    `id ∉ σ.cells`. -/
theorem getChild_spec
    (γ : WArrγ) (γP : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&getChild &platform &node) @ ↑arrN
    ⟪ ∃ ret, ∃ σ', arrFrag γ σ' ∗ getChildQ γ node id σ σ' ret | RET ret ⟫ := by
  iintro #Hinv Hid %Φ HAU
  unfold getChild
  wp_pures
  have Hfull : (↑arrN : CoPset) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  have Hsub : ((⊤ : CoPset) \ (↑arrN : CoPset)) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  iapply execute_shared_spec γ γP platform _ (getChildQ γ node id) $$ Hinv [Hid]
  · iintro #Hinv' Hguard %Φ' HAU'
    iunfold Arr.isId at Hid
    icases Hid with ⟨%d, #Hnode, Hweak⟩
    wp_pures
    icases rwGuard_split3 γP $$ Hguard with ⟨Hdep, Hpay, Hkeep⟩
    wp_bind &Weak.tryUpgrade _
    iapply wp_wand $$ [Hnode Hweak Hdep Hkeep]
    · iapply borrow_read_spec γ γP platform node id d $$ Hinv' Hnode Hweak Hdep Hkeep
    iintro %r ⟨Hkeep, Hweak, Hcases⟩
    icases Hcases with (⟨%hr, #Hcd, Hdep⟩ | ⟨%hr, Harc, Hmine⟩)
    · -- the handle was stale: the cell has left the list, so commit at once
      subst hr
      wp_pures
      ihave #Hinvraw : inv arrN (arrInvBody γ γP platform) $$ [Hinv']
      · iunfold isArrInv at Hinv'
        iexact Hinv'
      imod inv_acc Hfull $$ Hinvraw with ⟨>HI, Hcl⟩
      iunfold arrInvBody at HI
      icases HI with ⟨Hpart, Hphys⟩
      iauopen HAU' with ⟨%σc, Hfrag, Hclose⟩
      icases arrPhysPart_frag_dead γ γP platform σc d id q1_4
          $$ Hphys Hfrag Hnode Hcd Hkeep with ⟨%hnin, Hphys, Hfrag, Hkeep⟩
      icases Hclose with ⟨-, Hcommit⟩
      ihave Hbeta : (∃ σ', arrFrag γ σ' ∗ getChildQ γ node id σc σ' hl_val(none()))
          $$ [Hfrag Hweak]
      · iexists σc
        iframe Hfrag
        unfold getChildQ
        isplit
        · ipureintro; rfl
        isplitl [Hweak]
        · unfold Arr.isId
          iexists d
          iframe Hweak
          iexact Hnode
        · ileft
          isplit
          · ipureintro; rfl
          · ipureintro; exact hnin
      imod Hcommit $$ Hbeta with HΦ
      imod Hcl $$ [Hpart Hphys] with -
      · unfold arrInvBody
        iframe
      imodintro
      simp only [wandM]
      iapply HΦ
      isplitl [Hdep Hpay Hkeep]
      · iapply rwGuard_join3 γP $$ Hdep Hpay Hkeep
      · ipureintro; rfl
    · -- the handle was live: read the successor link out under the cell's own lock
      subst hr
      wp_pures
      wp_bind &Arc.get _
      iapply Arc.get_spec (γ := d.arc) node d.mux $$ Harc
      iintro !> Harc
      wp_pures
      wp_bind &RwLock.write_acquire _
      iapply wp_wand $$ [Hnode Harc Hpay Hkeep]
      · iapply node_acquire_spec γ γP platform node id d $$ Hinv' Hnode Harc Hpay Hkeep
      iintro %ptr ⟨%hptr, Hkeep, Harc, Hwguard, %nxt, Hcell, Hpayload⟩
      subst hptr
      wp_pures
      wp_bind !_
      iunfold payload at Hpayload
      cases nxt with
      | none =>
          iapply wp_load $$ Hpayload
          iintro !> Hpayload
          wp_pures
          ihave Hpayload : payload γ.l d none $$ [Hpayload]
          · unfold payload
            iexact Hpayload
          wp_bind &RwLock.write_release _
          iapply wp_wand $$ [Hnode Hwguard Hcell Hpayload Hkeep]
          · iapply node_release_spec γ γP platform node id d none
              $$ Hinv' Hnode Hwguard Hcell Hpayload Hkeep
          iintro %u ⟨Hpay, Hkeep⟩
          wp_pures
          wp_bind &Arc.drop _ _
          iapply wp_wand $$ [Hnode Harc Hmine Hkeep]
          · iapply return_read_spec γ γP platform node id d
              $$ Hinv' Hnode Harc Hmine Hkeep
          iintro %u2 ⟨Hdep, Hkeep⟩
          wp_pures
          -- both deposits are back, so the whole permit is in hand: commit here
          iauopen HAU' with ⟨%σc, Hfrag, Hclose⟩
          icases Hclose with ⟨-, Hcommit⟩
          ihave Hbeta : (∃ σ', arrFrag γ σ' ∗
              getChildQ γ node id σc σ' hl_val(some(none()))) $$ [Hfrag Hweak]
          · iexists σc
            iframe Hfrag
            unfold getChildQ
            isplit
            · ipureintro; rfl
            isplitl [Hweak]
            · unfold Arr.isId
              iexists d
              iframe Hweak
              iexact Hnode
            · iright; ileft
              ipureintro; rfl
          imod Hcommit $$ Hbeta with HΦ
          imodintro
          simp only [wandM]
          iapply HΦ
          isplitl [Hdep Hpay Hkeep]
          · iapply rwGuard_join3 γP $$ Hdep Hpay Hkeep
          · ipureintro; rfl
      | some cid =>
          iunfold wSuccRef at Hpayload
          icases Hpayload with ⟨%child, Hptr, %d', #Hmeta, Harcc⟩
          iapply wp_load $$ Hptr
          iintro !> Hptr
          wp_pures
          ihave #Hnodec : Arr.isNode γ cid d' $$ [Hmeta]
          · unfold Arr.isNode
            iexact Hmeta
          wp_bind &Arc.downgrade _
          iapply wp_wand $$ [Hnodec Harcc]
          · iapply downgrade_child_spec γ γP platform child cid d'
              $$ Hinv' Hnodec Harcc
          iintro %w ⟨%hw, Harcc, Hweakc⟩
          subst hw
          wp_pures
          ihave Hpayload : payload γ.l d (some cid) $$ [Hptr Harcc]
          · unfold payload wSuccRef
            iexists w
            iframe Hptr
            iexists d'
            iframe Harcc
            iexact Hmeta
          wp_bind &RwLock.write_release _
          iapply wp_wand $$ [Hnode Hwguard Hcell Hpayload Hkeep]
          · iapply node_release_spec γ γP platform node id d (some cid)
              $$ Hinv' Hnode Hwguard Hcell Hpayload Hkeep
          iintro %u ⟨Hpay, Hkeep⟩
          wp_pures
          wp_bind &Arc.drop _ _
          iapply wp_wand $$ [Hnode Harc Hmine Hkeep]
          · iapply return_read_spec γ γP platform node id d
              $$ Hinv' Hnode Harc Hmine Hkeep
          iintro %u2 ⟨Hdep, Hkeep⟩
          wp_pures
          -- both deposits are back, so the whole permit is in hand: commit here
          iauopen HAU' with ⟨%σc, Hfrag, Hclose⟩
          icases Hclose with ⟨-, Hcommit⟩
          ihave Hbeta : (∃ σ', arrFrag γ σ' ∗
              getChildQ γ node id σc σ' hl_val(some(some(&w)))) $$ [Hfrag Hweak Hweakc]
          · iexists σc
            iframe Hfrag
            unfold getChildQ
            isplit
            · ipureintro; rfl
            isplitl [Hweak]
            · unfold Arr.isId
              iexists d
              iframe Hweak
              iexact Hnode
            · iright; iright
              iexists w, cid
              isplit
              · ipureintro; rfl
              unfold Arr.isId
              iexists d'
              iframe Hweakc
              iexact Hnodec
          imod Hcommit $$ Hbeta with HΦ
          imodintro
          simp only [wandM]
          iapply HΦ
          isplitl [Hdep Hpay Hkeep]
          · iapply rwGuard_join3 γP $$ Hdep Hpay Hkeep
          · ipureintro; rfl
  · iexact HAU

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
