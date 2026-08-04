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

def wMetaMap (γ : GName) (M : H WData) : IProp GF :=
  γ ↪●MAP M
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

instance instWMetaMapTimeless (γ : GName) (M : H WData) :
    Timeless (wMetaMap (GF := GF) γ M) := by unfold wMetaMap; infer_instance
instance instWMetaAtTimeless (γ : GName) (id : Nat) (d : WData) :
    Timeless (wMetaAt (GF := GF) γ id d) := by unfold wMetaAt; infer_instance
instance instWStateVarTimeless (γ : GName) (q : Qp) (σ : Arr) (M : H WData) :
    Timeless (wStateVar (GF := GF) γ q σ M) := by unfold wStateVar; infer_instance
instance instRefTokTimeless (d : WData) :
    Timeless (refTok (GF := GF) d) := by unfold refTok; infer_instance
instance instRefAuthTimeless (d : WData) (n : Nat) :
    Timeless (refAuth (GF := GF) d n) := by unfold refAuth; infer_instance

theorem wMetaMap_alloc : ⊢@{IProp GF} |==> ∃ γ, wMetaMap γ (∅ : H WData) := by
  unfold wMetaMap
  iapply ghost_map_alloc_empty

theorem wMetaMap_lookup (γ : GName) (M : H WData) (id : Nat) (d : WData) :
    ⊢@{IProp GF} wMetaMap γ M -∗ wMetaAt γ id d -∗
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
    ⊢@{IProp GF} wMetaMap γ M ==∗
      wMetaMap γ (Std.insert M id d) ∗ wMetaAt γ id d := by
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
    ⊢@{IProp GF} wMetaMap γ M ==∗
      wMetaMap γ (Std.insert M counter d) ∗ wMetaAt γ counter d := by
  iapply wMetaMap_insert γ M counter d (wMetaMap_counter_fresh M counter hdom)

theorem wMetaMap_lookup_lt (γ : GName) (M : H WData) (counter id : Nat) (d : WData)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    ⊢@{IProp GF} wMetaMap γ M -∗ wMetaAt γ id d -∗ ⌜id < counter⌝ := by
  iintro HM Hid
  ihave %hlookup := wMetaMap_lookup γ M id d $$ HM Hid
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

/-- Every cell's reference counts live here, in a namespace of their own.  They are
    deliberately *not* under the platform lock: duplicating a weak handle takes no
    lock at all, so `arcAuth` has to be reachable while another thread holds the
    platform exclusively.  One namespace serves every cell — no two cells' counts
    are ever needed at the same time. -/
def arcN : Namespace := ndot nroot "wlistarc"

theorem arcN_disjoint : (↑arcN : CoPset) ## (↑arrN : CoPset) :=
  ndot_ne_disjoint nroot (by decide : "wlistarc" ≠ "wlist")

/-- All that is left of a cell once every reference to it is gone: `arcAuth γ 0 m`
    owns no memory, so this survives deallocation and the invariant never has to be
    torn down.  That is what lets revocation actually free a cell. -/
def arcInvBody (d : WData) : IProp GF := iprop%
  ∃ n m : Nat, arcAuth d.arc n m ∗ refAuth d n

instance instArcInvBodyTimeless (d : WData) :
    Timeless (arcInvBody (GF := GF) d) := by unfold arcInvBody; infer_instance

def isArcInv (d : WData) : IProp GF := inv arcN (arcInvBody d)

instance instIsArcInvPersistent (d : WData) :
    Persistent (isArcInv (GF := GF) d) := by unfold isArcInv; infer_instance

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
  | .write  => iprop% rwGuardFrac γP .read q1_2
  | .read _ => iprop% False
  | .free   => iprop% C 1 ∗ P

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
        ⌜x = d.val⌝ ∗ wMetaAt γ id d ∗ isArcInv d ∗
        refTok d ∗
        aliveSlot slot γ d (nextIdOr cells tail) ∗
        isGhostHelp slot γ tail cells

def isGhost (slot : Slot (H := H) GF) (γ : GName) (cells : List (Nat × Int)) : IProp GF :=
  isGhostHelp slot γ none cells

def arrContentAt (γ : WArrγ) (M : H WData) (σ : Arr) : IProp GF := iprop%
  wMetaMap γ.l M ∗ ⌜σ.wellFormed⌝ ∗ ⌜∀ id, dom M id ↔ id < σ.counter⌝ ∗
  isGhost nodeSlotExclusive γ.l σ.cells

def arrContent (γ : WArrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H WData, arrContentAt γ M σ

def arrShared (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr) : IProp GF := iprop%
  wMetaMap γ.l M ∗ ⌜σ.wellFormed⌝ ∗ ⌜∀ id, dom M id ↔ id < σ.counter⌝ ∗
  isGhost (nodeSlotShared γp) γ.l σ.cells

def isPhysical (γ : WArrγ) (γp : GName) (M : H WData) (σ : Arr) :
    RwLock.State → IProp GF
  | .write  => iprop% emp
  | .read _ => iprop% arrShared γ γp M σ ∗ wStateVar γ.s q3_4 σ M
  | .free   => iprop% arrContentAt γ M σ ∗ wStateVar γ.s q3_4 σ M

def isPlatform (ρ : GName) (s : RwLock.State) (platform : Val) : IProp GF := iprop%
  ∃ α : GName, ∃ gate : Val, ∃ cell : Loc,
    arcHasStrong α ∗ isArc α platform gate ∗
    isRwLock ρ gate s hl_val(#cell) ∗ cell ↦ hl_val(#())

def arrInvBody (γ : WArrγ) (γp : GName) (platform : Val) : IProp GF := iprop%
  ∃ s : RwLock.State, ∃ M : H WData, ∃ σ : Arr,
    isPlatform γp s platform ∗ isPhysical γ γp M σ s

def isArrInv (γ : WArrγ) (γp : GName) (platform : Val) : IProp GF :=
  inv arrN (arrInvBody γ γp platform)

instance instIsArrInvPersistent (γ : WArrγ) (γp : GName) (platform : Val) :
    Persistent (isArrInv (GF := GF) (H := H) γ γp platform) := by
  unfold isArrInv; infer_instance

def arrFrag (γ : WArrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H WData, wStateVar γ.s q1_4 σ M

/-- A list that has not been handed to a platform yet. -/
def Arr.isList (γ : WArrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H WData, arrContentAt γ M σ ∗ wStateVar γ.s 1 σ M

/-- Persistent knowledge that `id` names the cell described by `d`. -/
def Arr.isNode (γ : WArrγ) (id : Nat) (d : WData) : IProp GF := iprop%
  wMetaAt γ.l id d ∗ isArcInv d

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
    holds the only strong reference to the new cell, and the reference-count
    invariant has been installed. -/
theorem new_spec (γ : GName) (x : Int) (next : Val) (nxt : Option Nat) :
  ⊢@{IProp GF}
    ⦃ match nxt with
      | none => iprop% ⌜next = hl_val(none())⌝
      | some i => iprop% ∃ v : Val, ⌜next = hl_val(some(&v))⌝ ∗ wSuccRef γ v i ⦄
      hl(&new #x &next)
    ⦃ node, RET node;
      ∃ d : WData,
        ⌜x = d.val⌝ ∗
        isArcInv d ∗
        isArc d.arc node d.mux ∗ refTok d ∗
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
  ihave Hbody : arcInvBody ⟨⟨γarc, γrw, γcell, l, p, x⟩, γcnt⟩ $$ [Hauth Hcnt]
  · unfold arcInvBody refAuth
    iexists 1, 0
    iframe
  imod inv_alloc arcN ⊤ (arcInvBody ⟨⟨γarc, γrw, γcell, l, p, x⟩, γcnt⟩)
    $$ Hbody with #Hinv
  imodintro
  iapply HΦ
  iexists ⟨⟨γarc, γrw, γcell, l, p, x⟩, γcnt⟩
  isplit
  · ipureintro; rfl
  isplitl []
  · unfold isArcInv
    iexact Hinv
  isplitl [Harc]
  · iexact Harc
  isplitl [Htok]
  · unfold refTok
    iexact Htok
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

theorem init_spec (x : Int) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&init #x)
    ⦃ root, RET root;
      ∃ γ : WArrγ, Arr.isList γ (Arr.init x) ∗ Arr.isRoot γ root 0 ⦄ := by
  iintro %Φ - HΦ
  iapply wp_fupd
  unfold init
  wp_pures
  imod wMetaMap_alloc with ⟨%γl, HM⟩
  iapply new_spec γl x hl_val(none()) none
  · ipureintro; rfl
  iintro %root !> ⟨%d, %hval, #Hinv, Harc, Htok, Hlock, Hcell, Hpay⟩
  subst hval
  imod wMetaMap_insert γl (∅ : H WData) 0 d (by simp [get?_empty]) $$ HM with ⟨HM, #Hat⟩
  imod wStateVar_alloc (Arr.init d.val) (Std.insert (∅ : H WData) 0 d) with ⟨%γs, Hstate⟩
  imodintro
  iapply HΦ
  iexists ⟨γl, γs⟩
  isplitl [HM Hstate Htok Hlock Hcell Hpay]
  · unfold Arr.isList arrContentAt Arr.init
    iexists (Std.insert (∅ : H WData) 0 d)
    isplitl [HM Htok Hlock Hcell Hpay]
    · iframe HM
      isplit
      · ipureintro; exact Arr.init_wellFormed d.val
      isplit
      · ipureintro
        exact wMetaMap_insert_counter_dom (∅ : H WData) 0 d
          (by intro id; unfold dom; simp [get?_empty])
      · unfold isGhost isGhostHelp
        iexists d
        isplit
        · ipureintro; rfl
        iframe Hat
        isplitl []
        · unfold isArcInv
          iexact Hinv
        isplitl [Htok]
        · iexact Htok
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
    isplitl []
    · iexact Hat
    · unfold isArcInv
      iexact Hinv

omit [RwLockG GF] [ArrG GF H] in
/-- Take a weak handle on a cell the caller owns outright.  No lock is involved:
    the reference counts are not under the platform lock, which is the whole point
    of putting them in their own invariant. -/
theorem handle_spec (γ : WArrγ) (node : Val) (id : Nat) :
  ⊢@{IProp GF}
    ⦃ Arr.isRoot γ node id ⦄
      hl(&handle &node)
    ⦃ w, RET w;
      Arr.isRoot γ node id ∗ Arr.isId γ w id ⦄ := by
  iintro %Φ Hroot HΦ
  iunfold Arr.isRoot at Hroot
  icases Hroot with ⟨%d, #Hnode, Harc⟩
  ihave #Hinv : isArcInv d $$ [Hnode]
  · iunfold Arr.isNode at Hnode
    icases Hnode with ⟨-, Hinv⟩
    iexact Hinv
  unfold handle
  wp_pures
  iapply Arc.downgrade_spec (γ := d.arc) node d.mux $$ Harc
  iunfold isArcInv at Hinv
  iauintro
  iinv Hinv as Hbody
  iunfold arcInvBody at Hbody
  icases Hbody with ⟨%n, %m, Hauth, Hcnt⟩
  iaaccintro' with Hauth
  · iintro Hauth
    imodintro
    isplitl [Hauth Hcnt]
    · unfold arcInvBody
      iexists n, m
      iframe
    · iframe
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro ⟨Hauth, Harc, Hweak⟩
    imodintro
    isplitl [Hauth Hcnt]
    · unfold arcInvBody
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
  sorry

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
    under it. -/
theorem isId_clone_spec (γ : WArrγ) (node : Val) (id : Nat) :
  ⊢@{IProp GF}
    ⦃ Arr.isId γ node id ⦄
      hl(&Weak.clone &node)
    ⦃ w, RET w;
      ⌜w = node⌝ ∗ Arr.isId γ node id ∗ Arr.isId γ w id ⦄ := by
  sorry

end Atomic

end Specs

end Iris.Examples.HeapLang.WeakList
