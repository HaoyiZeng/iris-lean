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


/-! ## Resources -/

section Resources

variable {H : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H Nat]
variable [HeapLangGS hlc GF] [RwLockG GF] [ArcG GF] [ArrG GF H]

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
def arcInvBody (d : Data) : IProp GF := iprop%
  ∃ n m : Nat, arcAuth d.arc n m

instance instArcInvBodyTimeless (d : Data) :
    Timeless (arcInvBody (GF := GF) d) := by unfold arcInvBody; infer_instance

def isArcInv (d : Data) : IProp GF := inv arcN (arcInvBody d)

instance instIsArcInvPersistent (d : Data) :
    Persistent (isArcInv (GF := GF) d) := by unfold isArcInv; infer_instance

/-- The contents of a cell.  Unlike `Array` there is no revocation flag: a cell that
    has left the list has been freed, so no client can be looking at one. -/
def payload (γ : GName) (d : Data) : Option Nat → IProp GF
  | none => iprop%
      d.ptr ↦ hl_val((#d.val, none()))
  | some id => iprop%
      ∃ node : Val,
        d.ptr ↦ hl_val((#d.val, some(&node))) ∗ succRef γ node id

instance instPayloadTimeless (γ : GName) (d : Data) (nxt : Option Nat) :
    Timeless (payload (GF := GF) (H := H) γ d nxt) := by
  cases nxt <;> (unfold payload succRef; infer_instance)

/-- What a cell contributes to the list while the platform is held exclusively. -/
def nodeSlotExclusive (d : Data) (C : Qp → IProp GF) (P : IProp GF) : IProp GF := iprop%
  isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗ C 1 ∗ P

/-- The same under a platform read lock, where another reader may be part-way
    through a write on this cell.  The `rwGuardFrac` it leaves behind is what proves
    the list is quiescent again once the platform lock is released. -/
def nodeSlotSharedBody (γP : GName) (C : Qp → IProp GF) (P : IProp GF) :
    RwLock.State → IProp GF
  | .write  => iprop% rwGuardFrac γP .read q1_2
  | .read _ => iprop% False
  | .free   => iprop% C 1 ∗ P

def nodeSlotShared (γP : GName) (d : Data) (C : Qp → IProp GF) (P : IProp GF) :
    IProp GF := iprop%
  ∃ s : RwLock.State, isRwLock d.rw d.mux s hl_val(#d.ptr) ∗ nodeSlotSharedBody γP C P s

abbrev Slot (GF : BundledGFunctors) [HeapLangGS hlc GF] [ArcG GF] [ArrG GF H] :=
  Data → (Qp → IProp GF) → IProp GF → IProp GF

abbrev aliveSlot (slot : Slot (H := H) GF) (γ : GName) (d : Data) (nxt : Option Nat) :
    IProp GF :=
  slot d (fun q => cellAlive d.cell q nxt) (payload γ d nxt)

/-- The chain.  There is no companion big-op over retired cells: a cell that leaves
    the list is freed, and all that remains of it is `arcAuth _ 0 _` inside its own
    invariant. -/
def isGhostHelp (slot : Slot (H := H) GF) (γ : GName)
    (tail : Option Nat) : List (Nat × Int) → IProp GF
  | [] => iprop% emp
  | (id, x) :: cells => iprop%
      ∃ d : Data,
        ⌜x = d.val⌝ ∗ metaAt γ id d ∗ isArcInv d ∗
        aliveSlot slot γ d (nextIdOr cells tail) ∗
        isGhostHelp slot γ tail cells

def isGhost (slot : Slot (H := H) GF) (γ : GName) (cells : List (Nat × Int)) : IProp GF :=
  isGhostHelp slot γ none cells

def arrContentAt (γ : Arrγ) (M : H Data) (σ : Arr) : IProp GF := iprop%
  metaMap γ.l M ∗ ⌜σ.wellFormed⌝ ∗ ⌜∀ id, dom M id ↔ id < σ.counter⌝ ∗
  isGhost nodeSlotExclusive γ.l σ.cells

def arrContent (γ : Arrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H Data, arrContentAt γ M σ

def arrShared (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) : IProp GF := iprop%
  metaMap γ.l M ∗ ⌜σ.wellFormed⌝ ∗ ⌜∀ id, dom M id ↔ id < σ.counter⌝ ∗
  isGhost (nodeSlotShared γp) γ.l σ.cells

def isPhysical (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) :
    RwLock.State → IProp GF
  | .write  => iprop% emp
  | .read _ => iprop% arrShared γ γp M σ ∗ stateVar γ.s q3_4 σ M
  | .free   => iprop% arrContentAt γ M σ ∗ stateVar γ.s q3_4 σ M

def isPlatform (ρ : GName) (s : RwLock.State) (platform : Val) : IProp GF := iprop%
  ∃ α : GName, ∃ gate : Val, ∃ cell : Loc,
    arcHasStrong α ∗ isArc α platform gate ∗
    isRwLock ρ gate s hl_val(#cell) ∗ cell ↦ hl_val(#())

def arrInvBody (γ : Arrγ) (γp : GName) (platform : Val) : IProp GF := iprop%
  ∃ s : RwLock.State, ∃ M : H Data, ∃ σ : Arr,
    isPlatform γp s platform ∗ isPhysical γ γp M σ s

def isArrInv (γ : Arrγ) (γp : GName) (platform : Val) : IProp GF :=
  inv arrN (arrInvBody γ γp platform)

instance instIsArrInvPersistent (γ : Arrγ) (γp : GName) (platform : Val) :
    Persistent (isArrInv (GF := GF) (H := H) γ γp platform) := by
  unfold isArrInv; infer_instance

def arrFrag (γ : Arrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H Data, stateVar γ.s q1_4 σ M

/-- A list that has not been handed to a platform yet. -/
def Arr.isList (γ : Arrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H Data, arrContentAt γ M σ ∗ stateVar γ.s 1 σ M

/-- Persistent knowledge that `id` names the cell described by `d`. -/
def Arr.isNode (γ : Arrγ) (id : Nat) (d : Data) : IProp GF := iprop%
  metaAt γ.l id d ∗ isArcInv d

instance instIsNodePersistent (γ : Arrγ) (id : Nat) (d : Data) :
    Persistent (Arr.isNode (GF := GF) (H := H) γ id d) := by
  unfold Arr.isNode; infer_instance

/-- A client's handle: **weak**.  Holding one does not keep the cell alive, which is
    exactly why revocation can free it. -/
def Arr.isId (γ : Arrγ) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ d : Data, Arr.isNode γ id d ∗ isWeak d.arc node d.mux

/-- The strong reference to the root, held by whoever called `init`.  Nothing inside
    the list owns it: dropping it frees the whole list. -/
def Arr.isRoot (γ : Arrγ) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ d : Data, Arr.isNode γ id d ∗ isArc d.arc node d.mux

end

end Resources


/-! ## Specifications -/

section Specs

variable {H : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H Nat]
variable [HeapLangGS hlc GF] [RwLockG GF] [ArcG GF] [ArrG GF H]

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
      | some i => iprop% ∃ v : Val, ⌜next = hl_val(some(&v))⌝ ∗ succRef γ v i ⦄
      hl(&new #x &next)
    ⦃ node, RET node;
      ∃ d : Data,
        ⌜x = d.val⌝ ∗
        isArcInv d ∗
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
  ihave Hbody : arcInvBody ⟨γarc, γrw, γcell, l, p, x⟩ $$ [Hauth]
  · unfold arcInvBody
    iexists 1, 0
    iexact Hauth
  imod inv_alloc arcN ⊤ (arcInvBody ⟨γarc, γrw, γcell, l, p, x⟩)
    $$ Hbody with #Hinv
  imodintro
  iapply HΦ
  iexists ⟨γarc, γrw, γcell, l, p, x⟩
  isplit
  · ipureintro; rfl
  isplitl []
  · unfold isArcInv
    iexact Hinv
  iframe Harc Hlock Hcell
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
      ∃ γ : Arrγ, Arr.isList γ (Arr.init x) ∗ Arr.isRoot γ root 0 ⦄ := by
  iintro %Φ - HΦ
  iapply wp_fupd
  unfold init
  wp_pures
  imod metaMap_alloc with ⟨%γl, HM⟩
  iapply new_spec γl x hl_val(none()) none
  · ipureintro; rfl
  iintro %root !> ⟨%d, %hval, #Hinv, Harc, Hlock, Hcell, Hpay⟩
  subst hval
  imod metaMap_insert γl (∅ : H Data) 0 d (by simp [get?_empty]) $$ HM with ⟨HM, #Hat⟩
  imod stateVar_alloc (Arr.init d.val) (Std.insert (∅ : H Data) 0 d) with ⟨%γs, Hstate⟩
  imodintro
  iapply HΦ
  iexists ⟨γl, γs⟩
  isplitl [HM Hstate Hlock Hcell Hpay]
  · unfold Arr.isList arrContentAt Arr.init
    iexists (Std.insert (∅ : H Data) 0 d)
    isplitl [HM Hlock Hcell Hpay]
    · iframe HM
      isplit
      · ipureintro; exact Arr.init_wellFormed d.val
      isplit
      · ipureintro
        exact metaMap_insert_counter_dom (∅ : H Data) 0 d
          (by intro id; unfold dom; simp [get?_empty])
      · unfold isGhost isGhostHelp
        iexists d
        isplit
        · ipureintro; rfl
        iframe Hat
        isplitl []
        · unfold isArcInv
          iexact Hinv
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

omit [RwLockG GF] in
/-- Take a weak handle on a cell the caller owns outright.  No lock is involved:
    the reference counts are not under the platform lock, which is the whole point
    of putting them in their own invariant. -/
theorem handle_spec (γ : Arrγ) (node : Val) (id : Nat) :
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
  icases Hbody with ⟨%n, %m, Hauth⟩
  iaaccintro' with Hauth
  · iintro Hauth
    imodintro
    isplitl [Hauth]
    · unfold arcInvBody
      iexists n, m
      iexact Hauth
    · iframe
      repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro ⟨Hauth, Harc, Hweak⟩
    imodintro
    isplitl [Hauth]
    · unfold arcInvBody
      iexists n, (m + 1)
      iexact Hauth
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

end Specs

end Iris.Examples.HeapLang.WeakList
