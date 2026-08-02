module

public import Iris.Examples.SafeAPI
public import Iris.ProgramLogic.Atomic
public import Iris.HeapLang.Lib.IInv
public import Iris.HeapLang.Lib.FracAgreeLocal

@[expose] public section
namespace Iris.Examples.HeapLang

structure Arr where
  cells : List (Nat × Int)
  counter : Nat
deriving DecidableEq, Repr

instance : OFE Arr := OFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Arr := ⟨fun h => h⟩
instance : OFE.Leibniz Arr := ⟨fun h => h⟩

def Arr.idUqi (arr : Arr) : Prop := (arr.cells.map (·.1)).Nodup

structure Arr.wellFormed (arr : Arr) : Prop where
  idUqi : arr.idUqi
  counterFresh : ∀ p ∈ arr.cells, p.1 < arr.counter

def Arr.init (x : Int) : Arr := { cells := [(0, x)], counter := 1 }

def Arr.insert (arr : Arr) (id : Nat) (val : Int) : Arr × Option Nat :=
  if arr.cells.any (·.1 = id)
    then ({
      cells := arr.cells.flatMap λ c => if c.1 = id then [c, (arr.counter, val)] else [c],
      counter := arr.counter + 1
    }, some arr.counter)
    else (arr, none)

def Arr.cellsBefore (cells : List (Nat × Int)) (id : Nat) : List (Nat × Int) :=
  match cells with
  | [] => []
  | (id', x) :: cs =>
    if id' = id
      then [(id', x)]
      else (id', x) :: Arr.cellsBefore cs id

def Arr.revoke (arr : Arr) (id : Nat) : Arr × Option Unit :=
  if arr.cells.any (·.1 = id)
    then ({
      cells := Arr.cellsBefore arr.cells id,
      counter := arr.counter
    }, some ())
    else (arr, none)

section Facts


def Arr.insertBody (id counter : Nat) (val : Int) : (Nat × Int) → List (Nat × Int) :=
  fun c => if c.1 = id then [c, (counter, val)] else [c]

theorem Arr.flatMap_no_match (id counter : Nat) (val : Int) (cs : List (Nat × Int))
    (hne : ∀ x ∈ cs, x.1 ≠ id) :
    cs.flatMap (Arr.insertBody id counter val) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons]
    have hc : Arr.insertBody id counter val c = [c] := by
      unfold Arr.insertBody; rw [if_neg (hne c (by simp))]
    rw [hc, ih (fun x hx => hne x (by simp [hx]))]
    rfl

theorem Arr.mem_ids_flatMap (id counter : Nat) (val : Int) (cs : List (Nat × Int)) (x : Nat)
    (hx : x ∈ (cs.flatMap (Arr.insertBody id counter val)).map (·.1)) :
    x ∈ cs.map (·.1) ∨ x = counter := by
  rw [List.mem_map] at hx
  obtain ⟨p, hp, hpx⟩ := hx
  rw [List.mem_flatMap] at hp
  obtain ⟨d, hd, hpd⟩ := hp
  unfold Arr.insertBody at hpd
  by_cases hdi : d.1 = id
  · rw [if_pos hdi, List.mem_cons, List.mem_singleton] at hpd
    rcases hpd with rfl | rfl
    · left; exact List.mem_map.mpr ⟨_, hd, hpx⟩
    · right; exact hpx.symm
  · rw [if_neg hdi, List.mem_singleton] at hpd
    subst hpd
    left; exact List.mem_map.mpr ⟨_, hd, hpx⟩

theorem Arr.nodup_insert_ids (id counter : Nat) (val : Int) :
    ∀ (cells : List (Nat × Int)),
      (cells.map (·.1)).Nodup →
      (∀ p ∈ cells, p.1 < counter) →
      ((cells.flatMap (Arr.insertBody id counter val)).map (·.1)).Nodup := by
  intro cells
  induction cells with
  | nil => intro _ _; simp
  | cons c cs ih =>
    intro hnd hlt
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hcnotin, hndcs⟩ := hnd
    have hclt : c.1 < counter := hlt c (by simp)
    have hltcs : ∀ p ∈ cs, p.1 < counter := fun p hp => hlt p (by simp [hp])
    rw [List.flatMap_cons, List.map_append, List.nodup_append]
    by_cases hci : c.1 = id
    · have hne : ∀ x ∈ cs, x.1 ≠ id := by
        intro x hx heq
        exact hcnotin (List.mem_map.mpr ⟨x, hx, by rw [heq, ← hci]⟩)
      rw [Arr.flatMap_no_match id counter val cs hne]
      have hgc : Arr.insertBody id counter val c = [c, (counter, val)] := by
        unfold Arr.insertBody; rw [if_pos hci]
      rw [hgc]
      refine ⟨?_, hndcs, ?_⟩
      · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
          List.not_mem_nil, or_false, List.nodup_nil, and_true]
        exact ⟨Nat.ne_of_lt hclt, not_false⟩
      · intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at ha
        obtain ⟨q, hq, hqb⟩ := List.mem_map.mp hb
        have hqlt := hltcs q hq
        rcases ha with rfl | rfl
        · intro heq; subst heq; exact hcnotin hb
        · intro heq; rw [← hqb] at heq; omega
    · have hgc : Arr.insertBody id counter val c = [c] := by
        unfold Arr.insertBody; rw [if_neg hci]
      rw [hgc]
      refine ⟨by simp, ih hndcs hltcs, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at ha
      subst ha
      rcases Arr.mem_ids_flatMap id counter val cs b hb with hbcs | rfl
      · intro heq; subst heq; exact hcnotin hbcs
      · intro heq; omega

theorem Arr.exists_split_id {cells : List (Nat × Int)} {id : Nat}
    (hmem : id ∈ cells.map (·.1)) :
    ∃ pre x post, cells = pre ++ (id, x) :: post := by
  induction cells with
  | nil => simp at hmem
  | cons c cells ih =>
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with h | h
      · rcases c with ⟨cid, x⟩
        dsimp only at h
        subst cid
        exact ⟨[], x, cells, rfl⟩
      · obtain ⟨pre, x, post, rfl⟩ := ih h
        exact ⟨c :: pre, x, post, rfl⟩

theorem Arr.nodup_split_id (pre post : List (Nat × Int)) (id : Nat) (x : Int)
    (hnd : ((pre ++ (id, x) :: post).map (·.1)).Nodup) :
    (∀ p ∈ pre, p.1 ≠ id) ∧ (∀ p ∈ post, p.1 ≠ id) := by
  rw [List.map_append, List.map_cons, List.nodup_append] at hnd
  obtain ⟨-, hrest, hdisj⟩ := hnd
  rw [List.nodup_cons] at hrest
  obtain ⟨hidpost, -⟩ := hrest
  constructor
  · intro p hp heq
    exact hdisj p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩) id
      (List.mem_cons_self) heq
  · intro p hp heq
    apply hidpost
    rw [← heq]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem Arr.flatMap_insert_split (pre post : List (Nat × Int))
    (id counter : Nat) (x val : Int)
    (hpre : ∀ p ∈ pre, p.1 ≠ id) (hpost : ∀ p ∈ post, p.1 ≠ id) :
    (pre ++ (id, x) :: post).flatMap (Arr.insertBody id counter val) =
      pre ++ (id, x) :: (counter, val) :: post := by
  rw [List.flatMap_append, Arr.flatMap_no_match id counter val pre hpre]
  rw [List.flatMap_cons,
    show Arr.insertBody id counter val (id, x) = [(id, x), (counter, val)] by
      simp [Arr.insertBody],
    Arr.flatMap_no_match id counter val post hpost]
  rfl

theorem Arr.cellsBefore_split (pre post : List (Nat × Int)) (id : Nat) (x : Int)
    (hpre : ∀ p ∈ pre, p.1 ≠ id) :
    Arr.cellsBefore (pre ++ (id, x) :: post) id = pre ++ [(id, x)] := by
  induction pre with
  | nil => simp [Arr.cellsBefore]
  | cons p pre ih =>
      simp only [List.cons_append, Arr.cellsBefore]
      rw [if_neg (hpre p List.mem_cons_self)]
      rw [ih (fun q hq => hpre q (List.mem_cons_of_mem p hq))]

theorem Arr.insert_eq_of_split (arr : Arr) (pre post : List (Nat × Int))
    (id : Nat) (x val : Int) (hcells : arr.cells = pre ++ (id, x) :: post)
    (hpre : ∀ p ∈ pre, p.1 ≠ id) (hpost : ∀ p ∈ post, p.1 ≠ id) :
    Arr.insert arr id val =
      ({ cells := pre ++ (id, x) :: (arr.counter, val) :: post,
         counter := arr.counter + 1 }, some arr.counter) := by
  unfold Arr.insert
  have hany : arr.cells.any (·.1 = id) = true := by
    rw [List.any_eq_true]
    exact ⟨(id, x), hcells ▸ (by simp), by simp⟩
  simp only [hany, ↓reduceIte]
  rw [hcells]
  congr 1
  rw [Arr.mk.injEq]
  constructor
  · exact Arr.flatMap_insert_split pre post id arr.counter x val hpre hpost
  · rfl

theorem Arr.insert_eq_none (arr : Arr) (id : Nat) (val : Int)
    (hnot : id ∉ arr.cells.map (·.1)) :
    Arr.insert arr id val = (arr, none) := by
  unfold Arr.insert
  have hany : arr.cells.any (·.1 = id) = false := by
    rw [List.any_eq_false]
    intro p hp heq
    apply hnot
    exact List.mem_map.mpr ⟨p, hp, by simpa using heq⟩
  simp [hany]

theorem Arr.revoke_eq_of_split (arr : Arr) (pre post : List (Nat × Int))
    (id : Nat) (x : Int) (hcells : arr.cells = pre ++ (id, x) :: post)
    (hpre : ∀ p ∈ pre, p.1 ≠ id) :
    Arr.revoke arr id =
      ({ cells := pre ++ [(id, x)], counter := arr.counter }, some ()) := by
  unfold Arr.revoke
  have hany : arr.cells.any (·.1 = id) = true := by
    rw [List.any_eq_true]
    exact ⟨(id, x), hcells ▸ (by simp), by simp⟩
  simp only [hany, ↓reduceIte]
  rw [hcells]
  congr 1
  rw [Arr.mk.injEq]
  constructor
  · exact Arr.cellsBefore_split pre post id x hpre
  · rfl

theorem Arr.revoke_eq_none (arr : Arr) (id : Nat)
    (hnot : id ∉ arr.cells.map (·.1)) :
    Arr.revoke arr id = (arr, none) := by
  unfold Arr.revoke
  have hany : arr.cells.any (·.1 = id) = false := by
    rw [List.any_eq_false]
    intro p hp heq
    apply hnot
    exact List.mem_map.mpr ⟨p, hp, by simpa using heq⟩
  simp [hany]

def Arr.init_wellFormed (x : Int) : Arr.wellFormed <| Arr.init x := {
  idUqi := by simp [Arr.init, Arr.idUqi]
  counterFresh := by simp [Arr.init]
}

def Arr.insert_wellFormed (arr : Arr) (h : arr.wellFormed) (id : Nat) (val : Int) :
    (Arr.insert arr id val).1.wellFormed := {
  idUqi := by
    unfold Arr.insert Arr.idUqi
    split
    · show ((arr.cells.flatMap (Arr.insertBody id arr.counter val)).map (·.1)).Nodup
      exact Arr.nodup_insert_ids id arr.counter val arr.cells h.idUqi h.counterFresh
    · exact h.idUqi
  counterFresh := by
    unfold Arr.insert
    split
    · dsimp only
      intro p hp
      rw [List.mem_flatMap] at hp
      obtain ⟨c, hc, hpc⟩ := hp
      by_cases hci : c.1 = id
      · rw [if_pos hci, List.mem_cons, List.mem_singleton] at hpc
        rcases hpc with rfl | rfl
        · have := h.counterFresh _ hc; omega
        · exact Nat.lt_succ_self _
      · rw [if_neg hci, List.mem_singleton] at hpc
        subst hpc
        have := h.counterFresh _ hc; omega
    · exact h.counterFresh
}

theorem Arr.cellsBefore_sublist (cells : List (Nat × Int)) (id : Nat) :
    (Arr.cellsBefore cells id).Sublist cells := by
  induction cells with
  | nil => exact .slnil
  | cons c cells ih =>
      simp only [Arr.cellsBefore]
      split
      · exact .cons_cons c (List.nil_sublist cells)
      · exact .cons_cons c ih

def Arr.revoke_wellFormed (arr : Arr) (h : arr.wellFormed) (id : Nat) :
    (Arr.revoke arr id).1.wellFormed := by
  unfold Arr.revoke
  split
  · constructor
    · unfold Arr.idUqi
      exact ((Arr.cellsBefore_sublist arr.cells id).map
        (fun p : Nat × Int => p.1)).nodup h.idUqi
    · intro p hp
      exact h.counterFresh p
        (List.Sublist.mem hp (Arr.cellsBefore_sublist arr.cells id))
  · exact h

end Facts

open Iris.HeapLang

def Impl.platformNew : Val := hl_val%
  λ _,
    let cell := ref(#());
    let lock := &RwLock.new cell;
    &Arc.new lock

def Impl.execute : Val := hl_val%
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

def Impl.new : Val := hl_val%
  λ value next,
    let contents := ref((#false, (value, next)));
    let lock := &RwLock.new contents;
    &Arc.new lock

def Impl.init : Val := hl_val%
  λ value, &new value (none())

def Impl.insert : Val := hl_val%
  λ platform node value,
    &execute platform #false (λ _,
      let lock := &Arc.get(node); -- using isId and metaPointsTo
      /- `RwLockGuard γP read` -/
      let ptr := &RwLock.write_acquire(lock); -- access to atomic precondition to get the slot
      /- `RwLockGuard γP read ∗ metaPointsTo id d ∗ isArr` gives me `PhysicalSlot id d`  -/
      let contents := !ptr; -- unnfold the slot to get the payload
      /- unfold `PhysicalSlot id d` -/
      let revoked := fst(contents);
      let payload := snd(contents);
      let oldValue := fst(payload);
      let oldNext := snd(payload);
      if revoked then -- in this case, we are done
        /- easy case because we don't have to update the abstract state -/
        /- return `PhysicalSlot id d` to release the lock and get the `RwLockGuard γP read` back to unlock the platform -/
        (&RwLock.write_release(lock); -- access to atomic precondition to release the slot
         none())
      else
        (let newNode := &new value oldNext; -- create a new node with the value and the cloned arc
        /- create a new node, what would be the spec of new? do we assign any resources to next... -/
         let edge := &Arc.clone(newNode); -- clone the arc from the new node to create an edge
        /- copy the new node -/
         ptr ← (#false, (oldValue, some(edge))); -- update the physical payload!!
         &RwLock.write_release(lock); -- LINEARIZATION POINT
        /-
         At this point we need to update the abstract state
         we have updated the physical state
         basically now we have a different `PhysicalSlot id d` because the payload has changed
         and we also have a new `PhysicalSlot counter d'` for the new node
         emm, to make things easier, we should separate the physical resources from the abstract resources here,
         so that we can update the physical resources without having to update the abstract resources

         then we access to the atomic precondition
         the we get `isGhost(σ)` and `isPhysical(M)`
         as we hold `metaPointsTo id p`
         HOW CAN we know that `σ.cells` contains `id`, does it matter?
         now we perform an insert to the `M`
         it's easy to make `isPhysical(M')` work
         then we need to looks at the `isGhost(σ)`
         okk, seems like it's easy to proof `isGhost(σ) ∗ metaPointsTo σ.counter d ⊢ isGhost(σ.insert(d.value))`
         if we define `isGhost(σ)` as recursively over the `σ.cells` list, and
         interpret each cell to a `MetaPointsTo`

         IN THIS WAY, SEEMS LIKE TWP THINGS I HAVE FORGET
         1. i don't know if a node is alive
         2. i don't what is the next node
        -/
         some(newNode)))

def Impl.revokeSuffix : Val := hl_val%
  rec go current :=
    match current with
    | none() => #()
    | some(node) =>
      let lock := &Arc.get(node);
      let ptr := &RwLock.write_acquire(lock);
      let contents := !ptr;
      let payload := snd(contents);
      let value := fst(payload);
      let next := snd(payload);
      ptr ← (#true, (value, none()));
      &RwLock.write_release(lock);
      go next;
      &Arc.drop &RwLock.drop node

def Impl.revoke : Val := hl_val%
  λ platform node,
    &execute platform #true (λ _,
      let lock := &Arc.get(node);
      let ptr := &RwLock.write_acquire(lock);
      let contents := !ptr;
      let revoked := fst(contents);
      let payload := snd(contents);
      let value := fst(payload);
      let next := snd(payload);
      if revoked then
        (&RwLock.write_release(lock);
         none())
      else
        (ptr ← (#false, (value, none()));
         &RwLock.write_release(lock);
         &revokeSuffix next;
         some(#())))


section Specs

open Std PartialMap FracAgree

structure Data where
  arc : GName
  rw : GName
  cell : GName
  mux : Val
  ptr : Loc
  val : Int
deriving DecidableEq, Repr

/-- The synchronised ghost state: the abstract array **together with** the metadata
    map.  Pinning both under one fraction is what lets a writer that stepped outside
    the invariant (holding `3/4`) prove on the way back in that neither `σ` nor `M`
    moved.  `σ` alone would not be enough: `retiredNodes` is a big-op over `M`, so a
    silently grown `M` would leave the writer unable to restore the invariant. -/
structure ArrState (H : Type → Type) where
  arr : Arr
  mmap : H Data

instance : OFE (ArrState H) := OFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete (ArrState H) := ⟨fun h => h⟩
instance : OFE.Leibniz (ArrState H) := ⟨fun h => h⟩

abbrev ArrStateRF (H : Type → Type) : COFE.OFunctorPre :=
  constOF (DFracAgreeR (ArrState H))

inductive Cell where
  | alive : Option Nat → Cell
  | dead : Cell
  deriving DecidableEq, Repr

instance : OFE Cell := OFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Cell := ⟨fun h => h⟩
instance : OFE.Leibniz Cell := ⟨fun h => h⟩

abbrev CellRF : COFE.OFunctorPre :=
  constOF (DFracAgreeR Cell)

class ArrG (GF : BundledGFunctors) (H : outParam <| Type → Type) [LawfulFiniteMap H Nat] where
  [metaMapG : GhostMapG GF Nat Data H]
  [fracStateG : ElemG GF (ArrStateRF H)]
  [cellG : ElemG GF CellRF]

/-- The ghost names owned by the array itself.

    The platform lock's name is deliberately **not** a field: an array is created
    (`Impl.init`) before it is bound to a platform (`Impl.platformNew`), so that
    name is still universally quantified in `Arr.isList` and only gets fixed by
    `Arr.isArr`.  Bundling it here would force `isList` to guess it. -/
structure Arrγ where
  /-- Metadata map: `id ↦ Data` (per-node arc / rwlock / cell names). -/
  l : GName
  /-- Synchronisation variable pinning `(σ, M)` under one fraction. -/
  s : GName


attribute [reducible, instance] ArrG.metaMapG ArrG.fracStateG ArrG.cellG
open Iris.BI

section RA
variable [LawfulFiniteMap H Nat] [ArrG GF H]

def metaMap (γ : GName) (M : H Data) : IProp GF :=
  γ ↪●MAP M
def metaAt (γ : GName) (id : Nat) (d : Data) : IProp GF :=
  γ ↪◯MAP[id]{.discard} d

def stateVar (γ : GName) (q : Qp) (σ : Arr) (M : H Data) : IProp GF :=
  iOwn γ (F := ArrStateRF H) (FracAgree.Frac.mk q ⟨σ, M⟩)

def cellAlive (γ : GName) (q : Qp) (nxt : Option Nat) : IProp GF :=
  iOwn γ (F := CellRF) (FracAgree.mk (.own q) (Cell.alive nxt))
def cellDead (γ : GName) : IProp GF :=
  iOwn γ (F := CellRF) (FracAgree.mk .discard Cell.dead)

/-! ### Timelessness

Every resource in the array lives in a discrete camera or is a `↦`, so the whole
thing is timeless.  This is what lets `aacc_inv` open the array invariant without
leaving a `▷` behind. -/

instance instMetaMapTimeless (γ : GName) (M : H Data) :
    Timeless (metaMap (GF := GF) γ M) := by unfold metaMap; infer_instance
instance instMetaAtTimeless (γ : GName) (id : Nat) (d : Data) :
    Timeless (metaAt (GF := GF) γ id d) := by unfold metaAt; infer_instance
instance instStateVarTimeless (γ : GName) (q : Qp) (σ : Arr) (M : H Data) :
    Timeless (stateVar (GF := GF) γ q σ M) := by unfold stateVar; infer_instance
instance instCellAliveTimeless (γ : GName) (q : Qp) (nxt : Option Nat) :
    Timeless (cellAlive (GF := GF) γ q nxt) := by unfold cellAlive; infer_instance
instance instCellDeadTimeless (γ : GName) :
    Timeless (cellDead (GF := GF) γ) := by unfold cellDead; infer_instance

def q1_4 : Qp := Qp.half (Qp.half 1)
def q3_4 : Qp := Qp.half 1 + Qp.half (Qp.half 1)
def q1_2 : Qp := Qp.half 1

section Facts
theorem metaMap_alloc : ⊢@{IProp GF} |==> ∃ γ, metaMap γ (∅ : H Data) := by
  unfold metaMap
  iapply ghost_map_alloc_empty

theorem metaMap_lookup (γ : GName) (M : H Data) (id : Nat) (d : Data) :
    ⊢@{IProp GF} metaMap γ M -∗ metaAt γ id d -∗
      ⌜get? M id = some d⌝ := by
  unfold metaMap metaAt
  iapply ghost_map_lookup

/-- `metaAt` uses the `.discard` fraction, so it is persistent — but `metaAt` is a
    `def`, which instance resolution cannot see through, so the instance has to be
    restated here (same situation as `cellDead_persistent`). -/
instance metaAt_persistent (γ : GName) (id : Nat) (d : Data) :
    Persistent (metaAt (GF := GF) (H := H) γ id d) := by
  unfold metaAt; infer_instance

theorem metaAt_agree (γ : GName) (id : Nat) (d₁ d₂ : Data) :
    ⊢@{IProp GF} metaAt γ id d₁ -∗ metaAt γ id d₂ -∗ ⌜d₁ = d₂⌝ := by
  unfold metaAt
  iintro H₁ H₂
  iapply ghost_map_elem_agree
  iframe

theorem metaMap_insert (γ : GName) (M : H Data) (id : Nat) (d : Data)
    (fresh : get? M id = none) :
    ⊢@{IProp GF} metaMap γ M ==∗
      metaMap γ (insert M id d) ∗ metaAt γ id d := by
  unfold metaMap metaAt
  iapply ghost_map_insert_persist id d fresh

theorem metaMap_counter_fresh (M : H Data) (counter : Nat)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    get? M counter = none := by
  apply Option.not_isSome_iff_eq_none.mp
  intro hmem
  exact (Nat.lt_irrefl counter) ((hdom counter).mp hmem)

theorem metaMap_insert_counter_dom (M : H Data) (counter : Nat) (d : Data)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    ∀ id, dom (insert M counter d) id ↔ id < counter + 1 := by
  intro id
  unfold dom
  by_cases h : counter = id
  · subst id
    simp [get?_insert_eq rfl]
  · rw [get?_insert_ne h]
    change dom M id ↔ _
    rw [hdom]
    omega

theorem metaMap_insert_counter (γ : GName) (M : H Data) (counter : Nat) (d : Data)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    ⊢@{IProp GF} metaMap γ M ==∗
      metaMap γ (insert M counter d) ∗ metaAt γ counter d := by
  iapply metaMap_insert γ M counter d (metaMap_counter_fresh M counter hdom)

theorem metaMap_lookup_lt (γ : GName) (M : H Data) (counter id : Nat) (d : Data)
    (hdom : ∀ id, dom M id ↔ id < counter) :
    ⊢@{IProp GF} metaMap γ M -∗ metaAt γ id d -∗ ⌜id < counter⌝ := by
  iintro HM Hid
  ihave %hlookup := metaMap_lookup γ M id d $$ HM Hid
  ipureintro
  exact (hdom id).mp (by simp [dom, hlookup])

theorem q1_4_add_q3_4 : q1_4 + q3_4 = 1 := by
  unfold q1_4 q3_4 Qp.half; apply Subtype.ext; native_decide

theorem q1_2_add_q1_2 : q1_2 + q1_2 = 1 := by
  unfold q1_2 Qp.half; apply Subtype.ext; native_decide

instance cellDead_persistent (γ : GName) : Persistent (cellDead (GF := GF) γ) := by
  unfold cellDead FracAgree.mk; infer_instance

/-- Two live witnesses for the same cell must agree on the successor. -/
theorem cellAlive_agree (γ : GName) (q₁ q₂ : Qp) (n₁ n₂ : Option Nat) :
    cellAlive (GF := GF) γ q₁ n₁ ∗ cellAlive γ q₂ n₂ ⊢ ⌜n₁ = n₂⌝ := by
  unfold cellAlive
  iintro ⟨H₁, H₂⟩
  ihave H := iOwn_cmraValid_op $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete  $$ H with %Hvalid
  ipureintro
  have H := (FracAgree.op_valid_L.mp Hvalid).2
  apply (Cell.alive.inj H)

/-- A live witness and the retirement witness cannot coexist, at any fraction.
    This is the lemma that closes the `retiredSlot` case of `insert`'s positive
    branch and the `nodeSlotShared` case of its negative branch. -/
theorem cellAlive_dead_False (γ : GName) (q : Qp) (n : Option Nat) :
    cellAlive (GF := GF) γ q n ∗ cellDead γ ⊢ False := by
  unfold cellAlive cellDead
  iintro ⟨H₁, H₂⟩
  ihave H := iOwn_cmraValid_op $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete $$ H with %Hvalid
  ipureintro
  exact absurd (FracAgree.op_valid_L.mp Hvalid).2 (by simp)

/-- The `1/4` (invariant side) / `3/4` (payload side) split. -/
theorem cellAlive_split (γ : GName) (n : Option Nat) :
    cellAlive (GF := GF) γ 1 n ⊣⊢ cellAlive γ q1_4 n ∗ cellAlive γ q3_4 n := by
  unfold cellAlive
  have h : (FracAgree.mk (DFrac.own (1 : Qp)) (Cell.alive n) : DFracAgreeR Cell)
      = FracAgree.mk (DFrac.own q1_4) (Cell.alive n)
        • FracAgree.mk (DFrac.own q3_4) (Cell.alive n) := by
    rw [show DFrac.own (1 : Qp) = DFrac.own q1_4 • DFrac.own q3_4 from
      congrArg _ q1_4_add_q3_4.symm]
    exact FracAgree.mk_op.to_eq
  rw [h]; exact iOwn_op

/-- Full ownership can be retargeted at will. -/
theorem cellAlive_full_update (γ : GName) (n n' : Option Nat) :
    cellAlive (GF := GF) γ 1 n ⊢ |==> cellAlive γ 1 n' := by
  unfold cellAlive
  exact iOwn_update (Update.exclusive ⟨DFrac.valid_own_one, Agree.toAgree_valid⟩)

/-- Retiring: full ownership collapses to the persistent dead witness. -/
theorem cellAlive_full_kill (γ : GName) (n : Option Nat) :
    cellAlive (GF := GF) γ 1 n ⊢ |==> cellDead γ := by
  unfold cellAlive cellDead
  exact iOwn_update (Update.exclusive ⟨DFrac.valid_discard, Agree.toAgree_valid⟩)

/-- Rewiring the successor needs the full fraction, i.e. both halves. -/
theorem cellAlive_update (γ : GName) (n n' : Option Nat) :
    cellAlive (GF := GF) γ q1_4 n ∗ cellAlive γ q3_4 n ⊢
      |==> (cellAlive γ q1_4 n' ∗ cellAlive γ q3_4 n') :=
  (cellAlive_split γ n).mpr.trans
    ((cellAlive_full_update γ n n').trans (bupd_mono (cellAlive_split γ n').mp))

/-- Retiring a cell also needs the full fraction; the result is persistent. -/
theorem cellAlive_kill (γ : GName) (n : Option Nat) :
    cellAlive (GF := GF) γ q1_4 n ∗ cellAlive γ q3_4 n ⊢ |==> cellDead γ :=
  (cellAlive_split γ n).mpr.trans (cellAlive_full_kill γ n)

theorem cellAlive_alloc (n : Option Nat) :
    ⊢@{IProp GF} |==> ∃ γ, cellAlive γ 1 n := by
  unfold cellAlive
  exact iOwn_alloc (F := CellRF) _ ⟨DFrac.valid_own_one, Agree.toAgree_valid⟩


theorem stateVar_agree (γ : GName) (q₁ q₂ : Qp) (σ₁ σ₂ : Arr) (M₁ M₂ : H Data) :
    stateVar (GF := GF) γ q₁ σ₁ M₁ ∗ stateVar γ q₂ σ₂ M₂ ⊢ ⌜σ₁ = σ₂ ∧ M₁ = M₂⌝ := by
  unfold stateVar
  iintro ⟨H₁, H₂⟩
  ihave H := iOwn_cmraValid_op $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete $$ H with %Hvalid
  ipureintro
  have H := (FracAgree.Frac.op_valid_L.mp Hvalid).2
  exact ⟨congrArg ArrState.arr H, congrArg ArrState.mmap H⟩


/-- Two shares can only coexist if they fit inside one whole.  This is what makes
    the writer's `3/4` receipt incompatible with the `3/4` the invariant keeps while
    the platform lock is *not* write-held. -/
theorem stateVar_frac_valid (γ : GName) (q₁ q₂ : Qp) (σ₁ σ₂ : Arr) (M₁ M₂ : H Data) :
    stateVar (GF := GF) γ q₁ σ₁ M₁ ∗ stateVar γ q₂ σ₂ M₂ ⊢ ⌜(q₁ + q₂).val ≤ 1⌝ := by
  unfold stateVar
  iintro ⟨H₁, H₂⟩
  ihave H := iOwn_cmraValid_op $$ [H₁ H₂]
  · isplitl [H₁] <;> iassumption
  icases internalCmraValid_discrete $$ H with %Hvalid
  ipureintro
  exact (FracAgree.Frac.op_valid_L.mp Hvalid).1

theorem q3_4_add_q3_4_invalid : ¬ ((q3_4 + q3_4).val ≤ 1) := by
  unfold q3_4 Qp.half
  native_decide

/-- The `1/4` (invariant side) / `3/4` (writer side) split, mirroring `cellAlive`. -/
theorem stateVar_split (γ : GName) (σ : Arr) (M : H Data) :
    stateVar (GF := GF) γ 1 σ M ⊣⊢ stateVar γ q1_4 σ M ∗ stateVar γ q3_4 σ M := by
  unfold stateVar
  have h : (FracAgree.Frac.mk (1 : Qp) (⟨σ, M⟩ : ArrState H) : DFracAgreeR (ArrState H))
      = FracAgree.Frac.mk q1_4 (⟨σ, M⟩ : ArrState H)
        • FracAgree.Frac.mk q3_4 (⟨σ, M⟩ : ArrState H) := by
    rw [← q1_4_add_q3_4]; exact FracAgree.Frac.mk_op.to_eq
  rw [h]; exact iOwn_op

theorem stateVar_full_update (γ : GName) (σ σ' : Arr) (M M' : H Data) :
    stateVar (GF := GF) γ 1 σ M ⊢ |==> stateVar γ 1 σ' M' := by
  unfold stateVar FracAgree.Frac.mk
  exact iOwn_update (Update.exclusive ⟨DFrac.valid_own_one, Agree.toAgree_valid⟩)


theorem stateVar_alloc (σ : Arr) (M : H Data) :
    ⊢@{IProp GF} |==> ∃ γ, stateVar γ 1 σ M := by
  unfold stateVar FracAgree.Frac.mk
  exact iOwn_alloc (F := ArrStateRF H) _ ⟨DFrac.valid_own_one, Agree.toAgree_valid⟩
end Facts

end RA

variable {GF : BundledGFunctors} [LawfulFiniteMap H Nat]
variable [HeapLangGS hlc GF] [RwLockG GF] [ArcG GF] [ArrG GF H]

noncomputable section Resources

omit [ArcG GF] in
/-- Halve a platform read permit: one half is parked in the node slot, the other
    stays with the thread so it can keep proving the platform lock is read-held. -/
theorem rwGuardHalve (γ : GName) :
    ⊢@{IProp GF} rwGuard γ .read -∗ rwGuardFrac γ .read q1_2 ∗ rwGuardFrac γ .read q1_2 := by
  iintro H
  iapply (RwLock.rwGuardFrac_split γ .read q1_2 q1_2).mp
  rw [q1_2_add_q1_2, ← rwGuard_eq γ .read]
  iexact H

omit [ArcG GF] in
/-- …and put the two halves back together. -/
theorem rwGuardUnhalve (γ : GName) :
    ⊢@{IProp GF} rwGuardFrac γ .read q1_2 -∗ rwGuardFrac γ .read q1_2 -∗ rwGuard γ .read := by
  iintro H₁ H₂
  rw [rwGuard_eq γ .read, ← q1_2_add_q1_2]
  iapply (RwLock.rwGuardFrac_split γ .read q1_2 q1_2).mpr
  iframe

def arcHasStrong (γ : GName) : IProp GF := iprop%
  ∃ n w : Nat, arcAuth γ n w ∗ ⌜n > 0⌝

def arcNoStrong (γ : GName) : IProp GF := iprop%
  ∃ w : Nat, arcAuth γ 0 w

def nextIdOr (cells : List (Nat × Int)) (tail : Option Nat) : Option Nat :=
  match cells with
  | [] => tail
  | (id, _) :: _ => some id


def succRef (γ : GName) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ d : Data, metaAt γ id d ∗ isArc d.arc node d.mux

def livePayload (γ : GName) (d : Data): Option Nat → IProp GF
  | none => iprop%
      d.ptr ↦ hl_val((#false, (#d.val, none())))
  | some id => iprop%
      ∃ node : Val,
        d.ptr ↦ hl_val((#false, (#d.val, some(&node)))) ∗
        succRef γ node id

abbrev alivePayload (γ : GName) (d : Data) (q : Qp) (nxt : Option Nat) : IProp GF := iprop%
  cellAlive d.cell q nxt ∗ livePayload γ d nxt

def revokedPayload (d : Data) : IProp GF := iprop%
   cellDead d.cell ∗ d.ptr ↦ hl_val((#true, (#d.val, none())))

omit [RwLockG GF] in
/-- Split a live payload into the raw cell and exactly `Impl.new`'s precondition:
    whatever successor link the cell holds, in the shape the successor index says. -/
theorem livePayload_split (γ : GName) (d : Data) (nx : Option Nat) :
    livePayload (GF := GF) γ d nx ⊢
      ∃ nv : Val, d.ptr ↦ hl_val((#false, (#d.val, &nv))) ∗
        (match nx with
         | none => iprop% ⌜nv = hl_val(none())⌝
         | some j => iprop% ∃ u : Val, ⌜nv = hl_val(some(&u))⌝ ∗ succRef γ u j) := by
  cases nx with
  | none =>
      iintro H
      unfold livePayload
      iexists hl_val(none())
      iframe H
      itrivial
  | some j =>
      iintro H
      unfold livePayload
      icases H with ⟨%u, Hp, Hs⟩
      iexists hl_val(some(&u))
      iframe Hp
      iexists u
      isplit
      · ipureintro; rfl
      iexact Hs

omit [RwLockG GF] in
theorem livePayload_ptr (γ : GName) (d : Data) (nxt : Option Nat) :
    livePayload (GF := GF) γ d nxt ⊢ ∃ v : Val, d.ptr ↦ v := by
  rcases nxt with _ | i <;> simp only [livePayload]
  · iintro H
    iexists _
    iexact H
  · iintro H
    icases H with ⟨%nd, Hp, -⟩
    iexists _
    iexact Hp

omit [RwLockG GF] [ArcG GF] in
theorem revokedPayload_ptr (d : Data) :
    revokedPayload (GF := GF) d ⊢ ∃ v : Val, d.ptr ↦ v := by
  unfold revokedPayload
  iintro H
  icases H with ⟨-, Hp⟩
  iexists _
  iexact Hp

omit [RwLockG GF] [ArcG GF] in
theorem pointsTo_twice_False (l : Loc) (v w : Val) :
    (iprop(l ↦ v ∗ l ↦ w) : IProp GF) ⊢ False := by
  iintro ⟨H₁, H₂⟩
  icases pointsTo_ne $$ H₁ H₂ with %Hne
  ipureintro
  exact Hne rfl

abbrev Slot (GF : BundledGFunctors) [HeapLangGS hlc GF] [ArcG GF] [ArrG GF H] :=
  Data → (Qp → IProp GF) → IProp GF → IProp GF

abbrev aliveSlot (slot : Slot GF) (γ : GName) (d : Data) (nxt : Option Nat) : IProp GF :=
  slot d (fun q => cellAlive d.cell q nxt) (livePayload γ d nxt)

def isGhostHelp (slot : Slot GF) (γ : GName)
    (tail : Option Nat) : List (Nat × Int) → IProp GF
  | [] => iprop% emp
  | (id, x) :: cells => iprop%
      ∃ d : Data,
        ⌜x = d.val⌝ ∗
        metaAt γ id d ∗
        aliveSlot slot γ d (nextIdOr cells tail) ∗
        isGhostHelp slot γ tail cells

def isGhost (slot : Slot GF) (γ : GName)
    (cells : List (Nat × Int)) : IProp GF :=
  isGhostHelp slot γ none cells

def retiredSlot (slot : Slot GF) (d : Data) :
    IProp GF := iprop%
  cellDead d.cell ∗
    (slot d (fun _ => iprop% emp) (revokedPayload d) ∨ arcNoStrong d.arc)

def retiredNodes (slot : Slot GF) (M : H Data)
    (cells : List (Nat × Int)) : IProp GF := iprop%
  [∗map] id ↦ d ∈ M,
    if id ∈ cells.map (·.1) then emp else retiredSlot slot d

/-- What a shared-mode slot holds in each lock state.  Named rather than inlined so
    that instance resolution can case-split on `s` underneath the existential. -/
def nodeSlotSharedBody (γP : GName) (C : Qp → IProp GF) (P : IProp GF) :
    RwLock.State → IProp GF
  | .free =>
      iprop% P ∗ C 1
  | .write =>
      /- The thread that write-locked this node parks *half* its platform read
         permit here.  Keeping the other half is what lets it still prove the
         platform lock is read-held while it works — and it cannot leave the
         platform read lock without first releasing this node to get the half
         back, since `read_release` only accepts a full permit. -/
      iprop% rwGuardFrac γP RwLock.Mode.read q1_2 ∗ C q1_4
  | .read _ =>
      iprop% False

def nodeSlotShared (γP : GName) (d : Data) (C : Qp → IProp GF) (P : IProp GF) :
    IProp GF := iprop%
  arcHasStrong d.arc ∗
    ∃ s : RwLock.State,
    isRwLock d.rw d.mux s hl_val(#d.ptr) ∗ nodeSlotSharedBody γP C P s

def nodeSlotExclusive (d : Data) (C : Qp → IProp GF) (P : IProp GF) : IProp GF := iprop%
  arcHasStrong d.arc ∗ isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗ C 1 ∗ P

instance instArcHasStrongTimeless (γ : GName) :
    Timeless (arcHasStrong (GF := GF) γ) := by unfold arcHasStrong; infer_instance
instance instArcNoStrongTimeless (γ : GName) :
    Timeless (arcNoStrong (GF := GF) γ) := by unfold arcNoStrong; infer_instance
instance instSuccRefTimeless (γ : GName) (node : Val) (id : Nat) :
    Timeless (succRef (GF := GF) γ node id) := by unfold succRef; infer_instance
instance instLivePayloadTimeless (γ : GName) (d : Data) (nxt : Option Nat) :
    Timeless (livePayload (GF := GF) γ d nxt) := by
  cases nxt <;> unfold livePayload <;> infer_instance
instance instRevokedPayloadTimeless (d : Data) :
    Timeless (revokedPayload (GF := GF) d) := by unfold revokedPayload; infer_instance

/-- Abbreviation for "this slot interpretation is timeless whenever the resources it
    is applied to are".  Used as an instance-implicit hypothesis by everything built
    on top of a slot. -/
class SlotTimeless (slot : Slot GF) : Prop where
  out : ∀ (d : Data) (C : Qp → IProp GF) (P : IProp GF),
    (∀ q, Timeless (C q)) → Timeless P → Timeless (slot d C P)

instance instNodeSlotSharedBodyTimeless (γP : GName) (C : Qp → IProp GF) (P : IProp GF)
    [∀ q, Timeless (C q)] [Timeless P] (s : RwLock.State) :
    Timeless (nodeSlotSharedBody (GF := GF) γP C P s) := by
  cases s <;> simp only [nodeSlotSharedBody] <;> infer_instance

instance instNodeSlotSharedTimeless (γP : GName) (d : Data)
    (C : Qp → IProp GF) (P : IProp GF) [∀ q, Timeless (C q)] [Timeless P] :
    Timeless (nodeSlotShared (GF := GF) γP d C P) := by
  unfold nodeSlotShared; infer_instance

instance instNodeSlotExclusiveTimeless (d : Data)
    (C : Qp → IProp GF) (P : IProp GF) [∀ q, Timeless (C q)] [Timeless P] :
    Timeless (nodeSlotExclusive (GF := GF) d C P) := by
  unfold nodeSlotExclusive; infer_instance

instance instNodeSlotSharedSlotTimeless (γP : GName) :
    SlotTimeless (nodeSlotShared (GF := GF) γP) :=
  ⟨fun _ _ _ hC hP => by haveI := hC; haveI := hP; infer_instance⟩

instance instNodeSlotExclusiveSlotTimeless :
    SlotTimeless (GF := GF) (H := H) nodeSlotExclusive :=
  ⟨fun _ _ _ hC hP => by haveI := hC; haveI := hP; infer_instance⟩

instance instAliveSlotTimeless (slot : Slot GF) [inst : SlotTimeless slot]
    (γ : GName) (d : Data) (nxt : Option Nat) :
    Timeless (aliveSlot slot γ d nxt) :=
  inst.out d _ _ (fun _ => inferInstance) inferInstance

instance instIsGhostHelpTimeless (slot : Slot GF) [inst : SlotTimeless slot]
    (γ : GName) (tail : Option Nat) :
    ∀ cells, Timeless (isGhostHelp slot γ tail cells)
  | [] => by unfold isGhostHelp; infer_instance
  | (_, _) :: cs => by
      have := instIsGhostHelpTimeless slot (inst := inst) γ tail cs
      unfold isGhostHelp
      infer_instance

instance instIsGhostTimeless (slot : Slot GF) [inst : SlotTimeless slot]
    (γ : GName) (cells : List (Nat × Int)) :
    Timeless (isGhost slot γ cells) := by
  unfold isGhost
  exact instIsGhostHelpTimeless slot (inst := inst) γ none cells

instance instRetiredSlotTimeless (slot : Slot GF) [inst : SlotTimeless slot] (d : Data) :
    Timeless (retiredSlot slot d) := by
  haveI := inst.out d (fun _ => iprop% emp) (revokedPayload d)
            (fun _ => inferInstance) inferInstance
  unfold retiredSlot
  infer_instance

instance instRetiredNodesTimeless (slot : Slot GF) [inst : SlotTimeless slot]
    (M : H Data) (cells : List (Nat × Int)) :
    Timeless (retiredNodes slot M cells) := by
  unfold retiredNodes
  refine BigSepM.bigSepM_timeless (fun {id} {d} _ => ?_)
  haveI := instRetiredSlotTimeless slot (inst := inst) d
  by_cases h : id ∈ cells.map (·.1)
  · rw [if_pos h]; infer_instance
  · rw [if_neg h]; infer_instance

def sharedView (γ γP: GName) (M : H Data) (σ : Arr) : IProp GF := iprop%
  isGhost (nodeSlotShared γP) γ σ.cells ∗
  retiredNodes (nodeSlotShared γP) M σ.cells

def exclusiveView (γ : GName) (M : H Data) (σ : Arr) : IProp GF := iprop%
  isGhost nodeSlotExclusive γ σ.cells ∗ retiredNodes nodeSlotExclusive M σ.cells

/-- The mutable *content* of the array: the metadata map, the two side conditions
    `Arr.isArr` carries, and exclusive access to every node.  This is exactly what a
    thread holding the platform write lock gets to play with. -/
def arrContentAt (γ : Arrγ) (M : H Data) (σ : Arr) : IProp GF := iprop%
  metaMap γ.l M ∗ ⌜σ.wellFormed⌝ ∗ ⌜∀ id, dom M id ↔ id < σ.counter⌝ ∗
  exclusiveView γ.l M σ

/-- The same thing with the metadata map hidden: this is what a writing thread is
    handed, and it must give one back — possibly over a *different* map, since the
    body is allowed to allocate nodes. -/
def arrContent (γ : Arrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H Data, arrContentAt γ M σ

/-- The same content, but only shared (read) access to the nodes. -/
def arrShared (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) : IProp GF := iprop%
  metaMap γ.l M ∗ ⌜σ.wellFormed⌝ ∗ ⌜∀ id, dom M id ↔ id < σ.counter⌝ ∗
  sharedView γ.l γp M σ

/-- While the platform lock is write-held the content is *entirely* out with the
    writing thread; all that stays behind is the `1/4` share of `stateVar`, which
    pins `σ` and `M` so the abstract state cannot move until the writer comes back
    inside the atomic update. -/
def isPhysical (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) :
    RwLock.State → IProp GF
  | .write  => iprop% emp
  | .read _ => iprop% arrShared γ γp M σ ∗ /- Sync -/ stateVar γ.s q3_4 σ M
  | .free   => iprop% arrContentAt γ M σ ∗ /- Sync -/ stateVar γ.s q3_4 σ M

def isPlatform (ρ : GName) (s : RwLock.State) (platform : Val) : IProp GF := iprop%
  ∃ α : GName, ∃ gate : Val, ∃ cell : Loc,
    arcHasStrong α ∗ isArc α platform gate ∗
    isRwLock ρ gate s hl_val(#cell) ∗ cell ↦ hl_val(#())

instance instSharedViewTimeless (γ γP : GName) (M : H Data) (σ : Arr) :
    Timeless (sharedView (GF := GF) γ γP M σ) := by unfold sharedView; infer_instance
instance instExclusiveViewTimeless (γ : GName) (M : H Data) (σ : Arr) :
    Timeless (exclusiveView (GF := GF) γ M σ) := by unfold exclusiveView; infer_instance
instance instArrContentAtTimeless (γ : Arrγ) (M : H Data) (σ : Arr) :
    Timeless (arrContentAt (GF := GF) γ M σ) := by unfold arrContentAt; infer_instance
instance instArrContentTimeless (γ : Arrγ) (σ : Arr) :
    Timeless (arrContent (GF := GF) γ σ) := by unfold arrContent; infer_instance
instance instArrSharedTimeless (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) :
    Timeless (arrShared (GF := GF) γ γp M σ) := by unfold arrShared; infer_instance
instance instIsPhysicalTimeless (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr)
    (s : RwLock.State) :
    Timeless (isPhysical (GF := GF) γ γp M σ s) := by
  cases s <;> simp only [isPhysical] <;> infer_instance
instance instIsPlatformTimeless (ρ : GName) (s : RwLock.State) (platform : Val) :
    Timeless (isPlatform (GF := GF) ρ s platform) := by unfold isPlatform; infer_instance

/-! ### The array invariant

All *physical* resources live here: the platform `Arc` and `RwLock`, the metadata
map, every node slot and every payload.  The only thing that stays outside is
`arrFrag`, the client's fragment of the abstract state, and that is exactly what
an atomic update gets to touch — at the linearisation point and nowhere else. -/

def arrInvBody (γ : Arrγ) (γp : GName) (platform : Val) : IProp GF := iprop%
  ∃ s : RwLock.State, ∃ M : H Data, ∃ σ : Arr,
    isPlatform γp s platform ∗ isPhysical γ γp M σ s

instance instArrInvBodyTimeless (γ : Arrγ) (γp : GName) (platform : Val) :
    Timeless (arrInvBody (GF := GF) γ γp platform) := by unfold arrInvBody; infer_instance

/-- Persistent handle to a well-formed concurrent array.  Because it is persistent
    it survives past a linearisation point, which is what lets an operation still
    release the platform lock after its atomic update has been committed. -/
def isArrInv (N : Namespace) (γ : Arrγ) (γp : GName) (platform : Val) : IProp GF :=
  inv N (arrInvBody γ γp platform)

instance instIsArrInvPersistent (N : Namespace) (γ : Arrγ) (γp : GName) (platform : Val) :
    Persistent (isArrInv (GF := GF) N γ γp platform) := by unfold isArrInv; infer_instance

/-- The client's view: just the abstract state.  This is the *only* thing that ever
    appears inside an atomic update. -/
def arrFrag (γ : Arrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H Data, stateVar γ.s q1_4 σ M

instance instArrFragTimeless (γ : Arrγ) (σ : Arr) :
    Timeless (arrFrag (GF := GF) γ σ) := by unfold arrFrag; infer_instance

/-- Sanity check: the invariant body really is timeless, so `aacc_inv` applies to it
    without leaving a `▷`. -/
example (γ : Arrγ) (γp : GName) (platform : Val) :
    Timeless (arrInvBody (GF := GF) γ γp platform) := inferInstance

/-- What a client owns: a persistent handle plus the abstract state. -/
def Arr.isArr (N : Namespace) (γ : Arrγ) (γp : GName) (σ : Arr) (platform : Val) :
    IProp GF := iprop%
  isArrInv N γ γp platform ∗ arrFrag γ σ

/-- A freshly built node chain that has not been handed to a platform yet: the whole
    content, and the *undivided* abstract state.  Nothing is shared, so no invariant
    exists and there is nothing atomic about it. -/
def Arr.isList (γ : Arrγ) (σ : Arr) : IProp GF := iprop%
  ∃ M : H Data, arrContentAt γ M σ ∗ stateVar γ.s 1 σ M

def Arr.isId (γ : Arrγ) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ d : Data, metaAt γ.l id d ∗ isArc d.arc node d.mux


omit [RwLockG GF] in
theorem arcNoStrong_isArc_False (γ : GName) (a x : Val) :
    arcNoStrong γ ∗ isArc γ a x ⊢@{IProp GF} False := by
  unfold arcNoStrong
  iintro ⟨⟨%w, Hauth⟩, Harc⟩
  ihave #Hpos : ⌜(0:Nat) > 0⌝ $$ [Hauth Harc]
  · iapply Arc.arcAuth_isArc_valid
    isplitl [Hauth] <;> iassumption
  icases Hpos with %Hn
  exact absurd Hn (Nat.lt_irrefl 0)

theorem nodeSlotSharedUpgrade :
  ⊢@{IProp GF} nodeSlotShared γP d C P -∗ isRwLock γP mux .free ptr -∗ nodeSlotExclusive d C P ∗ isRwLock γP mux .free ptr := by
  iintro Hslot Hlock
  unfold nodeSlotShared nodeSlotExclusive
  icases Hslot with ⟨Harc, ⟨%s, H1, H2⟩⟩
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

theorem isGhostHelpUpgrade (cells : List (Nat × Int)) :
    ⊢@{IProp GF}
      isGhostHelp (nodeSlotShared γP) γ tail cells -∗
      isRwLock γP mux .free ptr -∗
      isGhostHelp nodeSlotExclusive γ tail cells ∗
        isRwLock γP mux .free ptr := by
  induction cells with
  | nil =>
      simp only [isGhostHelp]
      iintro Hempty Hlock
      iframe
  | cons cell cells ih =>
      simp only [isGhostHelp]
      iintro Hghost Hlock
      icases Hghost with ⟨%d, Hd, Hmeta, Hslot, Hrest⟩
      ihave Hslot' := nodeSlotSharedUpgrade $$ Hslot Hlock
      icases Hslot' with ⟨Hslot, Hlock⟩
      ihave Hrest' := ih $$ Hrest Hlock
      icases Hrest' with ⟨Hrest, Hlock⟩
      iframe
      iexists d
      iframe
theorem isGhostUpgrade :
    ⊢@{IProp GF}
      isGhost (nodeSlotShared γP) γ cells -∗
      isRwLock γP mux .free ptr -∗
      isGhost nodeSlotExclusive γ cells ∗ isRwLock γP mux .free ptr := by
  iintro Hghost Hlock
  unfold isGhost
  iapply isGhostHelpUpgrade $$ Hghost Hlock
omit [ArcG GF] [ArrG GF H] [RwLockG GF] in
theorem bigSepM_acc_mono
    {m : H Data}
    {Φ Ψ : Nat → Data → IProp GF}
    (step : ∀ k v, Φ k v -∗ A -∗ Ψ k v ∗ A) :
    ⊢@{IProp GF} ([∗map] k ↦ v ∈ m, Φ k v) -∗ A -∗ ([∗map] k ↦ v ∈ m, Ψ k v) ∗ A := by
  induction m using LawfulFiniteMap.induction_on with
  | hemp =>
      simp only [Algebra.BigOpM.bigOpM_empty]
      iintro Hempty HA
      iframe

  | hins k v m hnone ih =>
      iintro Hm HA

      ihave Hm :=
        (BigSepM.bigSepM_insert (Φ := Φ) hnone).mp $$ Hm
      icases Hm with ⟨Hhead, Htail⟩

      ihave Hhead' := step k v $$ Hhead HA
      icases Hhead' with ⟨Hhead, HA⟩

      ihave Htail' := ih $$ Htail HA
      icases Htail' with ⟨Htail, HA⟩

      isplitl [Hhead Htail]
      · iapply (BigSepM.bigSepM_insert (Φ := Ψ) hnone).mpr
        iframe
      · iframe
theorem retiredNodesUpgrade (M : H Data):
    ⊢@{IProp GF}
      retiredNodes (nodeSlotShared γP) M cells -∗
      isRwLock γP mux .free ptr -∗
      retiredNodes nodeSlotExclusive M cells ∗ isRwLock γP mux .free ptr := by
  unfold retiredNodes
  iapply bigSepM_acc_mono
  iintro %id %d Hentry Hlock
  by_cases h : id ∈ cells.map (·.1)
  · simp only [h, if_true]
    iframe
  · simp only [h, if_false, retiredSlot]
    icases Hentry with ⟨#Hcd, Hslot | Hdead⟩
    · ihave Hslot' := nodeSlotSharedUpgrade $$ Hslot Hlock
      icases Hslot' with ⟨Hslot, Hlock⟩
      iframe Hlock Hcd
      ileft
      iframe
    · iframe Hcd
      iframe


theorem sharedViewUpgrade (γ γP : GName) (M : H Data) (σ : Arr) :
    ⊢@{IProp GF} sharedView γ γP M σ -∗ isRwLock γP mux .free ptr -∗ exclusiveView γ M σ ∗ isRwLock γP mux .free ptr := by
  iintro Hshared Hlock
  unfold sharedView exclusiveView
  icases Hshared with ⟨Hghost, Hretired⟩

  ihave Hghost' := isGhostUpgrade $$ Hghost Hlock
  icases Hghost' with ⟨Hghost, Hlock⟩

  ihave Hretired' := retiredNodesUpgrade $$ Hretired Hlock
  icases Hretired' with ⟨Hretired, Hlock⟩

  iframe
def nodeSlotExclusiveDowngrad (d : Data) (C : Qp → IProp GF) (P : IProp GF) :
    nodeSlotExclusive d C P ⊢@{IProp GF} nodeSlotShared γP d C P := by
  unfold nodeSlotExclusive nodeSlotShared
  iintro H
  icases H with ⟨Harc, Hlock, HC, HP⟩
  iframe
  iexists .free
  dsimp only [nodeSlotSharedBody]
  iframe

def exclusiveViewDowngrad : exclusiveView γ M σ ⊢@{IProp GF} sharedView γ γP M σ := by
  unfold exclusiveView sharedView
  iintro H
  icases H with ⟨Hlive, Hretired⟩
  isplitl [Hlive]
  · unfold isGhost
    induction σ.cells with
    | nil =>
      simp only [isGhostHelp]
      itrivial
    | cons cell cells ih =>
      simp only [isGhostHelp]
      icases Hlive with ⟨%d, Hd, Hmeta, Hslot, Hrest⟩
      iexists d
      iframe
      isplitl [Hslot]
      · iapply nodeSlotExclusiveDowngrad $$ Hslot
      · apply ih
  · unfold retiredNodes
    iapply BigSepM.bigSepM_mono_of_forall $$ Hretired
    iintro %x %y H
    by_cases h : x ∈ σ.cells.map (·.1)
    · simp [h]; itrivial
    · simp only [h, if_false, retiredSlot]
      icases H with ⟨#Hcd, Hlive | Hdead⟩
      · iframe Hcd
        ileft
        iapply nodeSlotExclusiveDowngrad $$ Hlive
      · iframe Hcd
        iright
        iframe

omit [RwLockG GF] in
theorem retiredNodesAccNotIn {M : H Data} {cells} {id}
    (hl : get? M id = some d) (hnotin : id ∉ cells.map (·.1)) :
    retiredNodes slot M cells ⊢@{IProp GF}
      retiredSlot slot d ∗ (retiredSlot slot d -∗ retiredNodes slot M cells) := by
  unfold retiredNodes
  refine (BigSepM.bigSepM_lookup_acc
    (Φ := fun k v => if k ∈ cells.map (·.1) then emp else retiredSlot slot v)
    hl).1.trans ?_
  rw [if_neg hnotin]
  exact .rfl

omit [RwLockG GF] in
/-- Accessor for a **live** node, the mirror image of `retiredNodesAccNotIn`: that one
    digs into the map big-op `retiredNodes`, this one into the list recursion
    `isGhostHelp`.

    Two things deserve note.  First, it hands out the *whole slot*, not the payload:
    the payload lives only in the `.free` branch of `nodeSlotShared`, so a node that
    somebody else currently holds write-locked has none.  Extracting it requires
    learning `s = .free`, which only `RwLock.write_acquire`'s commit can tell you.
    Second, `nxt` is existential — the successor is pinned by the `1/4` vs `3/4`
    confrontation on `cellAlive`, not by this lemma. -/
theorem isGhostHelpAccIn (γ : GName) (d : Data)
    (slot : Slot GF)
    (tail : Option Nat) (id : Nat) :
    ∀ cells : List (Nat × Int), id ∈ cells.map (·.1) →
    metaAt γ id d ⊢@{IProp GF} isGhostHelp slot γ tail cells -∗
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
      ihave %hd := metaAt_agree $$ Hmeta' Hmeta
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

omit [RwLockG GF] in
/-- `isGhost` is `isGhostHelp` at `tail = none`. -/
theorem isGhostAccIn (γ : GName) (d : Data)
    (slot : Slot GF)
    (id : Nat) (cells : List (Nat × Int)) (hin : id ∈ cells.map (·.1)) :
    metaAt γ id d ⊢@{IProp GF} isGhost slot γ cells -∗
      ∃ nxt : Option Nat,
        aliveSlot slot γ d nxt ∗
        (aliveSlot slot γ d nxt -∗
          isGhost slot γ cells) :=
  isGhostHelpAccIn γ d slot none id cells hin

/-! ### Reading a node's status off the cell witness

These two are the reason `cellDead` is hoisted out of `retiredSlot`: they turn a
*resource* you happen to be holding into a *decision* about the current `σ`, at any
lock state.  They are strictly stronger than carrying `⌜id ∈ σ.cells⌝` around in a
spec, because they apply to every future `σ`, not to a snapshot. -/

omit [RwLockG GF] in
/-- Accessor for splicing a node in.  Given the chain over `pre ++ (id, x) :: post`,
    hand out the slot sitting at `id` and, in exchange for that slot re-pointed at a
    fresh `nid` plus a slot for `nid` itself, get back the chain over the list with
    `(nid, v)` inserted right after `id`.

    Cells in `pre` are untouched because a slot only records the *head* of the list
    that follows it (`nextIdOr`), and inserting after `id` does not move that head. -/
theorem isGhostHelpAccInsert (γ : GName) (d : Data) (slot : Slot GF)
    (tail : Option Nat) (id : Nat) (x : Int) (post : List (Nat × Int)) :
    ∀ pre : List (Nat × Int),
    metaAt γ id d ⊢@{IProp GF}
      isGhostHelp slot γ tail (pre ++ (id, x) :: post) -∗
        aliveSlot slot γ d (nextIdOr post tail) ∗
        ((aliveSlot slot γ d (nextIdOr post tail) -∗
            isGhostHelp slot γ tail (pre ++ (id, x) :: post)) ∧
         (∀ nid : Nat, ∀ v : Int, ∀ dNew : Data, ⌜v = dNew.val⌝ -∗ metaAt γ nid dNew -∗
            aliveSlot slot γ d (some nid) -∗
            aliveSlot slot γ dNew (nextIdOr post tail) -∗
            isGhostHelp slot γ tail (pre ++ (id, x) :: (nid, v) :: post))) := by
  intro pre
  induction pre with
  | nil =>
      iintro #Hmeta Hlist
      simp only [List.nil_append, isGhostHelp]
      icases Hlist with ⟨%d', %hval, #Hmeta', Hslot, Hrest⟩
      ihave %hd := metaAt_agree $$ Hmeta' Hmeta
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


omit [RwLockG GF] in
/-- The mirror image, for revoke: hand out the slot at `id` *and* the whole chain
    that follows it, and take back a chain that stops at `id`.  What comes out as
    `isGhostHelp … post` is what `Impl.revokeSuffix` walks. -/
theorem isGhostHelpAccTruncate (γ : GName) (d : Data) (slot : Slot GF)
    (tail : Option Nat) (id : Nat) (x : Int) (post : List (Nat × Int)) :
    ∀ pre : List (Nat × Int),
    metaAt γ id d ⊢@{IProp GF}
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
      ihave %hd := metaAt_agree $$ Hmeta' Hmeta
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

/-- Holding any share of the live witness proves the node is still in `σ`. -/
theorem cellAlive_mem (γ γp : GName) (M : H Data) (σ : Arr) (id : Nat) (d : Data)
    (q : Qp) (nxt : Option Nat) (hl : get? M id = some d) :
    ⊢@{IProp GF} metaAt γ id d -∗ cellAlive d.cell q nxt -∗ sharedView γ γp M σ -∗
      ⌜id ∈ σ.cells.map (·.1)⌝ := by
  iintro #Hmeta Halive Hview
  by_cases hin : id ∈ σ.cells.map (·.1)
  · ipureintro
    exact hin
  · unfold sharedView
    icases Hview with ⟨-, Hretired⟩
    ihave ⟨Hslot, -⟩ := retiredNodesAccNotIn hl hin $$ Hretired
    iunfold retiredSlot at Hslot
    icases Hslot with ⟨#Hcd, -⟩
    iexfalso
    iapply cellAlive_dead_False d.cell q nxt
    isplitl [Halive] <;> iassumption

/-- Dually, the persistent dead witness proves the node has left `σ`.  Here no
    hoisting is needed: a *live* slot carries `cellAlive` in **every** lock state
    (at `1` when free, at `1/4` when write-locked), so the refutation always lands. -/
theorem cellDead_not_mem (γ γp : GName) (M : H Data) (σ : Arr) (id : Nat) (d : Data) :
    ⊢@{IProp GF} metaAt γ id d -∗ cellDead d.cell -∗ sharedView γ γp M σ -∗
      ⌜id ∉ σ.cells.map (·.1)⌝ := by
  iintro #Hmeta #Hcd Hview
  by_cases hin : id ∈ σ.cells.map (·.1)
  · unfold sharedView
    icases Hview with ⟨Hghost, -⟩
    ihave Hacc := isGhostAccIn γ d (nodeSlotShared γp) id σ.cells hin $$ Hmeta Hghost
    icases Hacc with ⟨%nxt, Hslot, -⟩
    iunfold nodeSlotShared at Hslot
    icases Hslot with ⟨-, %s, -, Hstate⟩
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



theorem isPlatform_read_guard_valid (ρ : GName) (s : RwLock.State) (platform : Val) (q : Qp) :
    isPlatform ρ s platform ∗ rwGuardFrac ρ .read q ⊢@{IProp GF}
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




omit [LawfulFiniteMap H Nat] [ArcG GF] [ArrG GF H] in
theorem rwGuard_toFrac (γ : GName) :
    ⊢@{IProp GF} rwGuard γ .read -∗ rwGuardFrac γ .read 1 := by
  iintro H
  rw [← rwGuard_eq γ RwLock.Mode.read]
  iexact H

/-- Reassembling the invariant body while the platform lock is read-held. -/
theorem arrInvBody_read (γ : Arrγ) (γp : GName) (platform : Val) (n : Nat)
    (M : H Data) (σ : Arr) (hwf : σ.wellFormed)
    (hdom : ∀ id, dom M id ↔ id < σ.counter) :
    ⊢@{IProp GF}
      isPlatform γp (.read (n + 1)) platform -∗ metaMap γ.l M -∗
      isGhost (nodeSlotShared γp) γ.l σ.cells -∗
      retiredNodes (nodeSlotShared γp) M σ.cells -∗
      stateVar γ.s q3_4 σ M -∗ arrInvBody γ γp platform := by
  iintro Hplat HM Hghost Hretired Hstate
  unfold arrInvBody
  iexists (RwLock.State.read (n + 1)), M, σ
  simp only [isPhysical]
  iframe Hplat
  unfold arrShared sharedView
  isplitl [HM Hghost Hretired]
  · iframe HM
    isplit
    · ipureintro; exact hwf
    isplit
    · ipureintro; exact hdom
    iframe
  · iframe

/-- Taking a node's write lock.  A plain Hoare triple: the abstract state `σ` does
    not move, so there is nothing to linearise and no atomic update in sight — the
    node slot is simply borrowed out of the array invariant and back.

    The read permit is what makes this possible at all: it rules out the platform
    lock being write-held, which is the only state in which the invariant holds no
    node slots.  Half of it is left behind in the slot as a deposit. -/
theorem nodeWriteAcquireSpec (N : Namespace)
    (γ : Arrγ) (γp : GName) (platform node : Val) (id : Nat) (d : Data) :
    ⊢@{IProp GF}
      isArrInv N γ γp platform -∗ metaAt γ.l id d -∗ isArc d.arc node d.mux -∗
      rwGuard γp .read -∗
      WP hl(&RwLock.write_acquire &d.mux)
        {{ v, ⌜v = hl_val(#d.ptr)⌝ ∗
              isArc d.arc node d.mux ∗ rwGuard d.rw .write ∗
              rwGuardFrac γp .read q1_2 ∗
              ((∃ nxt, alivePayload γ.l d q3_4 nxt) ∨ revokedPayload d) }} := by
  iintro #Hinv #Hg HArc H
  ihave #Hinvraw : inv N (arrInvBody γ γp platform) $$ [Hinv]
  · iunfold isArrInv at Hinv
    iexact Hinv
  have Hfull' : (↑N : CoPset) ⊆ ((⊤ : CoPset) \ (∅ : CoPset)) :=
    fun _ _ => CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.mem_empty⟩
  iapply RwLock.write_acquire_spec d.rw d.mux hl_val(#d.ptr)
  iauintro
  iapply aacc_inv _ _ _ _ Hfull' $$ Hinvraw
  iintro HI
  iunfold arrInvBody at HI
  icases HI with ⟨%sp, %M, %σ, Hplat, Hphys⟩
  ihave #hread : ⌜∃ n, sp = RwLock.State.read (n + 1)⌝ $$ [Hplat H]
  · iapply isPlatform_read_guard_valid γp sp platform 1
    isplitl [Hplat]
    · iexact Hplat
    · iapply rwGuard_toFrac γp $$ H
  icases hread with ⟨%np, %hsp⟩
  subst hsp
  simp only [isPhysical]
  icases Hphys with ⟨Hsh, HstateVar⟩
  iunfold arrShared at Hsh
  icases Hsh with ⟨HM, %hwf, %hdom, Hview⟩
  unfold sharedView
  icases Hview with ⟨Hghost, Hretired⟩
  ihave %Hl := metaMap_lookup $$ HM Hg -- HM should not be consummed
  by_cases hin : id ∈ σ.cells.map (·.1)
  · ihave Hacc := isGhostAccIn γ.l d (nodeSlotShared γp) id σ.cells hin $$ Hg Hghost
    icases Hacc with ⟨%nxt, Hslot, Hback⟩
    iunfold nodeSlotShared at Hslot
    icases Hslot with ⟨Harc, %s, Hlock, Hstate⟩
    itele_reduce
    iaaccintro' with Hlock
    · -- ABORT: the CAS failed, so put the slot back in exactly the state we found it
      iintro Hlock
      imodintro
      ihave Hslot :
          aliveSlot (nodeSlotShared γp) γ.l d nxt
          $$ [Harc Hlock Hstate]
      · unfold aliveSlot nodeSlotShared
        iframe Harc
        iexists s
        iframe Hlock Hstate
      ihave Hghost := Hback $$ Hslot
      ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
        $$ Hplat HM Hghost Hretired HstateVar
      iframe
      isplitl []
      · isplitl []
        · imodintro; iexact Hinv
        · imodintro; iexact Hg
      · imodintro; iexact Hinvraw
    · -- COMMIT: the CAS succeeded, so `s = .free` and the payload is ours
      iintro %_ ⟨Hlock, Hguard, %hs⟩
      subst hs
      imodintro
      dsimp
      itele_reduce
      iunfold nodeSlotSharedBody at Hstate
      icases Hstate with ⟨HP, HC⟩
      -- 1/4 stays behind in the invariant, 3/4 goes out with the caller
      icases (cellAlive_split d.cell nxt).mp $$ HC with ⟨HC14, HC34⟩
      -- half the platform read permit is parked in the slot, half stays with us
      icases rwGuardHalve γp $$ H with ⟨Hdep, Hkeep⟩
      ihave Hslot :
          aliveSlot (nodeSlotShared γp) γ.l d nxt
          $$ [Harc Hlock HC14 Hdep]
      · unfold aliveSlot nodeSlotShared
        iframe Harc
        iexists .write
        dsimp only [nodeSlotSharedBody]
        iframe Hlock Hdep HC14
      ihave Hghost := Hback $$ Hslot
      ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
        $$ Hplat HM Hghost Hretired HstateVar
      iframe HIb
      isplit
      · ipureintro; rfl
      iframe HArc Hguard Hkeep
      ileft
      iexists nxt
      unfold alivePayload
      iframe HC34 HP
  · ihave ⟨Hslot, Hother⟩ := retiredNodesAccNotIn Hl hin $$ Hretired
    iunfold retiredSlot at Hslot
    icases Hslot with ⟨#Hcd, Hlive | Hdead⟩
    iunfold nodeSlotShared at Hlive
    icases Hlive with ⟨Harc, %s, Hlock, Hstate⟩
    itele_reduce
    iaaccintro' with Hlock
    · iintro Hlock
      imodintro
      ihave Hretired : retiredNodes (nodeSlotShared γp) M σ.cells
        $$ [Hother Harc Hstate Hlock Hcd]
      · iapply Hother
        unfold retiredSlot
        iframe Hcd
        ileft
        unfold nodeSlotShared
        iframe
        iexists s
        iframe
      ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
        $$ Hplat HM Hghost Hretired HstateVar
      iframe
      isplitl []
      · isplitl []
        · imodintro; iexact Hinv
        · imodintro; iexact Hg
      · imodintro; iexact Hinvraw
    · iintro %_  ⟨Hlock, Hguard, %hs⟩
      subst hs
      imodintro
      dsimp
      itele_reduce
      icases rwGuardHalve γp $$ H with ⟨Hdep, Hkeep⟩
      iunfold nodeSlotSharedBody at Hstate
      icases Hstate with ⟨HP, HC⟩
      ihave Hretired : retiredNodes (nodeSlotShared γp) M σ.cells
        $$ [Hother Harc Hlock Hdep Hcd]
      · iapply Hother
        unfold retiredSlot
        iframe Hcd
        ileft
        unfold nodeSlotShared
        iframe
        iexists .write
        dsimp only [nodeSlotSharedBody]
        iframe
      ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
        $$ Hplat HM Hghost Hretired HstateVar
      iframe HIb
      isplit
      · ipureintro; rfl
      iframe HArc Hguard Hkeep
      iright
      iframe HP
    ihave Hfalso := arcNoStrong_isArc_False $$ [Hdead HArc]
    iframe
    iexfalso; itrivial


/-- Releasing a node's write lock, the exact inverse of `sharedViewWriteAcquireSpec`.

    You hand back whichever bundle you took out and reclaim the platform read guard
    you deposited — the deposit is what stops anyone from leaving the platform read
    lock while still holding a node write-locked.

    There is no `⌜id ∈ σ.cells⌝` side condition: which case applies is decided by
    *which resource you hold*, via `cellAlive_mem` / `cellDead_not_mem`.  That is
    strictly stronger than a pure snapshot, since those lemmas speak about the `σ`
    at *this* linearisation point, not the one where the lock was taken. -/
theorem nodeWriteReleaseSpec (N : Namespace)
    (γ : Arrγ) (γp : GName) (platform node : Val) (id : Nat) (d : Data) :
    ⊢@{IProp GF}
      isArrInv N γ γp platform -∗ metaAt γ.l id d -∗ isArc d.arc node d.mux -∗
      rwGuard d.rw .write -∗ rwGuardFrac γp .read q1_2 -∗
      ((∃ nxt : Option Nat, alivePayload γ.l d q3_4 nxt) ∨ revokedPayload d) -∗
      WP hl(&RwLock.write_release &d.mux)
        {{ v, ⌜v = hl_val(#())⌝ ∗ isArc d.arc node d.mux ∗ rwGuard γp .read }} := by
  iintro #Hinv #Hg HArc Hguard Hkeep Hpay
  ihave #Hinvraw : inv N (arrInvBody γ γp platform) $$ [Hinv]
  · iunfold isArrInv at Hinv
    iexact Hinv
  have Hfull' : (↑N : CoPset) ⊆ ((⊤ : CoPset) \ (∅ : CoPset)) :=
    fun _ _ => CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.mem_empty⟩
  iapply RwLock.write_release_spec d.rw d.mux hl_val(#d.ptr) $$ Hguard
  iauintro
  iapply aacc_inv _ _ _ _ Hfull' $$ Hinvraw
  iintro HI
  iunfold arrInvBody at HI
  icases HI with ⟨%sp, %M, %σ, Hplat, Hphys⟩
  ihave #hread : ⌜∃ n, sp = RwLock.State.read (n + 1)⌝ $$ [Hplat Hkeep]
  · iapply isPlatform_read_guard_valid γp sp platform q1_2
    isplitl [Hplat] <;> iassumption
  icases hread with ⟨%np, %hsp⟩
  subst hsp
  simp only [isPhysical]
  icases Hphys with ⟨Hsh, HstateVar⟩
  iunfold arrShared at Hsh
  icases Hsh with ⟨HM, %hwf, %hdom, Hview⟩
  ihave #Hl : ⌜get? M id = some d⌝ $$ [HM Hg]
  · iapply metaMap_lookup γ.l M id d $$ HM Hg
  icases Hl with %Hl
  icases Hpay with ⟨⟨%nxt, Hcell, HP⟩ | Hrev⟩
  · -- the node is still live: locate its slot inside `isGhost`
    ihave #hin : ⌜id ∈ σ.cells.map (·.1)⌝ $$ [Hcell Hview Hg]
    · iapply cellAlive_mem γ.l γp M σ id d q3_4 nxt Hl $$ Hg Hcell Hview
    icases hin with %hin
    unfold sharedView
    icases Hview with ⟨Hghost, Hretired⟩
    ihave Hacc := isGhostAccIn γ.l d (nodeSlotShared γp) id σ.cells hin $$ Hg Hghost
    icases Hacc with ⟨%nxt', Hslot, Hback⟩
    iunfold nodeSlotShared at Hslot
    icases Hslot with ⟨Harc, %s, Hlock, Hstate⟩
    rcases s with ⟨h1 | h2 | h3⟩ <;> dsimp only [nodeSlotSharedBody]
    · -- `.free` is impossible: we are holding the payload out here
      icases Hstate with ⟨HP', -⟩
      iexfalso
      ihave ⟨%v, Hp⟩ := livePayload_ptr γ.l d nxt $$ HP
      ihave ⟨%v', Hp'⟩ := livePayload_ptr γ.l d nxt' $$ HP'
      iapply pointsTo_twice_False d.ptr v v'
      isplitl [Hp] <;> iassumption
    · iexfalso
      iexact Hstate
    · icases Hstate with ⟨Hdep, Hcell14⟩
      ihave #hnx : ⌜nxt = nxt'⌝ $$ [Hcell Hcell14]
      · iapply cellAlive_agree d.cell q3_4 q1_4 nxt nxt'
        isplitl [Hcell] <;> iassumption
      icases hnx with %hnx
      subst hnx
      iaaccintro' with Hlock
      · -- ABORT: nothing happened, park the slot back in `.write`
        iintro Hlock
        imodintro
        ihave Hpay : ((∃ n : Option Nat, alivePayload γ.l d q3_4 n) ∨ revokedPayload d)
            $$ [Hcell HP]
        · ileft
          iexists nxt
          unfold alivePayload
          iframe Hcell HP
        ihave Hslot : aliveSlot (nodeSlotShared γp) γ.l d nxt
          $$ [Harc Hlock Hdep Hcell14]
        · unfold aliveSlot nodeSlotShared
          iframe Harc
          iexists .write
          dsimp only [nodeSlotSharedBody]
          iframe Hlock Hdep Hcell14
        ihave Hghost := Hback $$ Hslot
        ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
          $$ Hplat HM Hghost Hretired HstateVar
        iframe
        isplitl []
        · isplitl []
          · imodintro; iexact Hinv
          · imodintro; iexact Hg
        · imodintro; iexact Hinvraw
      · -- COMMIT: the lock is free again, so the full cell and payload go back in
        iintro %_ Hlock
        imodintro
        itele_reduce
        ihave Hfull := (cellAlive_split d.cell nxt).mpr $$ [Hcell14 Hcell]
        · isplitl [Hcell14] <;> iassumption
        ihave Hslot : aliveSlot (nodeSlotShared γp) γ.l d nxt $$ [Harc Hlock Hfull HP]
        · unfold aliveSlot nodeSlotShared
          iframe Harc
          iexists .free
          dsimp only [nodeSlotSharedBody]
          iframe Hlock HP Hfull
        ihave Hghost := Hback $$ Hslot
        ihave Hfullguard := rwGuardUnhalve γp $$ Hdep Hkeep
        ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
          $$ Hplat HM Hghost Hretired HstateVar
        iframe HIb
        isplit
        · itrivial
        iframe HArc Hfullguard
  · -- the node has been revoked: its slot lives in `retiredNodes`
    iunfold revokedPayload at Hrev
    icases Hrev with ⟨#Hcd, Hptr⟩
    ihave #hnotin : ⌜id ∉ σ.cells.map (·.1)⌝ $$ [Hview Hg Hcd]
    · iapply cellDead_not_mem γ.l γp M σ id d $$ Hg Hcd Hview
    icases hnotin with %hnotin
    unfold sharedView
    icases Hview with ⟨Hghost, Hretired⟩
    ihave ⟨Hslot, Hback⟩ := retiredNodesAccNotIn Hl hnotin $$ Hretired
    iunfold retiredSlot at Hslot
    icases Hslot with ⟨-, Hlive | Hdead⟩
    · iunfold nodeSlotShared at Hlive
      icases Hlive with ⟨Harc, %s, Hlock, Hstate⟩
      rcases s with ⟨h1 | h2 | h3⟩ <;> dsimp only [nodeSlotSharedBody]
      · icases Hstate with ⟨HP', -⟩
        iexfalso
        ihave ⟨%v', Hp'⟩ := revokedPayload_ptr d $$ HP'
        iapply pointsTo_twice_False d.ptr hl_val((#true, (#d.val, none()))) v'
        isplitl [Hptr] <;> iassumption
      · iexfalso
        iexact Hstate
      · icases Hstate with ⟨Hdep, -⟩
        iaaccintro' with Hlock
        · iintro Hlock
          imodintro
          ihave Hslot : retiredSlot (nodeSlotShared γp) d $$ [Harc Hlock Hdep Hcd]
          · unfold retiredSlot nodeSlotShared
            iframe Hcd
            ileft
            iframe Harc
            iexists .write
            dsimp only [nodeSlotSharedBody]
            iframe Hlock Hdep
          ihave Hretired := Hback $$ Hslot
          ihave Hpay : ((∃ n : Option Nat, alivePayload γ.l d q3_4 n) ∨ revokedPayload d)
              $$ [Hptr Hcd]
          · iright
            unfold revokedPayload
            iframe Hcd Hptr
          ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
            $$ Hplat HM Hghost Hretired HstateVar
          iframe
          isplitl []
          · isplitl []
            · imodintro; iexact Hinv
            · imodintro; iexact Hg
          · imodintro; iexact Hinvraw
        · iintro %_ Hlock
          imodintro
          itele_reduce
          ihave Hslot : retiredSlot (nodeSlotShared γp) d $$ [Harc Hlock Hptr Hcd]
          · unfold retiredSlot nodeSlotShared revokedPayload
            iframe Hcd
            ileft
            iframe Harc
            iexists .free
            dsimp only [nodeSlotSharedBody]
            iframe Hlock Hptr Hcd
          ihave Hretired := Hback $$ Hslot
          ihave Hfullguard := rwGuardUnhalve γp $$ Hdep Hkeep
          ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
            $$ Hplat HM Hghost Hretired HstateVar
          iframe HIb
          isplit
          · itrivial
          iframe HArc Hfullguard
    · iexfalso
      iapply arcNoStrong_isArc_False d.arc node d.mux
      isplitl [Hdead] <;> iassumption


omit [RwLockG GF] in
theorem retiredNodes_congr (slot : Slot GF) (M : H Data)
    (cells₁ cells₂ : List (Nat × Int))
    (hmem : ∀ id, id ∈ cells₁.map (·.1) ↔ id ∈ cells₂.map (·.1)) :
    retiredNodes slot M cells₁ ⊣⊢ retiredNodes slot M cells₂ := by
  unfold retiredNodes
  apply BI.equiv_iff.mp
  apply BigSepM.bigSepM_eqv
  intro id d _
  by_cases h₁ : id ∈ cells₁.map (·.1)
  · have h₂ := (hmem id).mp h₁
    simp [h₁, h₂]
  · have h₂ : id ∉ cells₂.map (·.1) := fun h => h₁ ((hmem id).mpr h)
    simp [h₁, h₂]

omit [RwLockG GF] in
theorem retiredNodes_delete (slot : Slot GF)
    (M : H Data) (cells : List (Nat × Int)) (id : Nat) (d : Data)
    (hlookup : get? M id = some d) (hretired : id ∉ cells.map (·.1)) :
    retiredNodes slot M cells ⊣⊢
      retiredSlot slot d ∗ retiredNodes slot (delete M id) cells := by
  unfold retiredNodes
  refine (BigSepM.bigSepM_delete
    (Φ := fun id d => if id ∈ cells.map (·.1) then emp else retiredSlot slot d)
    hlookup).trans ?_
  rw [if_neg hretired]
  exact .rfl

omit [RwLockG GF] in
theorem retiredNodes_delete_live (slot : Slot GF)
    (M : H Data) (cells : List (Nat × Int)) (id : Nat) (d : Data)
    (hlookup : get? M id = some d) (hlive : id ∈ cells.map (·.1)) :
    retiredNodes slot M cells ⊣⊢ retiredNodes slot (delete M id) cells := by
  unfold retiredNodes
  refine (BigSepM.bigSepM_delete
    (Φ := fun id d => if id ∈ cells.map (·.1) then emp else retiredSlot slot d)
    hlookup).trans ?_
  rw [if_pos hlive]
  exact (emp_sep (PROP := IProp GF))

omit [RwLockG GF] in
/-- Two retired-node maps over the same `M` agree as soon as membership agrees on
    the ids `M` actually has. -/
theorem retiredNodes_congr_dom (slot : Slot GF) (M : H Data)
    (c₁ c₂ : List (Nat × Int))
    (h : ∀ k v, get? M k = some v → (k ∈ c₁.map (·.1) ↔ k ∈ c₂.map (·.1))) :
    retiredNodes slot M c₁ ⊣⊢ retiredNodes slot M c₂ := by
  unfold retiredNodes
  apply BI.equiv_iff.mp
  apply BigSepM.bigSepM_eqv
  intro k v hlookup
  by_cases hc : k ∈ c₁.map (·.1)
  · rw [if_pos hc, if_pos ((h k v hlookup).mp hc)]
    exact .rfl
  · rw [if_neg hc, if_neg (fun hx => hc ((h k v hlookup).mpr hx))]
    exact .rfl

omit [RwLockG GF] in
/-- Turn the `metaAt` witnesses `Impl.revokeSuffix` hands back into lookups in the
    metadata map, so the retired slots can be filed by id. -/
theorem retireList_lookup (γl : GName) (slot : Slot GF) (M : H Data) :
    ∀ removed : List (Nat × Int),
    ⊢@{IProp GF} metaMap γl M -∗
      ([∗list] c ∈ removed, ∃ d : Data, metaAt γl c.1 d ∗ retiredSlot slot d) -∗
      metaMap γl M ∗
      ([∗list] c ∈ removed, ∃ d : Data, ⌜get? M c.1 = some d⌝ ∗ retiredSlot slot d) := by
  intro removed
  induction removed with
  | nil =>
      iintro HM -
      iframe HM
      simp only [BI.bigSepL, Algebra.bigOpL]
      itrivial
  | cons c removed ih =>
      iintro HM Hlist
      simp only [BI.bigSepL, Algebra.bigOpL] at *
      icases Hlist with ⟨⟨%d, #Hat, Hslot⟩, Hrest⟩
      ihave #Hl : ⌜get? M c.1 = some d⌝ $$ [HM Hat]
      · iapply metaMap_lookup γl M c.1 d $$ HM Hat
      icases Hl with %Hl
      ihave ⟨HM, Hrest⟩ := ih $$ HM Hrest
      iframe HM
      isplitl [Hslot]
      · iexists d
        iframe Hslot
        ipureintro
        exact Hl
      · iexact Hrest

omit [RwLockG GF] in
/-- Retire a single node: it leaves the live list, and its slot gets filed. -/
theorem retiredNodes_retire_one (slot : Slot GF)
    (M : H Data) (cells cells' : List (Nat × Int)) (i : Nat) (d : Data)
    (hlookup : get? M i = some d) (hlive : i ∈ cells.map (·.1))
    (hnot : i ∉ cells'.map (·.1))
    (hdom : ∀ k v, get? M k = some v → k ≠ i →
       (k ∈ cells.map (·.1) ↔ k ∈ cells'.map (·.1))) :
    retiredNodes slot M cells ∗ retiredSlot slot d
    ⊢@{IProp GF} retiredNodes slot M cells' := by
  iintro ⟨Hold, Hslot⟩
  ihave Hold := (retiredNodes_delete_live slot M cells i d hlookup hlive).mp $$ Hold
  iapply (retiredNodes_delete slot M cells' i d hlookup hnot).mpr
  iframe Hslot
  iapply (retiredNodes_congr_dom slot (delete M i) cells cells' (by
    intro k v hk
    have hne : i ≠ k := by
      intro h; subst h; rw [get?_delete_eq rfl] at hk; exact absurd hk (by simp)
    rw [get?_delete_ne hne] at hk
    exact hdom k v hk (Ne.symm hne))).mp
  iexact Hold

omit [RwLockG GF] in
/-- File a batch of freshly retired nodes: the ids in `removed` leave the live set,
    everything else stays put. -/
theorem retiredNodes_retire (slot : Slot GF) (newCells : List (Nat × Int)) :
    ∀ (removed : List (Nat × Int)) (M : H Data) (oldCells : List (Nat × Int)),
    (∀ k v, get? M k = some v →
       (k ∈ oldCells.map (·.1) ↔ k ∈ newCells.map (·.1) ∨ k ∈ removed.map (·.1))) →
    (∀ k, k ∈ newCells.map (·.1) → k ∉ removed.map (·.1)) →
    (removed.map (·.1)).Nodup →
    retiredNodes slot M oldCells ∗
      ([∗list] c ∈ removed, ∃ d : Data, ⌜get? M c.1 = some d⌝ ∗ retiredSlot slot d)
    ⊢@{IProp GF} retiredNodes slot M newCells := by
  intro removed
  induction removed with
  | nil =>
      intro M oldCells hsub _ _
      iintro ⟨Hold, -⟩
      iapply (retiredNodes_congr_dom slot M oldCells newCells (by
        intro k v hk
        rw [hsub k v hk]
        simp)).mp
      iexact Hold
  | cons c removed ih =>
      rcases c with ⟨i, xc⟩
      intro M oldCells hsub hdisj hnd
      iintro ⟨Hold, Hlist⟩
      simp only [BI.bigSepL, Algebra.bigOpL] at *
      icases Hlist with ⟨⟨%d, %Hl, Hslot⟩, Hrest⟩
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnotin, hnd'⟩ := hnd
      have hlive : i ∈ oldCells.map (·.1) := by
        rw [hsub i d Hl]; right; simp
      have hnot : i ∉ (newCells ++ removed).map (·.1) := by
        simp only [List.map_append, List.mem_append]
        rintro (h | h)
        · exact hdisj i h (by simp)
        · exact hnotin h
      ihave Hold := retiredNodes_retire_one slot M oldCells (newCells ++ removed) i d
        Hl hlive hnot (by
          intro k v hk hne
          rw [hsub k v hk]
          simp only [List.map_append, List.mem_append, List.map_cons, List.mem_cons]
          constructor
          · rintro (h | h | h)
            · exact Or.inl h
            · exact absurd h hne
            · exact Or.inr h
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)) $$ [Hold Hslot]
      · isplitl [Hold] <;> iassumption
      iapply ih M (newCells ++ removed)
        (by
          intro k v _
          simp only [List.map_append, List.mem_append])
        (fun k hk => fun hkm => hdisj k hk (by
          simp only [List.map_cons, List.mem_cons]; exact Or.inr hkm))
        hnd'
      isplitl [Hold] <;> iassumption

omit [RwLockG GF] in
theorem retiredNodes_insert_live (slot : Slot GF)
    (M : H Data) (oldCells newCells : List (Nat × Int)) (id : Nat) (d : Data)
    (fresh : get? M id = none) (hlive : id ∈ newCells.map (·.1))
    (hsame : ∀ k v, get? M k = some v →
      (k ∈ newCells.map (·.1) ↔ k ∈ oldCells.map (·.1))) :
    retiredNodes slot (insert M id d) newCells ⊣⊢
      retiredNodes slot M oldCells := by
  unfold retiredNodes
  refine (BigSepM.bigSepM_insert
    (Φ := fun id d => if id ∈ newCells.map (·.1) then emp else retiredSlot slot d)
    fresh).trans ?_
  rw [if_pos hlive]
  refine (emp_sep (PROP := IProp GF)).trans ?_
  apply BI.equiv_iff.mp
  apply BigSepM.bigSepM_eqv
  intro k v hlookup
  have hmem := hsame k v hlookup
  by_cases hnew : k ∈ newCells.map (·.1)
  · have hold := hmem.mp hnew
    simp [hnew, hold]
  · have hold : k ∉ oldCells.map (·.1) := fun h => hnew (hmem.mpr h)
    simp [hnew, hold]








theorem isPhysical_read_acquire_first (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) :
    isPhysical γ γp M σ .free ⊢@{IProp GF} isPhysical γ γp M σ (.read 1) := by
  simp only [isPhysical, arrContentAt, arrShared]
  iintro H
  icases H with ⟨⟨HM, %hwf, %hdom, Hview⟩, Hstate⟩
  iframe
  isplit
  · ipureintro; exact hwf
  isplit
  · ipureintro; exact hdom
  iapply exclusiveViewDowngrad $$ Hview

/-- Joining an already-read-locked platform changes nothing: `isPhysical` does not
    look at the reader count, so this is definitional. -/
theorem isPhysical_read_acquire_more (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) (n : Nat) :
    isPhysical γ γp M σ (.read n) ⊢@{IProp GF} isPhysical γ γp M σ (.read (n + 1)) := .rfl

/-- Leaving while other readers remain: same, definitional. -/
theorem isPhysical_read_release_nonlast (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) (n : Nat) :
    isPhysical γ γp M σ (.read (n + 1)) ⊢@{IProp GF} isPhysical γ γp M σ (.read n) := .rfl

theorem isPhysical_read_release_last (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) :
    ⊢@{IProp GF}
      isPhysical γ γp M σ (.read 1) -∗ isRwLock γp mux .free ptr -∗
        isPhysical γ γp M σ .free ∗ isRwLock γp mux .free ptr := by
  simp only [isPhysical, arrContentAt, arrShared]
  iintro H Hlock
  icases H with ⟨⟨HM, %hwf, %hdom, Hview⟩, Hstate⟩
  ihave Hview' := sharedViewUpgrade $$ Hview Hlock
  icases Hview' with ⟨Hview, Hlock⟩
  iframe
  isplit
  · ipureintro; exact hwf
  ipureintro; exact hdom


/-- Taking the platform write lock empties the invariant: the whole content, and the
    `3/4` receipt that goes with it, leave with the writing thread. -/
theorem isPhysical_write_acquire (γ : Arrγ) (γp : GName) (M : H Data) (σ : Arr) :
    isPhysical γ γp M σ .free ⊢@{IProp GF}
      (arrContentAt γ M σ ∗ stateVar γ.s q3_4 σ M) ∗ isPhysical γ γp M σ .write := by
  simp only [isPhysical]
  iintro H
  iframe

/-- Releasing the platform write lock is the linearisation point.  The writer's `3/4`
    receipt only becomes a whole once the client's `1/4` arrives through the atomic
    update, and only a whole can advance the abstract state — which is exactly why
    the linearisation point cannot be anywhere else. -/
theorem isPhysical_write_release (γ : Arrγ) (γp : GName)
    (M M' : H Data) (σ σ' : Arr) :
    ⊢@{IProp GF}
      arrContentAt γ M' σ' -∗ stateVar γ.s q3_4 σ M -∗ arrFrag γ σ ==∗
        isPhysical γ γp M' σ' .free ∗ arrFrag γ σ' := by
  simp only [isPhysical]
  iintro Hview Hout Hfrag
  iunfold arrFrag at Hfrag
  icases Hfrag with ⟨%M₀, Hinv⟩
  ihave #hag : ⌜σ = σ ∧ M₀ = M⌝ $$ [Hinv Hout]
  · iapply stateVar_agree γ.s q1_4 q3_4 σ σ M₀ M
    isplitl [Hinv] <;> iassumption
  icases hag with ⟨-, %hM⟩
  subst hM
  ihave Hfull := (stateVar_split γ.s σ M₀).mpr $$ [Hinv Hout]
  · isplitl [Hinv] <;> iassumption
  ihave Hupd := stateVar_full_update γ.s σ σ' M₀ M' $$ Hfull
  imod Hupd with Hfull
  icases (stateVar_split γ.s σ' M').mp $$ Hfull with ⟨Hinv', Hout'⟩
  imodintro
  iframe Hview Hout'
  unfold arrFrag
  iexists M'
  iframe

omit [RwLockG GF] [ArcG GF] in
/-- The client's fragment agrees with the writer's receipt on the abstract state. -/
theorem arrFrag_agree (γ : Arrγ) (σ σ' : Arr) (M : H Data) :
    arrFrag γ σ ∗ stateVar γ.s q3_4 σ' M ⊢@{IProp GF} ⌜σ = σ'⌝ := by
  unfold arrFrag
  iintro ⟨⟨%M₀, Hfrag⟩, Hout⟩
  icases stateVar_agree γ.s q1_4 q3_4 σ σ' M₀ M $$ [Hfrag Hout] with %h
  · isplitl [Hfrag] <;> iassumption
  ipureintro
  exact h.1

/-- The `3/4` share is a *receipt* for the platform write lock: no other lock state
    leaves that much of `stateVar` unclaimed. -/
theorem isPhysical_write_pinned (γ : Arrγ) (γp : GName) (M M' : H Data)
    (σ σ' : Arr) (s : RwLock.State) :
    isPhysical γ γp M σ s ∗ stateVar γ.s q3_4 σ' M' ⊢@{IProp GF} ⌜s = .write⌝ := by
  cases s <;> simp only [isPhysical] <;> iintro ⟨Hphys, Hout⟩
  · iexfalso
    icases Hphys with ⟨-, Hstate⟩
    icases stateVar_frac_valid γ.s q3_4 q3_4 σ σ' M M' $$ [Hstate Hout] with %h
    · isplitl [Hstate] <;> iassumption
    exact absurd h q3_4_add_q3_4_invalid
  · iexfalso
    icases Hphys with ⟨-, Hstate⟩
    icases stateVar_frac_valid γ.s q3_4 q3_4 σ σ' M M' $$ [Hstate Hout] with %h
    · isplitl [Hstate] <;> iassumption
    exact absurd h q3_4_add_q3_4_invalid
  · ipureintro; trivial

omit [RwLockG GF] in
theorem Arr.isId_lookup (γ : Arrγ) (M : H Data) (node : Val) (id : Nat) :
    metaMap γ.l M ∗ Arr.isId γ node id ⊢@{IProp GF}
      metaMap γ.l M ∗
      ∃ d : Data,
        ⌜get? M id = some d⌝ ∗ metaAt γ.l id d ∗ isArc d.arc node d.mux := by
  unfold Arr.isId
  iintro H
  icases H with ⟨HM, Hid⟩
  icases Hid with ⟨%d, Hmeta, Harc⟩
  ihave #Hlookup : ⌜get? M id = some d⌝ $$ [HM Hmeta]
  · iapply metaMap_lookup γ.l M id d $$ HM Hmeta
  icases Hlookup with %hlookup
  isplitl [HM]
  · iexact HM
  · iexists d
    iframe Hmeta Harc %hlookup

end Resources

/-- Handing a freshly built list to a platform.  This is where the array becomes
    concurrent: the physical content is sealed into an invariant, the abstract state
    is split `3/4` (invariant) / `1/4` (client), and what comes back is a persistent
    handle plus the client's fragment.

    Allocating an invariant is a ghost update, so unlike the old pure wand this has
    to be a fancy update. -/
theorem Arr.isList_bind (N : Namespace)
    (γ : Arrγ) (γp : GName) (σ : Arr) (platform : Val) :
  ⊢@{IProp GF}
    Arr.isList γ σ -∗
    isPlatform γp .free platform ={⊤}=∗
    Arr.isArr N γ γp σ platform := by
  iintro Hlist Hplat
  unfold Arr.isList
  icases Hlist with ⟨%M, Hcontent, Hstate⟩
  icases (stateVar_split γ.s σ M).mp $$ Hstate with ⟨Hfrag, Hinv⟩
  ihave Hbody : arrInvBody γ γp platform $$ [Hplat Hcontent Hinv]
  · unfold arrInvBody
    iexists RwLock.State.free, M, σ
    simp only [isPhysical]
    iframe
  imod inv_alloc N ⊤ (arrInvBody γ γp platform) $$ Hbody with #Hinvariant
  imodintro
  unfold Arr.isArr isArrInv arrFrag
  iframe Hinvariant
  iexists M
  iframe

theorem Impl.platformNew_spec :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.platformNew #())
    ⦃ platform, RET platform;
      ∃ γp, isPlatform γp .free platform ⦄ := by
  iintro %Φ - HΦ
  unfold Impl.platformNew
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

/-! ### Sub-operation specs

`Impl.new` and `Impl.execute` are the building blocks of `Impl.insert` and
`Impl.revoke`. -/

/-- `Impl.new x next` allocates a fresh node.  Ownership of the successor link
    (either the literal `none()`, or `some(&v)` **together with one strong
    reference** to the successor node `i`) is *moved in*; what comes back is a
    fresh, unlocked node holding the only strong reference to itself.

    Note this spec is a plain Hoare triple: nothing here touches shared state, so
    no atomic update has to be opened. -/
theorem Impl.new_spec (γ : GName) (x : Int) (next : Val) (nxt : Option Nat) :
  ⊢@{IProp GF}
    ⦃ match nxt with
      | none => iprop% ⌜next = hl_val(none())⌝
      | some i => iprop% ∃ v : Val, ⌜next = hl_val(some(&v))⌝ ∗ succRef γ v i ⦄
      hl(&Impl.new #x &next)
    ⦃ node, RET node;
      ∃ d : Data,
        ⌜x = d.val⌝ ∗
        arcAuth d.arc 1 0 ∗
        isArc d.arc node d.mux ∗
        isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗
        cellAlive d.cell 1 nxt ∗
        livePayload γ d nxt ⦄ := by
  iintro %Φ Hpre HΦ
  iapply wp_fupd
  unfold Impl.new
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
  imodintro
  iapply HΦ
  iexists ⟨γarc, γrw, γcell, l, p, x⟩
  isplit
  · ipureintro; rfl
  iframe Hauth Harc Hlock Hcell
  unfold livePayload
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

/-- Running `f` under the platform **read** lock.  `f` never sees the platform: it
    gets the persistent handle and a read permit, and its atomic update carries only
    the abstract state.  `execute` never opens the atomic update at all — it hands it
    straight to `f`, so the linearisation point is wherever `f` puts it.

    That the platform read lock can still be released *after* `f` has already
    committed is exactly what `isArrInv` being persistent buys: the invariant can be
    reopened, an atomic update cannot. -/
theorem Impl.init_spec (x : Int) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.init #x)
    ⦃ root, RET root;
      ∃ γ, Arr.isList γ (Arr.init x) ∗ Arr.isId γ root 0 ⦄ := by
  iintro %Φ - HΦ
  iapply wp_fupd
  unfold Impl.init
  wp_pures
  -- allocate the metadata map first: `new` needs a name to hang `succRef` on
  imod metaMap_alloc with ⟨%γl, HM⟩
  iapply Impl.new_spec γl x hl_val(none()) none
  · ipureintro; rfl
  iintro %root !> ⟨%d, %hval, Hauth, Harc, Hlock, Hcell, Hpay⟩
  subst hval
  imod metaMap_insert γl (∅ : H Data) 0 d (by simp [get?_empty]) $$ HM with ⟨HM, #Hat⟩
  imod stateVar_alloc (Arr.init d.val) (Std.insert (∅ : H Data) 0 d) with ⟨%γs, Hstate⟩
  imodintro
  iapply HΦ
  iexists ⟨γl, γs⟩
  isplitl [HM Hstate Hauth Hlock Hcell Hpay]
  · unfold Arr.isList arrContentAt exclusiveView Arr.init
    iexists (Std.insert (∅ : H Data) 0 d)
    isplitl [HM Hauth Hlock Hcell Hpay]
    · iframe HM
      isplit
      · ipureintro; exact Arr.init_wellFormed d.val
      isplit
      · ipureintro
        exact metaMap_insert_counter_dom (∅ : H Data) 0 d
          (by intro id; unfold dom; simp [get?_empty])
      isplitl [Hauth Hlock Hcell Hpay]
      · unfold isGhost isGhostHelp
        iexists d
        isplit
        · ipureintro; rfl
        iframe Hat
        isplitl [Hauth Hlock Hcell Hpay]
        · unfold aliveSlot nodeSlotExclusive nextIdOr
          iframe Hlock Hcell Hpay
          unfold arcHasStrong
          iexists 1, 0
          iframe Hauth
          ipureintro
          omega
        · unfold isGhostHelp
          itrivial
      · unfold retiredNodes
        iapply (BigSepM.bigSepM_insert (h := by simp [get?_empty])).mpr
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil]
        rw [if_pos (by simp)]
        isplit
        · itrivial
        iapply BigSepM.bigSepM_empty.mpr
        itrivial
    · iframe Hstate
  · unfold Arr.isId
    dsimp only []
    iexists d
    iframe
    iexact Hat

theorem Impl.execute_shared_spec (N : Namespace)
    (γ : Arrγ) (γP : GName) (platform f : Val) (Q : Arr → Arr → Val → IProp GF) :
  ⊢@{IProp GF}
    isArrInv N γ γP platform -∗
    (isArrInv N γ γP platform -∗ rwGuard γP .read -∗
       ⟪ ∀ σ, arrFrag γ σ ⟫
         hl(&f #()) @ ↑N
       ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r ∗ rwGuard γP .read | RET r ⟫) -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&Impl.execute &platform #false &f) @ ↑N
    ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r | RET r ⟫ := by
  iintro #Hinv Hf %Φ HAU
  ihave #Hinvraw : inv N (arrInvBody γ γP platform) $$ [Hinv]
  · iunfold isArrInv at Hinv
    iexact Hinv
  have Hfull : (↑N : CoPset) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  have Hfull' : (↑N : CoPset) ⊆ ((⊤ : CoPset) \ (∅ : CoPset)) :=
    fun _ _ => CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.mem_empty⟩
  -- Peek at the runtime shape of `platform` so that `Arc.get` can reduce.
  iapply fupd_wp
  imod inv_acc Hfull $$ Hinvraw with ⟨>HI, Hcl⟩
  iunfold arrInvBody at HI
  icases HI with ⟨%s0, %M0, %σ0, Hplat, Hphys⟩
  iunfold isPlatform at Hplat
  icases Hplat with ⟨%α, %gate, %cell, Hstrong, Harc, Hlock, Hcell⟩
  ihave #hshape : ⌜∃ ps pw p c : Loc, platform = hl_val(((#ps, #pw), (#p, #c)))⌝ $$ [Harc Hlock]
  · icases Arc.isArc_copyRuntime α platform gate $$ Harc with ⟨⟨%ps, %pw, %hp⟩, -⟩
    icases RwLock.isRwLock_copyRuntime γP gate hl_val(#cell) s0 $$ Hlock with ⟨⟨%p, %hg⟩, -⟩
    ipureintro
    exact ⟨ps, pw, p, cell, by rw [hp, hg]⟩
  ihave HI : arrInvBody γ γP platform $$ [Hphys Hstrong Harc Hlock Hcell]
  · unfold arrInvBody isPlatform
    iexists s0, M0, σ0
    isplitl [Hstrong Harc Hlock Hcell]
    · iexists α, gate, cell
      iframe
    · iframe
  imod Hcl $$ HI with -
  imodintro
  icases hshape with ⟨%ps, %pw, %p, %c, %hplat⟩
  subst hplat
  unfold Impl.execute Arc.get
  wp_pures
  -- `read_acquire`: invariant only, σ untouched.
  wp_bind &RwLock.read_acquire _
  iapply RwLock.read_acquire_spec γP hl_val((#p, #c)) hl_val(#c)
  iauintro
  iapply aacc_inv _ _ _ _ Hfull' $$ Hinvraw
  iintro HI
  iunfold arrInvBody at HI
  icases HI with ⟨%s1, %M1, %σ1, Hplat, Hphys⟩
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
  · -- abort
    iintro Hlock
    imodintro
    isplitl [Hstrong Harc Hlock Hcell Hphys]
    · unfold arrInvBody isPlatform
      iexists s1, M1, σ1
      isplitl [Hstrong Harc Hlock Hcell]
      · iexists α1, hl_val((#p, #c)), c
        iframe
      · iframe
    · iframe
      isplitl []
      · imodintro; iexact Hinv
      · imodintro; iexact Hinvraw
  · -- commit: whichever way the lock was free or already read-held, we end up one
    -- reader deeper and the view degrades to the shared one.
    itele_reduce
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
    isplitl [Hstrong Harc Hlock Hcell Hphys]
    · unfold arrInvBody isPlatform
      iexists (RwLock.State.read (m + 1)), M1, σ1
      isplitl [Hstrong Harc Hlock Hcell]
      · iexists α1, hl_val((#p, #c)), c
        iframe
      · iframe
    · itele_reduce
      wp_pures
      -- `f` runs with the read permit; its atomic update is ours, passed straight on.
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
        · -- `f` aborted: hand the fragment back and keep the update
          iintro Hfrag
          icases Hclose with ⟨Habort, -⟩
          imod Habort $$ Hfrag with HAU
          imodintro
          iframe
          isplitl []
          · imodintro; iexact Hinv
          · imodintro; iexact Hinvraw
        · -- `f` linearised: commit ours at the same instant, keep the read permit
          itele_reduce
          iintro %r Hbeta
          icases Hbeta with ⟨%σ', Hfrag', HQ, Hguard⟩
          icases Hclose with ⟨-, Hcommit⟩
          ihave Hbeta : ∃ σ'', arrFrag γ σ'' ∗ Q σc σ'' r $$ [Hfrag' HQ]
          · iexists σ'
            iframe
          imod Hcommit $$ Hbeta with HΦ
          imodintro
          wp_pures
          -- The update is gone, but `isArrInv` is persistent: reopen and release.
          wp_bind &RwLock.read_release _
          iapply RwLock.read_release_spec γP hl_val((#p, #c)) hl_val(#c) $$ Hguard
          iauintro
          iapply aacc_inv _ _ _ _ Hfull' $$ Hinvraw
          iintro HI
          iunfold arrInvBody at HI
          icases HI with ⟨%s2, %M2, %σ2, Hplat, Hphys⟩
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
          · -- abort
            iintro Hlock
            imodintro
            isplitl [Hstrong Harc Hlock Hcell Hphys]
            · unfold arrInvBody isPlatform
              iexists s2, M2, σ2
              isplitl [Hstrong Harc Hlock Hcell]
              · iexists α2, hl_val((#p, #c)), c
                iframe
              · iframe
            · iframe
              isplitl []
              · imodintro; iexact Hinv
              · imodintro; iexact Hinvraw
          · -- commit: last reader restores the exclusive view, otherwise nothing moves
            itele_reduce
            iintro %k Hpost
            icases Hpost with ⟨%hs2, Hcases⟩
            subst hs2
            ihave Hres : ∃ s' : RwLock.State,
                isRwLock γP hl_val((#p, #c)) s' hl_val(#c) ∗
                isPhysical γ γP M2 σ2 s' $$ [Hcases Hphys]
            · icases Hcases with (⟨Hlock, %hk⟩ | ⟨Hlock, %hk⟩)
              · subst hk
                iexists RwLock.State.free
                ihave Hres := isPhysical_read_release_last γ γP M2 σ2 $$ Hphys Hlock
                icases Hres with ⟨Hphys, Hlock⟩
                iframe
              · iexists (RwLock.State.read k)
                iframe Hlock
                iapply isPhysical_read_release_nonlast γ γP M2 σ2 k
                iexact Hphys
            icases Hres with ⟨%s', Hlock, Hphys⟩
            imodintro
            isplitl [Hstrong Harc Hlock Hcell Hphys]
            · unfold arrInvBody isPlatform
              iexists s', M2, σ2
              isplitl [Hstrong Harc Hlock Hcell]
              · iexists α2, hl_val((#p, #c)), c
                iframe
              · iframe
            · itele_reduce
              wp_pures
              iexact HΦ

/-- Running `f` under the platform **write** lock.  `f` gets the whole content
    sequentially — no atomic update, no lock, no ghost names — and hands back a
    content at a possibly different abstract state plus its own result `Q`.

    Every lock operation only opens the *invariant*; the atomic update is touched
    exactly once, at `write_release`, which is the linearisation point.  While `f`
    runs the invariant is empty and the abstract state cannot move, because
    advancing it needs the writer's `3/4` receipt *and* the client's `1/4`. -/
theorem Impl.execute_exclusive_spec (N : Namespace)
    (γ : Arrγ) (γP : GName) (platform f : Val) (Q : Arr → Arr → Val → IProp GF) :
  ⊢@{IProp GF}
    isArrInv N γ γP platform -∗
    (∀ σ,
       ⦃ arrContent γ σ ⦄
         hl(&f #())
       ⦃ r, RET r; ∃ σ', arrContent γ σ' ∗ Q σ σ' r ⦄) -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&Impl.execute &platform #true &f) @ ↑N
    ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r | RET r ⟫ := by
  iintro #Hinv Hf %Φ HAU
  iunfold isArrInv at Hinv
  have Hfull : (↑N : CoPset) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  have Hfull' : (↑N : CoPset) ⊆ ((⊤ : CoPset) \ (∅ : CoPset)) :=
    fun _ _ => CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.mem_empty⟩
  -- Peek at the runtime shape of `platform` so that `Arc.get` can reduce.  Opening
  -- and closing the invariant with no program step in between, hence `fupd_wp`.
  iapply fupd_wp
  imod inv_acc Hfull $$ Hinv with ⟨>HI, Hcl⟩
  iunfold arrInvBody at HI
  icases HI with ⟨%s0, %M0, %σ0, Hplat, Hphys⟩
  iunfold isPlatform at Hplat
  icases Hplat with ⟨%α, %gate, %cell, Hstrong, Harc, Hlock, Hcell⟩
  ihave #hshape : ⌜∃ ps pw p c : Loc, platform = hl_val(((#ps, #pw), (#p, #c)))⌝ $$ [Harc Hlock]
  · icases Arc.isArc_copyRuntime α platform gate $$ Harc with ⟨⟨%ps, %pw, %hp⟩, -⟩
    icases RwLock.isRwLock_copyRuntime γP gate hl_val(#cell) s0 $$ Hlock with ⟨⟨%p, %hg⟩, -⟩
    ipureintro
    exact ⟨ps, pw, p, cell, by rw [hp, hg]⟩
  ihave HI : arrInvBody γ γP platform $$ [Hphys Hstrong Harc Hlock Hcell]
  · unfold arrInvBody isPlatform
    iexists s0, M0, σ0
    isplitl [Hstrong Harc Hlock Hcell]
    · iexists α, gate, cell
      iframe
    · iframe
  imod Hcl $$ HI with -
  imodintro
  icases hshape with ⟨%ps, %pw, %p, %c, %hplat⟩
  subst hplat
  unfold Impl.execute Arc.get
  wp_pures
  -- `write_acquire`: only the invariant is touched; σ does not move.
  wp_bind &RwLock.write_acquire _
  iapply RwLock.write_acquire_spec γP hl_val((#p, #c)) hl_val(#c)
  iauintro
  iapply aacc_inv _ _ _ _ Hfull' $$ Hinv
  iintro HI
  iunfold arrInvBody at HI
  icases HI with ⟨%s1, %M1, %σ1, Hplat, Hphys⟩
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
  · -- abort: nothing happened, put the body back
    iintro Hlock
    imodintro
    isplitl [Hstrong Harc Hlock Hcell Hphys]
    · unfold arrInvBody isPlatform
      iexists s1, M1, σ1
      isplitl [Hstrong Harc Hlock Hcell]
      · iexists α1, hl_val((#p, #c)), c
        iframe
      · iframe
    · iframe
      imodintro
      iexact Hinv
  · -- commit: the lock was free, so the content walks out with us
    itele_reduce
    iintro Hpost
    icases Hpost with ⟨Hlock, Hguard, %hs1⟩
    subst hs1
    imodintro
    icases isPhysical_write_acquire γ γP M1 σ1 $$ Hphys with ⟨⟨Hcontent, Hout⟩, Hphys⟩
    isplitl [Hstrong Harc Hlock Hcell Hphys]
    · unfold arrInvBody isPlatform
      iexists RwLock.State.write, M1, σ1
      isplitl [Hstrong Harc Hlock Hcell]
      · iexists α1, hl_val((#p, #c)), c
        iframe
      · iframe
    · itele_reduce
      wp_pures
      -- `f` runs sequentially on the whole content
      wp_bind &f _
      ihave Hcontent : arrContent γ σ1 $$ [Hcontent]
      · unfold arrContent
        iexists M1
        iexact Hcontent
      iapply Hf $$ Hcontent
      iintro %r !> Hres
      icases Hres with ⟨%σ2, Hcontent2, HQ⟩
      iunfold arrContent at Hcontent2
      icases Hcontent2 with ⟨%M2, Hcontent2⟩
      wp_pures
      -- `write_release`: the linearisation point.  Invariant *and* atomic update.
      wp_bind &RwLock.write_release _
      iapply RwLock.write_release_spec γP hl_val((#p, #c)) hl_val(#c) $$ Hguard
      iauintro
      iapply aacc_inv _ _ _ _ Hfull' $$ Hinv
      iintro HI
      iunfold arrInvBody at HI
      icases HI with ⟨%s3, %M3, %σ3, Hplat, Hphys⟩
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
      · -- abort: keep everything, put the (empty) body back
        iintro Hlock
        imodintro
        isplitl [Hstrong Harc Hlock Hcell Hphys]
        · unfold arrInvBody isPlatform
          iexists RwLock.State.write, M3, σ3
          isplitl [Hstrong Harc Hlock Hcell]
          · iexists α3, hl_val((#p, #c)), c
            iframe
          · iframe
        · iframe
          imodintro
          iexact Hinv
      · -- commit: open the atomic update, advance σ, seal the new content back in
        itele_reduce
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
        isplitl [Hstrong Harc Hlock Hcell Hphys']
        · unfold arrInvBody isPlatform
          iexists RwLock.State.free, M2, σ2
          isplitl [Hstrong Harc Hlock Hcell]
          · iexists α3, hl_val((#p, #c)), c
            iframe
          · iframe
        · itele_reduce
          wp_pures
          iexact HΦ

/-- Releasing a node's write lock **at a linearisation point that grows the array**.

    The `σ`-preserving `nodeWriteReleaseSpec` cannot be used here: by the time the
    predecessor's lock is dropped the new node is already physically linked, so the
    invariant can only be re-established at the *new* abstract state, and moving the
    abstract state needs the client's fragment — which only the atomic update can
    deliver.  Hence this one is logically atomic while its `σ`-preserving sibling is
    not.

    Everything about the new node arrives raw: `new` and `Arc.clone` have run, so
    there are two strong references (one becomes the edge stored in the predecessor,
    one is handed back to the caller) and the metadata record has not been registered
    yet.  Registering it is part of the linearisation point, because its id is
    `σ.counter`, which is only known once the update is open. -/
theorem nodeWriteReleaseInsertSpec (N : Namespace)
    (γ : Arrγ) (γp : GName) (platform node newNode : Val)
    (id : Nat) (x : Int) (d dNew : Data) (nxt : Option Nat) :
    ⊢@{IProp GF}
      isArrInv N γ γp platform -∗ metaAt γ.l id d -∗ isArc d.arc node d.mux -∗
      rwGuard d.rw .write -∗ rwGuardFrac γp .read q1_2 -∗
      -- the predecessor: its `3/4` cell share still says `nxt`, but its payload has
      -- already been re-pointed at the new node
      cellAlive d.cell q3_4 nxt -∗
      d.ptr ↦ hl_val((#false, (#d.val, some(&newNode)))) -∗
      -- the new node, straight out of `Impl.new` followed by `Arc.clone`
      ⌜x = dNew.val⌝ -∗
      arcAuth dNew.arc 2 0 -∗
      isArc dNew.arc newNode dNew.mux -∗
      isArc dNew.arc newNode dNew.mux -∗
      isRwLock dNew.rw dNew.mux .free hl_val(#dNew.ptr) -∗
      cellAlive dNew.cell 1 nxt -∗
      livePayload γ.l dNew nxt -∗
      ⟪ ∀ σ, arrFrag γ σ ⟫
        hl(&RwLock.write_release &d.mux) @ ↑N
      ⟪ arrFrag γ (Arr.insert σ id x).1 ∗
          isArc d.arc node d.mux ∗ rwGuard γp .read ∗
          Arr.isId γ newNode σ.counter ∗
          ⌜(Arr.insert σ id x).2 = some σ.counter⌝
        | RET hl_val(#()) ⟫ := by
  iintro #Hinv #Hat HArc Hwguard Hkeep Hcell Hptr %hval HauthN HarcN HedgeN
         HlockN HcellN HpayN %Φ HAU
  ihave #Hinvraw : inv N (arrInvBody γ γp platform) $$ [Hinv]
  · iunfold isArrInv at Hinv
    iexact Hinv
  have Hfull' : (↑N : CoPset) ⊆ ((⊤ : CoPset) \ (∅ : CoPset)) :=
    fun _ _ => CoPset.in_diff.mpr ⟨CoPset.mem_full, CoPset.mem_empty⟩
  iapply RwLock.write_release_spec d.rw d.mux hl_val(#d.ptr) $$ Hwguard
  iauintro
  iapply aacc_inv _ _ _ _ Hfull' $$ Hinvraw
  iintro HI
  iunfold arrInvBody at HI
  icases HI with ⟨%sp, %M, %σ, Hplat, Hphys⟩
  ihave #hread : ⌜∃ n, sp = RwLock.State.read (n + 1)⌝ $$ [Hplat Hkeep]
  · iapply isPlatform_read_guard_valid γp sp platform q1_2
    isplitl [Hplat] <;> iassumption
  icases hread with ⟨%np, %hsp⟩
  subst hsp
  simp only [isPhysical]
  icases Hphys with ⟨Hsh, HstateVar⟩
  iunfold arrShared at Hsh
  icases Hsh with ⟨HM, %hwf, %hdom, Hview⟩
  ihave #Hl : ⌜get? M id = some d⌝ $$ [HM Hat]
  · iapply metaMap_lookup γ.l M id d $$ HM Hat
  icases Hl with %Hl
  -- the `3/4` cell share says the node is still in `σ`
  ihave #hin : ⌜id ∈ σ.cells.map (·.1)⌝ $$ [Hcell Hview Hat]
  · iapply cellAlive_mem γ.l γp M σ id d q3_4 nxt Hl $$ Hat Hcell Hview
  icases hin with %hin
  obtain ⟨pre, xv, post, hsplit⟩ := Arr.exists_split_id hin
  iunfold sharedView at Hview
  icases Hview with ⟨Hghost, Hretired⟩
  iunfold isGhost at Hghost
  ihave Hghost' : isGhostHelp (nodeSlotShared γp) γ.l none (pre ++ (id, xv) :: post)
      $$ [Hghost]
  · rw [← hsplit]
    iexact Hghost
  ihave Hacc := isGhostHelpAccInsert γ.l d (nodeSlotShared γp) none id xv post pre
                  $$ Hat Hghost'
  icases Hacc with ⟨Hslot, Hback⟩
  iunfold aliveSlot at Hslot
  iunfold nodeSlotShared at Hslot
  icases Hslot with ⟨Harc, %s, Hlock, Hstate⟩
  -- the payload is in our hands, so the slot cannot be `.free`; `.read` is absurd
  rcases s with ⟨h1 | h2 | h3⟩ <;> dsimp only [nodeSlotSharedBody]
  · icases Hstate with ⟨HP', -⟩
    iexfalso
    ihave ⟨%v', Hp'⟩ := livePayload_ptr γ.l d (nextIdOr post none) $$ HP'
    iapply pointsTo_twice_False d.ptr hl_val((#false, (#d.val, some(&newNode)))) v'
    isplitl [Hptr] <;> iassumption
  · iexfalso
    iexact Hstate
  · icases Hstate with ⟨Hdep, Hcell14⟩
    ihave #hnx : ⌜nxt = nextIdOr post none⌝ $$ [Hcell Hcell14]
    · iapply cellAlive_agree d.cell q3_4 q1_4 nxt (nextIdOr post none)
      isplitl [Hcell] <;> iassumption
    icases hnx with %hnx
    subst hnx
    iaaccintro' with Hlock
    · -- ABORT: put the slot back exactly as we found it
      iintro Hlock
      imodintro
      ihave Hslot : aliveSlot (nodeSlotShared γp) γ.l d (nextIdOr post none)
          $$ [Harc Hlock Hdep Hcell14]
      · unfold aliveSlot nodeSlotShared
        iframe Harc
        iexists .write
        dsimp only [nodeSlotSharedBody]
        iframe Hlock Hdep Hcell14
      -- rebuild the chain at the *same* shape
      icases Hback with ⟨Hsame, -⟩
      ihave Hghost' := Hsame $$ Hslot
      ihave Hghost : isGhost (nodeSlotShared γp) γ.l σ.cells $$ [Hghost']
      · unfold isGhost
        rw [hsplit]
        iexact Hghost'
      ihave HIb := arrInvBody_read γ γp platform np M σ hwf hdom
        $$ Hplat HM Hghost Hretired HstateVar
      iframe
      isplitl []
      · isplitl []
        · imodintro; iexact Hinv
        · imodintro; iexact Hat
      · imodintro; iexact Hinvraw
    · -- COMMIT: the linearisation point
      itele_reduce
      iintro Hlock
      iauopen HAU with ⟨%σc, Hfrag, Hclose⟩
      ihave #hσ : ⌜σc = σ⌝ $$ [Hfrag HstateVar]
      · iapply arrFrag_agree γ σc σ M
        isplitl [Hfrag] <;> iassumption
      icases hσ with %hσ
      subst hσ
      -- register the new node's metadata; its id is `σ.counter`
      imod metaMap_insert_counter γ.l M σc.counter dNew hdom $$ HM with ⟨HM, #HatN⟩
      -- re-point the predecessor at it
      imod cellAlive_update d.cell (nextIdOr post none) (some σc.counter)
        $$ [Hcell14 Hcell] with ⟨Hcell14, Hcell⟩
      · isplitl [Hcell14] <;> iassumption
      -- the predecessor's slot, back in `.free` and pointing at the new node
      ihave Hslotd : aliveSlot (nodeSlotShared γp) γ.l d (some σc.counter)
          $$ [Harc Hlock Hcell14 Hcell Hptr HedgeN]
      · unfold aliveSlot nodeSlotShared
        iframe Harc
        iexists .free
        dsimp only [nodeSlotSharedBody]
        iframe Hlock
        isplitl [Hptr HedgeN]
        · unfold livePayload
          iexists newNode
          iframe Hptr
          unfold succRef
          iexists dNew
          iframe HedgeN
          iexact HatN
        · iapply (cellAlive_split d.cell (some σc.counter)).mpr
          iframe Hcell14 Hcell
      -- and the new node's own slot
      ihave HslotN : aliveSlot (nodeSlotShared γp) γ.l dNew (nextIdOr post none)
          $$ [HauthN HlockN HcellN HpayN]
      · unfold aliveSlot nodeSlotShared
        isplitl [HauthN]
        · unfold arcHasStrong
          iexists 2, 0
          iframe HauthN
          ipureintro
          omega
        iexists .free
        dsimp only [nodeSlotSharedBody]
        iframe HlockN HpayN HcellN
      icases Hback with ⟨-, Hsplice⟩
      ihave Hghost' := Hsplice $$ %σc.counter %x %dNew %hval HatN Hslotd HslotN
      -- what the abstract insert does to the list, spelled out
      obtain ⟨hpre, hpost⟩ := Arr.nodup_split_id pre post id xv (hsplit ▸ hwf.idUqi)
      have hins : Arr.insert σc id x =
          ({ cells := pre ++ (id, xv) :: (σc.counter, x) :: post,
             counter := σc.counter + 1 }, some σc.counter) :=
        Arr.insert_eq_of_split σc pre post id xv x hsplit hpre hpost
      -- advance the abstract state: `3/4` from the invariant, `1/4` from the client
      iunfold arrFrag at Hfrag
      icases Hfrag with ⟨%M₀, Hfrag⟩
      ihave #hag : ⌜σc = σc ∧ M₀ = M⌝ $$ [Hfrag HstateVar]
      · iapply stateVar_agree γ.s q1_4 q3_4 σc σc M₀ M
        isplitl [Hfrag] <;> iassumption
      icases hag with ⟨-, %hM⟩
      subst hM
      ihave Hfull := (stateVar_split γ.s σc M₀).mpr $$ [Hfrag HstateVar]
      · isplitl [Hfrag] <;> iassumption
      ihave Hupd := stateVar_full_update γ.s σc (Arr.insert σc id x).1 M₀
                      (Std.insert M₀ σc.counter dNew) $$ Hfull
      imod Hupd with Hfull
      icases (stateVar_split γ.s (Arr.insert σc id x).1
                (Std.insert M₀ σc.counter dNew)).mp $$ Hfull with ⟨Hfrag, HstateVar⟩
      -- the retired map is unchanged: the new id is live, and no old id moved
      ihave Hretired' : retiredNodes (nodeSlotShared γp)
            (Std.insert M₀ σc.counter dNew) (Arr.insert σc id x).1.cells $$ [Hretired]
      · iapply (retiredNodes_insert_live (nodeSlotShared γp) M₀ σc.cells
            (Arr.insert σc id x).1.cells σc.counter dNew
            (metaMap_counter_fresh M₀ σc.counter hdom)
            (by rw [hins]; simp) (by
              intro k v hk
              rw [hins, hsplit]
              simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
              have hklt : k < σc.counter := (hdom k).mp (by unfold dom; rw [hk]; rfl)
              constructor
              · rintro (h | h | h | h)
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · omega
                · exact Or.inr (Or.inr h)
              · rintro (h | h | h)
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr (Or.inr h)))).mpr
        iexact Hretired
      -- reassemble and commit
      ihave Hghost : isGhost (nodeSlotShared γp) γ.l (Arr.insert σc id x).1.cells
          $$ [Hghost']
      · unfold isGhost
        rw [hins]
        iexact Hghost'
      have hdom' : ∀ i, dom (Std.insert M₀ σc.counter dNew) i ↔
          i < (Arr.insert σc id x).1.counter := by
        rw [hins]
        exact metaMap_insert_counter_dom M₀ σc.counter dNew hdom
      ihave HIb := arrInvBody_read γ γp platform np (Std.insert M₀ σc.counter dNew)
        (Arr.insert σc id x).1 (Arr.insert_wellFormed σc hwf id x) hdom'
        $$ Hplat HM Hghost Hretired' HstateVar
      icases Hclose with ⟨-, Hcommit⟩
      ihave Hfullguard := rwGuardUnhalve γp $$ Hdep Hkeep
      ihave Hbeta : (arrFrag γ (Arr.insert σc id x).1 ∗ isArc d.arc node d.mux ∗
                     rwGuard γp .read ∗ Arr.isId γ newNode σc.counter ∗
                     ⌜(Arr.insert σc id x).2 = some σc.counter⌝)
          $$ [Hfrag HArc Hfullguard HarcN]
      · unfold arrFrag Arr.isId
        isplitl [Hfrag]
        · iexists (Std.insert M₀ σc.counter dNew)
          iexact Hfrag
        iframe HArc Hfullguard
        isplitl [HarcN]
        · iexists dNew
          iframe HarcN
          iexact HatN
        · ipureintro
          rw [hins]
      imod Hcommit $$ Hbeta with HΦ
      imodintro
      iframe HIb
      iexact HΦ

/-- What `Impl.insert`'s body achieves, phrased as `Impl.execute_shared_spec` wants
    it: the abstract state moves to `(Arr.insert σ id x).1` and the result reports
    whether a node was actually created. -/
def Impl.insertQ (γ : Arrγ) (node : Val) (id : Nat) (x : Int)
    (σ σ' : Arr) (ret : Val) : IProp GF := iprop%
  ⌜σ' = (Arr.insert σ id x).1⌝ ∗
  Arr.isId γ node id ∗
  match (Arr.insert σ id x).2 with
  | none => iprop% ⌜ret = hl_val(none())⌝
  | some nid => iprop%
      ∃ newNode : Val,
        ⌜ret = hl_val(some(&newNode))⌝ ∗
        Arr.isId γ newNode nid

theorem Impl.insert_spec (N : Namespace)
    (γ : Arrγ) (γp : GName) (platform node : Val) (id : Nat) (x : Int) :
  ⊢@{IProp GF}
    isArrInv N γ γp platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&Impl.insert &platform &node #x) @ ↑N
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
  iintro #Hinv Hid %Φ HAU
  unfold Impl.insert
  wp_pures
  iapply Impl.execute_shared_spec N γ γp platform _ (Impl.insertQ γ node id x) $$ Hinv [Hid]
  · -- the body, running under the platform read lock
    iintro #Hinv' Hguard %Φ' HAU'
    iunfold Arr.isId at Hid
    icases Hid with ⟨%d, #Hat, HArc⟩
    wp_pures
    wp_bind &Arc.get _
    iapply Arc.get_spec (γ := d.arc) node d.mux $$ HArc
    iintro !> HArc
    wp_pures
    -- take the node's write lock; the abstract state does not move here
    wp_bind &RwLock.write_acquire _
    iapply wp_wand $$ [Hinv' Hat HArc Hguard]
    · iapply nodeWriteAcquireSpec N γ γp platform node id d $$ Hinv' Hat HArc Hguard
    iintro %ptr ⟨%hptr, HArc, Hwguard, Hkeep, Hpay⟩
    subst hptr
    wp_pures
    icases Hpay with ⟨Hlive | Hrev⟩
    · -- the node is still live: link a fresh node in after it
      icases Hlive with ⟨%nxt, Hcell, HP⟩
      -- read the payload; the successor link comes out in whichever shape `nxt` says
      -- split the payload into the raw cell and exactly `Impl.new`'s precondition
      ihave Hsplit :
          ∃ nv : Val, d.ptr ↦ hl_val((#false, (#d.val, &nv))) ∗
            (match nxt with
             | none => iprop% ⌜nv = hl_val(none())⌝
             | some i => iprop% ∃ v : Val, ⌜nv = hl_val(some(&v))⌝ ∗ succRef γ.l v i)
          $$ [HP]
      · cases nxt with
        | none =>
            iunfold livePayload at HP
            iexists hl_val(none())
            iframe HP
            itrivial
        | some i =>
            iunfold livePayload at HP
            icases HP with ⟨%nv, Hp, Hsucc⟩
            iexists hl_val(some(&nv))
            iframe Hp
            iexists nv
            isplit
            · ipureintro; rfl
            iexact Hsucc
      icases Hsplit with ⟨%nv, Hptr, Hnext⟩
      wp_bind !_
      iapply wp_load $$ Hptr
      iintro !> Hptr
      wp_pures
      -- allocate the new node; the old successor link moves into it
      wp_bind (&Impl.new _ _)
      iapply Impl.new_spec γ.l x nv nxt $$ Hnext
      iintro %newNode !> ⟨%dNew, %hval, HauthN, HisArcN, HlockN, HcellN, HpayN⟩
      wp_pures
      -- clone the new node's reference: one copy becomes the edge stored in the
      -- predecessor, the other is what the caller gets back
      wp_bind &Arc.clone _
      iapply Arc.clone_spec (γ := dNew.arc) newNode dNew.mux $$ HisArcN
      iauintro
      iaaccintro' with HauthN
      · iintro HauthN
        imodintro
        iframe
        isplitl []
        · isplitl []
          · imodintro; iexact Hinv
          · imodintro; iexact Hinv'
        · imodintro; iexact Hat
      · itele_reduce
        iintro Hpost
        imodintro
        icases Hpost with ⟨HauthN, HisArcN, HedgeN⟩
        iframe
        wp_pures
        -- physically link the new node in
        wp_bind (_ ← _)
        iapply wp_store $$ Hptr
        iintro !> Hptr
        wp_pures
        -- and drop the predecessor's lock: this is the linearisation point
        wp_bind &RwLock.write_release _
        iapply nodeWriteReleaseInsertSpec N γ γp platform node newNode id x d dNew nxt
          $$ Hinv' Hat HArc Hwguard Hkeep Hcell Hptr %hval HauthN HisArcN HedgeN
             HlockN HcellN HpayN
        -- the linearisation point: our own update is what backs the one we hand over
        iauintro
        simp only [atomicAcc]
        iauopen HAU' with ⟨%σ, Hfrag, Hclose⟩
        imodintro
        iexists σ
        isplitl [Hfrag]
        · iexact Hfrag
        · isplit
          · -- abort
            iintro Hfrag
            icases Hclose with ⟨Habort, -⟩
            imod Habort $$ Hfrag with HAU'
            imodintro
            iframe
            isplitl []
            · isplitl []
              · imodintro; iexact Hinv
              · imodintro; iexact Hinv'
            · imodintro; iexact Hat
          · -- commit
            itele_reduce
            iintro Hbeta
            icases Hbeta with ⟨Hfrag', HArc, Hguard, Hnew, %hins⟩
            icases Hclose with ⟨-, Hcommit⟩
            ihave Hb : (∃ σ', arrFrag γ σ' ∗
                          Impl.insertQ γ node id x σ σ' hl_val(injr(&newNode)) ∗
                          rwGuard γp .read)
                $$ [Hfrag' HArc Hguard Hnew]
            · iexists (Arr.insert σ id x).1
              iframe Hfrag' Hguard
              unfold Impl.insertQ
              isplit
              · ipureintro; rfl
              isplitl [HArc]
              · unfold Arr.isId
                iexists d
                iframe HArc
                iexact Hat
              · rw [hins]
                iexists newNode
                isplit
                · ipureintro; rfl
                iexact Hnew
            imod Hcommit $$ Hb with HΦ
            imodintro
            wp_pures
            iexact HΦ
    · -- the node has already been revoked: read `true`, put the slot straight back
      ihave #Hcd : cellDead d.cell $$ [Hrev]
      · iunfold revokedPayload at Hrev
        icases Hrev with ⟨#H, -⟩
        iexact H
      iunfold revokedPayload at Hrev
      icases Hrev with ⟨-, Hptr⟩
      wp_bind !_
      iapply wp_load $$ Hptr
      iintro !> Hptr
      wp_pures
      -- hand the (unchanged) payload back and drop the node lock
      ihave Hpay : ((∃ n : Option Nat, alivePayload γ.l d q3_4 n) ∨ revokedPayload d)
          $$ [Hptr Hcd]
      · iright
        unfold revokedPayload
        iframe Hcd Hptr
      wp_bind &RwLock.write_release _
      iapply wp_wand $$ [Hinv' Hat HArc Hwguard Hkeep Hpay]
      · iapply nodeWriteReleaseSpec N γ γp platform node id d
          $$ Hinv' Hat HArc Hwguard Hkeep Hpay
      iintro %u ⟨%hu, HArc, Hguard⟩
      subst hu
      wp_pures
      -- linearise: nothing changed, and `id` is not in `σ` because the cell is dead.
      -- No program step is involved, so this is a plain fancy update.
      ihave #Hinvraw : inv N (arrInvBody γ γp platform) $$ [Hinv']
      · iunfold isArrInv at Hinv'
        iexact Hinv'
      have Hfull : (↑N : CoPset) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
      imod inv_acc Hfull $$ Hinvraw with ⟨>HI, Hcl⟩
      iunfold arrInvBody at HI
      icases HI with ⟨%sp, %M, %σi, Hplat, Hphys⟩
      ihave #hread : ⌜∃ n, sp = RwLock.State.read (n + 1)⌝ $$ [Hplat Hguard]
      · iapply isPlatform_read_guard_valid γp sp platform 1
        isplitl [Hplat]
        · iexact Hplat
        · iapply rwGuard_toFrac γp $$ Hguard
      icases hread with ⟨%np, %hsp⟩
      subst hsp
      simp only [isPhysical]
      icases Hphys with ⟨Hsh, HstateVar⟩
      iunfold arrShared at Hsh
      icases Hsh with ⟨HM, %hwf, %hdom, Hview⟩
      ihave #hnotin : ⌜id ∉ σi.cells.map (·.1)⌝ $$ [Hat Hcd Hview]
      · iapply cellDead_not_mem γ.l γp M σi id d $$ Hat Hcd Hview
      icases hnotin with %hnotin
      iauopen HAU' with ⟨%σc, Hfrag, Hclose⟩
      ihave #hσ : ⌜σc = σi⌝ $$ [Hfrag HstateVar]
      · iapply arrFrag_agree γ σc σi M
        isplitl [Hfrag] <;> iassumption
      icases hσ with %hσ
      subst hσ
      icases Hclose with ⟨-, Hcommit⟩
      ihave Hbeta : ∃ σ', arrFrag γ σ' ∗ Impl.insertQ γ node id x σc σ' hl_val(none())
                          ∗ rwGuard γp .read $$ [Hfrag Hguard HArc]
      · iexists σc
        iframe Hfrag Hguard
        have hnone : Arr.insert σc id x = (σc, none) := by
          unfold Arr.insert
          rw [if_neg (by
            intro hex
            simp only [List.any_eq_true, decide_eq_true_eq] at hex
            obtain ⟨c, hmem, hc⟩ := hex
            exact hnotin (List.mem_map.mpr ⟨c, hmem, hc⟩))]
        unfold Impl.insertQ
        rw [hnone]
        isplit
        · ipureintro; rfl
        isplitl [HArc]
        · unfold Arr.isId
          iexists d
          iframe HArc
          iexact Hat
        · itrivial
      imod Hcommit $$ Hbeta with HΦ
      iunfold sharedView at Hview
      icases Hview with ⟨Hghost, Hretired⟩
      ihave HI := arrInvBody_read γ γp platform np M σc hwf hdom
        $$ Hplat HM Hghost Hretired HstateVar
      imod Hcl $$ HI with -
      imodintro
      iexact HΦ
  · -- the abstract state `f` reports is exactly the one our own client expects
    iapply aupd_mono_commit _ _ _ _ $$ HAU
    rintro ⟨σ, ⟨⟩⟩ ⟨ret, ⟨⟩⟩
    simp only [Tele.app, Impl.insertQ]
    iintro ⟨%σ', Hfrag, %hσ', Hid, Hrest⟩
    subst hσ'
    iframe

/-- Walking off the end of the list, retiring everything on the way.

    Runs under the platform *write* lock, so every node slot is `.free` and owned
    outright — no invariant, no atomic update, just a sequential induction on the
    suffix.  The strong reference that the predecessor used to hold is what gets
    handed in as `v`, and it is dropped once the recursion returns. -/
theorem Impl.revokeSuffix_spec (γ : Arrγ) :
    ∀ (suffix : List (Nat × Int)) (v : Val),
    ⊢@{IProp GF}
      ⦃ (match nextIdOr suffix none with
         | none => iprop% ⌜v = hl_val(none())⌝
         | some i => iprop% ∃ w : Val, ⌜v = hl_val(some(&w))⌝ ∗ succRef γ.l w i) ∗
        isGhostHelp nodeSlotExclusive γ.l none suffix ⦄
        hl(&Impl.revokeSuffix &v)
      ⦃ RET hl_val(#());
        [∗list] c ∈ suffix, ∃ d : Data,
          metaAt γ.l c.1 d ∗ retiredSlot nodeSlotExclusive d ⦄ := by
  intro suffix
  induction suffix with
  | nil =>
      intro v
      simp only [nextIdOr]
      iintro %Φ Hpre HΦ
      icases Hpre with ⟨%hv, -⟩
      subst hv
      unfold Impl.revokeSuffix
      wp_rec
      wp_pures
      imodintro
      iapply HΦ
      iapply BigSepL.bigSepL_nil.mpr
      itrivial
  | cons c suffix ih =>
      rcases c with ⟨i, xv⟩
      intro v
      simp only [nextIdOr]
      iintro %Φ Hpre HΦ
      icases Hpre with ⟨⟨%w, %hv, Hsucc⟩, Hlist⟩
      subst hv
      -- the reference we were handed and the head of the chain agree on the record
      iunfold succRef at Hsucc
      icases Hsucc with ⟨%dd, #Hat, HArc⟩
      simp only [isGhostHelp]
      icases Hlist with ⟨%d, %hxv, #Hat', Hslot, Hrest⟩
      ihave %hdd := metaAt_agree $$ Hat Hat'
      subst dd
      unfold Impl.revokeSuffix
      wp_rec
      wp_pures
      wp_bind &Arc.get _
      iapply Arc.get_spec (γ := d.arc) w d.mux $$ HArc
      iintro !> HArc
      wp_pures
      -- the slot is ours outright: platform write lock is held, so it is `.free`
      iunfold aliveSlot at Hslot
      iunfold nodeSlotExclusive at Hslot
      icases Hslot with ⟨Hstrong, Hlock, Hcell, HP⟩
      wp_bind &RwLock.write_acquire _
      iapply RwLock.write_acquire_spec d.rw d.mux hl_val(#d.ptr)
      iauintro
      iaaccintro' with Hlock
      · iintro Hlock
        imodintro
        iframe
        isplitl []
        · imodintro; iexact Hat
        · imodintro; iexact Hat
      · itele_reduce
        iintro Hpost
        icases Hpost with ⟨Hlock, Hwguard, -⟩
        imodintro
        iframe
        wp_pures
        -- read the payload, mark the node revoked, hand the successor to the recursion
        ihave Hsplit :
            ∃ nv : Val, d.ptr ↦ hl_val((#false, (#d.val, &nv))) ∗
              (match nextIdOr suffix none with
               | none => iprop% ⌜nv = hl_val(none())⌝
               | some j => iprop% ∃ u : Val, ⌜nv = hl_val(some(&u))⌝ ∗ succRef γ.l u j)
            $$ [HP]
        · iapply livePayload_split γ.l d (nextIdOr suffix none) $$ HP
        icases Hsplit with ⟨%nv, Hptr, Hnext⟩
        wp_bind !_
        iapply wp_load $$ Hptr
        iintro !> Hptr
        wp_pures
        wp_bind (_ ← _)
        iapply wp_store $$ Hptr
        iintro !> Hptr
        wp_pures
        -- the cell is now dead
        icases (cellAlive_split d.cell (nextIdOr suffix none)).mp $$ Hcell
          with ⟨Hc14, Hc34⟩
        imod cellAlive_kill d.cell (nextIdOr suffix none) $$ [Hc14 Hc34] with #Hcd
        · isplitl [Hc14] <;> iassumption
        -- give the lock back
        wp_bind &RwLock.write_release _
        iapply RwLock.write_release_spec d.rw d.mux hl_val(#d.ptr) $$ Hwguard
        iauintro
        iaaccintro' with Hlock
        · iintro Hlock
          imodintro
          iframe
          isplitl []
          · isplitl []
            · imodintro; iexact Hat
            · imodintro; iexact Hat
          · imodintro; iexact Hcd
        · itele_reduce
          iintro Hlock
          imodintro
          iframe
          -- recurse on the tail, then drop our reference
          wp_pure
          wp_pure
          wp_bind &Impl.revokeSuffix _
          unfold Impl.revokeSuffix at ih
          iapply ih nv $$ [Hnext Hrest]
          · iframe
          iintro !> Hretired
          wp_pures
          -- drop our reference; whether it was the last one decides which side of
          -- `retiredSlot` we can produce
          iunfold arcHasStrong at Hstrong
          icases Hstrong with ⟨%n, %m, Hauth, %hn⟩
          ihave Hpd : (⦃ isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗
                          d.ptr ↦ hl_val((#true, (#d.val, none()))) ⦄
                          hl(&RwLock.drop &d.mux)
                        ⦃ RET hl_val(#()); True ⦄) $$ []
          · iapply RwLock.ptr_drop_spec d.rw d.mux d.ptr
              hl_val((#true, (#d.val, none())))
          by_cases hn1 : n = 1
          · -- ours was the last reference: the payload is freed and the arc dies
            subst hn1
            iapply Arc.drop_spec (γ := d.arc) RwLock.drop w d.mux 1 m
              (iprop% isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗
                      d.ptr ↦ hl_val((#true, (#d.val, none())))) $$ Hpd
              [HArc Hauth Hlock Hptr]
            · iframe HArc Hauth
              rw [if_pos rfl]
              iframe Hlock Hptr
            iintro !> Hauth
            iapply HΦ
            iapply BigSepL.bigSepL_cons.mpr
            isplitl [Hauth]
            · iexists d
              isplitl []
              · iexact Hat
              unfold retiredSlot
              isplitl []
              · iexact Hcd
              iright
              unfold arcNoStrong
              iexists m
              iexact Hauth
            · iexact Hretired
          · -- somebody else still holds a reference: the slot survives, revoked
            iapply Arc.drop_spec (γ := d.arc) RwLock.drop w d.mux n m
              (iprop% isRwLock d.rw d.mux .free hl_val(#d.ptr) ∗
                      d.ptr ↦ hl_val((#true, (#d.val, none())))) $$ Hpd
              [HArc Hauth]
            · iframe HArc Hauth
              rw [if_neg hn1]
              itrivial
            iintro !> Hauth
            iapply HΦ
            iapply BigSepL.bigSepL_cons.mpr
            isplitl [Hauth Hlock Hptr]
            · iexists d
              isplitl []
              · iexact Hat
              unfold retiredSlot
              isplitl []
              · iexact Hcd
              ileft
              unfold nodeSlotExclusive revokedPayload
              isplitl [Hauth]
              · unfold arcHasStrong
                iexists (n - 1), m
                iframe Hauth
                ipureintro
                omega
              iframe Hlock
              isplit
              · itrivial
              isplitl []
              · iexact Hcd
              · iexact Hptr
            · iexact Hretired

/-- What `Impl.revoke`'s body achieves, in the shape `Impl.execute_exclusive_spec`
    wants.  Unlike insert this runs under the platform *write* lock, so the body is
    an ordinary Hoare triple on `arrContent` — no atomic update, no invariant. -/
def Impl.revokeQ (γ : Arrγ) (node : Val) (id : Nat)
    (σ σ' : Arr) (ret : Val) : IProp GF := iprop%
  ⌜σ' = (Arr.revoke σ id).1⌝ ∗
  Arr.isId γ node id ∗
  ⌜ret = match (Arr.revoke σ id).2 with
         | none => hl_val(none())
         | some _ => hl_val(some(#()))⌝

theorem Impl.revoke_spec (N : Namespace)
    (γ : Arrγ) (γp : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv N γ γp platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&Impl.revoke &platform &node) @ ↑N
    ⟪ arrFrag γ (Arr.revoke σ id).1 ∗ Arr.isId γ node id
      | RET match (Arr.revoke σ id).2 with
            | none => hl_val(none())
            | some _ => hl_val(some(#()))
    ⟫ := by
  iintro #Hinv Hid %Φ HAU
  unfold Impl.revoke
  wp_pures
  iapply Impl.execute_exclusive_spec N γ γp platform _ (Impl.revokeQ γ node id)
    $$ Hinv [Hid]
  · -- the body, running with exclusive access to the whole content
    iintro %σ %Φ' Hcontent HΦ'
    iunfold arrContent at Hcontent
    icases Hcontent with ⟨%M, Hcontent⟩
    iunfold arrContentAt at Hcontent
    icases Hcontent with ⟨HM, %hwf, %hdom, Hview⟩
    iunfold Arr.isId at Hid
    icases Hid with ⟨%d, #Hat, HArc⟩
    ihave #Hl : ⌜get? M id = some d⌝ $$ [HM Hat]
    · iapply metaMap_lookup γ.l M id d $$ HM Hat
    icases Hl with %Hl
    wp_pures
    wp_bind &Arc.get _
    iapply Arc.get_spec (γ := d.arc) node d.mux $$ HArc
    iintro !> HArc
    wp_pures
    -- locate this node's slot: live cells sit in `isGhost`, retired ones in `retiredNodes`
    iunfold exclusiveView at Hview
    icases Hview with ⟨Hghost, Hretired⟩
    by_cases hin : id ∈ σ.cells.map (·.1)
    · -- the node is live, so revoking it really does shrink the array
      obtain ⟨pre, xv, post, hsplit⟩ := Arr.exists_split_id hin
      ihave Hghost' : isGhostHelp nodeSlotExclusive γ.l none (pre ++ (id, xv) :: post)
          $$ [Hghost]
      · iunfold isGhost at Hghost
        rw [← hsplit]
        iexact Hghost
      ihave Hacc := isGhostHelpAccTruncate γ.l d nodeSlotExclusive none id xv post pre
                      $$ Hat Hghost'
      icases Hacc with ⟨Hslot, Hpost, Hback⟩
      iunfold aliveSlot at Hslot
      iunfold nodeSlotExclusive at Hslot
      icases Hslot with ⟨Hstrong, Hlock, Hcell, HP⟩
      -- take the node's lock (we own it outright, the platform is write-locked)
      wp_bind &RwLock.write_acquire _
      iapply RwLock.write_acquire_spec d.rw d.mux hl_val(#d.ptr)
      iauintro
      iaaccintro' with Hlock
      · iintro Hlock
        imodintro
        iframe
        isplitl []
        · imodintro; iexact Hinv
        · imodintro; iexact Hat
      · itele_reduce
        iintro Hpost'
        icases Hpost' with ⟨Hlock, Hwguard, -⟩
        imodintro
        iframe
        wp_pures
        ihave Hsplit := livePayload_split γ.l d (nextIdOr post none) $$ HP
        icases Hsplit with ⟨%nv, Hptr, Hnext⟩
        wp_bind !_
        iapply wp_load $$ Hptr
        iintro !> Hptr
        wp_pures
        -- cut the link: the node stays alive but loses its successor
        wp_bind (_ ← _)
        iapply wp_store $$ Hptr
        iintro !> Hptr
        wp_pures
        imod cellAlive_update d.cell (nextIdOr post none) none $$ [Hcell] with Hcell
        · iapply (cellAlive_split d.cell (nextIdOr post none)).mp $$ Hcell
        icases Hcell with ⟨Hc14, Hc34⟩
        ihave Hcell := (cellAlive_split d.cell none).mpr $$ [Hc14 Hc34]
        · isplitl [Hc14] <;> iassumption
        wp_bind &RwLock.write_release _
        iapply RwLock.write_release_spec d.rw d.mux hl_val(#d.ptr) $$ Hwguard
        iauintro
        iaaccintro' with Hlock
        · iintro Hlock
          imodintro
          iframe
          isplitl []
          · imodintro; iexact Hinv
          · imodintro; iexact Hat
        · itele_reduce
          iintro Hlock
          imodintro
          iframe
          wp_pure
          wp_pure
          -- retire everything after this node
          wp_bind &Impl.revokeSuffix _
          iapply Impl.revokeSuffix_spec γ post nv $$ [Hnext Hpost]
          · iframe
          iintro !> Hsuffix
          wp_pures
          -- the abstract step: `id` keeps its value, everything after it is gone
          obtain ⟨hpre, -⟩ := Arr.nodup_split_id pre post id xv (hsplit ▸ hwf.idUqi)
          have hrev := Arr.revoke_eq_of_split σ pre post id xv hsplit hpre
          have hnd0 : ((pre ++ (id, xv) :: post).map (·.1)).Nodup := hsplit ▸ hwf.idUqi
          rw [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnd0
          obtain ⟨-, ⟨hidpost, hpostnd⟩, hdisj0⟩ := hnd0
          -- put this node's slot back, now with an empty tail
          ihave Hslot : aliveSlot nodeSlotExclusive γ.l d none $$ [Hstrong Hlock Hcell Hptr]
          · unfold aliveSlot nodeSlotExclusive livePayload
            iframe Hstrong Hlock Hcell
            iexact Hptr
          ihave Hghost := Hback $$ Hslot
          -- file the retired suffix
          ihave ⟨HM, Hsuffix⟩ := retireList_lookup γ.l nodeSlotExclusive M post
            $$ HM Hsuffix
          ihave Hretired := retiredNodes_retire nodeSlotExclusive (pre ++ [(id, xv)])
            post M σ.cells
            (by
              intro k _ _
              rw [hsplit]
              simp [List.map_append, or_assoc])
            (by
              intro k hk hkp
              rw [List.map_append] at hk
              rcases List.mem_append.mp hk with h | h
              · exact hdisj0 k h k (List.mem_cons_of_mem _ hkp) rfl
              · have hki : k = id := by simpa using h
                exact hidpost (hki ▸ hkp))
            hpostnd $$ [Hretired Hsuffix]
          · isplitl [Hretired] <;> iassumption
          imodintro
          iapply HΦ'
          iexists { cells := pre ++ [(id, xv)], counter := σ.counter }
          isplitl [HM Hghost Hretired]
          · unfold arrContent arrContentAt exclusiveView isGhost
            iexists M
            iframe HM Hghost Hretired
            isplit
            · ipureintro
              have := Arr.revoke_wellFormed σ hwf id
              rw [hrev] at this
              exact this
            · ipureintro
              exact hdom
          · unfold Impl.revokeQ Arr.isId
            rw [hrev]
            isplitl []
            · itrivial
            isplitl [Hat HArc]
            · iexists d
              iframe Hat HArc
            · itrivial
    · -- already revoked: `Arr.revoke` is the identity here
      have hrev := Arr.revoke_eq_none σ id hin
      ihave ⟨Hslot, Hback⟩ := retiredNodesAccNotIn Hl hin $$ Hretired
      iunfold retiredSlot at Hslot
      icases Hslot with ⟨#Hcd, Hlive | Hdead⟩
      · -- the node is still there, just flagged revoked
        iunfold nodeSlotExclusive at Hlive
        icases Hlive with ⟨Hstrong, Hlock, -, HP⟩
        iunfold revokedPayload at HP
        icases HP with ⟨-, Hptr⟩
        wp_bind &RwLock.write_acquire _
        iapply RwLock.write_acquire_spec d.rw d.mux hl_val(#d.ptr)
        iauintro
        iaaccintro' with Hlock
        · iintro Hlock
          imodintro
          iframe
          repeat' first | (imodintro; iassumption) | isplitl []
        · itele_reduce
          iintro Hpost'
          icases Hpost' with ⟨Hlock, Hwguard, -⟩
          imodintro
          iframe
          wp_pures
          wp_bind !_
          iapply wp_load $$ Hptr
          iintro !> Hptr
          wp_pures
          wp_bind &RwLock.write_release _
          iapply RwLock.write_release_spec d.rw d.mux hl_val(#d.ptr) $$ Hwguard
          iauintro
          iaaccintro' with Hlock
          · iintro Hlock
            imodintro
            iframe
            repeat' first | (imodintro; iassumption) | isplitl []
          · itele_reduce
            iintro Hlock
            imodintro
            iframe
            wp_pures
            -- everything goes back exactly where it came from
            ihave Hretired := Hback $$ [Hstrong Hlock Hptr]
            · unfold retiredSlot nodeSlotExclusive revokedPayload
              isplitl []
              · iexact Hcd
              ileft
              iframe Hstrong Hlock Hptr
              iexact Hcd
            imodintro
            iapply HΦ'
            iexists σ
            isplitl [HM Hghost Hretired]
            · unfold arrContent arrContentAt exclusiveView
              iexists M
              iframe HM Hghost Hretired
              isplit
              · ipureintro; exact hwf
              · ipureintro; exact hdom
            · unfold Impl.revokeQ Arr.isId
              rw [hrev]
              isplitl []
              · itrivial
              isplitl [Hat HArc]
              · iexists d
                iframe Hat HArc
              · itrivial

      · -- the arc handle we hold rules out the "no strong reference" case
        -- the arc handle we hold rules out the "no strong reference" case
        iexfalso
        iapply arcNoStrong_isArc_False d.arc node d.mux $$ [Hdead HArc]
        · iframe

  · -- our own update backs the one `execute` wants; the return value is computed
    -- from `σ`, so the telescopes differ and this has to be built by hand
    iauintro
    simp only [atomicAcc]
    iauopen HAU with ⟨%σ, Hfrag, Hclose⟩
    imodintro
    iexists σ
    isplitl [Hfrag]
    · iexact Hfrag
    · isplit
      · iintro Hfrag
        icases Hclose with ⟨Habort, -⟩
        imod Habort $$ Hfrag with HAU
        imodintro
        iframe
        imodintro
        iexact Hinv
      · itele_reduce
        iintro %r Hbeta
        iunfold Impl.revokeQ at Hbeta
        icases Hbeta with ⟨%σ', Hfrag', %hσ', Hid, %hr⟩
        subst hσ'
        subst hr
        icases Hclose with ⟨-, Hcommit⟩
        ihave Hb : (arrFrag γ (Arr.revoke σ id).1 ∗ Arr.isId γ node id)
            $$ [Hfrag' Hid]
        · iframe
        imod Hcommit $$ Hb with HΦ
        imodintro
        iexact HΦ

end Specs

end Iris.Examples.HeapLang
