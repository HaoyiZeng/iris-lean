module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Lib.SpinLock
public import Iris.HeapLang.Lib.IInv
public import Iris.Algebra.Lib.ExclAuth
public import Iris.ProgramLogic.Atomic

@[expose] public section
namespace Iris.Examples.HeapLang

/-
================================================================================
  ArrayCopy — logically-atomic singly-linked list with per-node locks
  Line statistics (approx., by section):

    Abstract model + pure list helpers ....  278   (Arr, init/insert/remove,
                                                     adjacent, wellFormed, flatMap)
    HeapLang implementations ..............   41   (Impl.init/insert/remove)
    RA layer (ghost state) ................  145   (dataMap, dataPointsto,
                                                     arrRoot, arrState + lemmas)
    Lock invariant (isArrLockINV) .........   77   (pre + contractive + unfold
                                                     + shared lockBody def)
    contents predicate + lemmas ...........  207   (incl. insert/removeAfter extract)
    Core predicates .......................   65   (isArrINV incl. wellFormed,
                                                     isArr, isContents, idRecord)
    ------------------------------------------------
    init_spec   proof .....................   79
    insert_spec proof .....................  366   (incl. AU double-open PEEK)
    remove_spec proof .....................  386   (incl. AU double-open PEEK)
    ------------------------------------------------
    Total (this file) ..................... 1758
    Clients (ArrayCopyClient.lean) ........  165   (seq + concurrent, verified)
================================================================================
-/

/-
================================================================================
  RESULTS — the proven specifications (the specs are the point; proofs are boring)
================================================================================

  Abstract state.  `σ : Arr` is the ordered association list `cells : List (Nat × Int)`
  (logical id ↦ value) plus a monotone `counter` for fresh ids.
    · `Arr.init x`        = the one-element list `[(0, x)]`.
    · `σ.insert id x`     = insert value `x` right after the node with id `id`
                            (fresh id `= σ.counter`).
    · `σ.remove sid`      = delete the node with id `sid`.
    · `Arr.adjacent σ id sid` ⟺ `sid` immediately follows `id` in `σ.cells`.

  Client-facing predicates.
    · `Arr.isArr γ`            : persistent handle to the whole structure (γ).
    · `Arr.isContents γ σ`     : the structure currently represents abstract list `σ`
                                 (exclusive; this is what the atomic specs mutate).
    · `Arr.idRecord γ node id` : a durable, transferable capability for the node `node`
                                 with logical id `id` (holds its "alive" ¼-token + lock).

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ init_spec  (ordinary Hoare triple)                                         │
  └──────────────────────────────────────────────────────────────────────────┘
    ⦃ True ⦄
      &Impl.init #x
    ⦃ v, RET v; ∃ γ, isArr γ ∗ isContents γ (Arr.init x) ∗ idRecord γ v 0 ⦄

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ insert_spec  (logically atomic; inserts after node `id`)                   │
  └──────────────────────────────────────────────────────────────────────────┘
    isArr γ  -∗
      ⟪ ∀ σ, isContents γ σ ∗ idRecord γ node id ⟫
        &Impl.insert &node #x @ arrN
      ⟪ ∃ nid, isContents γ (σ.insert id x) ∗ idRecord γ node id ∗ ⌜nid = σ.counter⌝
        | ret, RET ret; idRecord γ ret nid ⟫

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ remove_spec  (logically atomic; remove-AFTER: unlinks node's successor)    │
  └──────────────────────────────────────────────────────────────────────────┘
    isArr γ  -∗
      ⟪ ∀ σ, isContents γ σ ∗ idRecord γ node id ∗ idRecord γ snode sid ∗ ⌜adjacent σ id sid⌝ ⟫
        &Impl.remove &node @ arrN
      ⟪ isContents γ (σ.remove sid) ∗ idRecord γ node id | RET #() ⟫

  Notes.
    · The node record(s) live *inside* the atomic precondition, so these are fully
      general logically-atomic specs: a client may keep `idRecord` in shared state
      and only produce it at the linearization point (the proof double-opens the AU
      to grab the node's *persistent* lock before the LP; see the PEEK in each proof).
    · Well-formedness (`Nodup` ids, fresh counter) is maintained *inside* the shared
      invariant, so callers never supply or track it.
    · Returned ids are *concrete*: `init` names the root `0` and `insert` pins the new
      node to `σ.counter`, so a client can later `remove` a node it inserted.
    · `remove` consumes `snode`'s record (logically deleting `sid`) and returns
      `node`'s record; `snode` is a logical-only parameter (its `Val` is irrelevant).

  Clients (in ArrayCopyClient.lean, all verified).
    · Impl.insert_hoare   : collapses insert_spec to a sequential Hoare triple
                            (atomicWP_seq), supplying `isContents ∗ idRecord` privately.
    · Impl.seqClient_spec : init then two inserts ⊢ ∃ γ σ, isContents γ σ.
    · Impl.insert_conc    : one thread inserts against a shared invariant
                            `inv (∃ σ, isContents γ σ)`, threading its own `idRecord`
                            through the AU's coinductive frame (LP at the commit).
    · Impl.parClient_spec : two threads insert concurrently (via `par`); the shared
                            invariant is preserved across every interleaving.
================================================================================
-/

structure Arr where
  cells : List (Nat × Int)
  counter : Nat

def Arr.idUqi (arr : Arr) : Prop := (arr.cells.map (·.1)).Nodup

structure Arr.wellFormed (arr : Arr) : Prop where
  idUqi : arr.idUqi
  counterFresh : ∀ p ∈ arr.cells, p.1 < arr.counter

def Arr.init (x : Int) : Arr := { cells := [(0, x)], counter := 1 }

def Arr.insert (arr : Arr) (id : Nat) (val : Int) : Arr :=
  if arr.cells.any (·.1 = id)
    then {
      cells := arr.cells.flatMap λ c => if c.1 = id then [c, (arr.counter, val)] else [c],
      counter := arr.counter + 1
    }
    else arr

def Arr.remove (arr : Arr) (id : Nat) : Arr :=
  { cells := arr.cells.filter (·.1 ≠ id), counter := arr.counter }

/-- `sid` immediately follows `id` in `σ.cells` (so `remove node` — which unlinks node's
successor — logically removes the cell with id `sid`). -/
def Arr.adjacent (σ : Arr) (id sid : Nat) : Prop :=
  ∃ (pre post : List (Nat × Int)) (x sx : Int), σ.cells = pre ++ (id, x) :: (sid, sx) :: post

/-- Membership of ids in `σ.remove sid`: everything except `sid`. -/
theorem Arr.remove_ids_mem (σ : Arr) (sid : Nat) (id' : Nat) :
    id' ∈ (σ.remove sid).cells.map (·.1) ↔ (id' ≠ sid ∧ id' ∈ σ.cells.map (·.1)) := by
  unfold Arr.remove
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, hps⟩, hpid⟩; exact ⟨hpid ▸ hps, p, hp, hpid⟩
  · rintro ⟨hne, p, hp, hpid⟩; exact ⟨p, ⟨hp, hpid ▸ hne⟩, hpid⟩

/-- From `Nodup`, `sid` (at its unique position) differs from every other cell id. -/
theorem Arr.nodup_ne_sid (id sid : Nat) (x sx : Int) (pre post : List (Nat × Int))
    (hnd : ((pre ++ (id, x) :: (sid, sx) :: post).map (·.1)).Nodup) :
    id ≠ sid ∧ (∀ a ∈ pre, a.1 ≠ sid) ∧ (∀ a ∈ post, a.1 ≠ sid) := by
  rw [List.map_append, List.map_cons, List.map_cons, List.nodup_append] at hnd
  obtain ⟨hpre, hrest, hdisj⟩ := hnd
  rw [List.nodup_cons, List.nodup_cons] at hrest
  obtain ⟨hid, hsid, _⟩ := hrest
  refine ⟨?_, ?_, ?_⟩
  · intro heq; exact hid (by rw [heq]; exact List.mem_cons_self)
  · intro a ha heq
    have hmem2 : a.1 ∈ (id :: sid :: post.map (·.1)) := by
      simp only [List.mem_cons]; right; left; exact heq
    exact hdisj a.1 (List.mem_map.mpr ⟨a, ha, rfl⟩) a.1 hmem2 rfl
  · intro a ha heq
    exact hsid (by rw [← heq]; exact List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- Removing `sid` (which sits right after `id`) from the list. -/
theorem Arr.filter_removeAfter (id sid : Nat) (x sx : Int) :
    ∀ (pre post : List (Nat × Int)),
      id ≠ sid → (∀ a ∈ pre, a.1 ≠ sid) → (∀ a ∈ post, a.1 ≠ sid) →
      (pre ++ (id, x) :: (sid, sx) :: post).filter (·.1 ≠ sid) = pre ++ (id, x) :: post := by
  intro pre
  induction pre with
  | nil =>
    intro post hid hpre hpost
    simp only [List.nil_append]
    rw [List.filter_cons_of_pos (by simpa using hid),
        List.filter_cons_of_neg (by simp),
        List.filter_eq_self.mpr (fun a ha => by simpa using hpost a ha)]
  | cons c pre' ih =>
    intro post hid hpre hpost
    simp only [List.cons_append]
    rw [List.filter_cons_of_pos (by simpa using hpre c List.mem_cons_self),
        ih post hid (fun a ha => hpre a (List.mem_cons_of_mem _ ha)) hpost]

/-- Removing an element strictly after the head keeps the same head. -/
theorem Arr.append_cons_head {α : Type _} : ∀ (pre : List α) (a : α) (r1 r2 : List α),
    ∃ (h : α) (t1 t2 : List α), pre ++ a :: r1 = h :: t1 ∧ pre ++ a :: r2 = h :: t2
  | [], a, r1, r2 => ⟨a, r1, r2, rfl, rfl⟩
  | c :: cs, a, r1, r2 => ⟨c, cs ++ a :: r1, cs ++ a :: r2, rfl, rfl⟩

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

theorem Arr.flatMap_insert_head (id counter : Nat) (xnew cx : Int) (cs : List (Nat × Int))
    (htl : ∀ y ∈ cs, y.1 ≠ id) :
    ((id, cx) :: cs).flatMap (Arr.insertBody id counter xnew)
      = (id, cx) :: (counter, xnew) :: cs := by
  rw [List.flatMap_cons, Arr.flatMap_no_match id counter xnew cs htl]
  simp [Arr.insertBody]

theorem Arr.flatMap_skip_head (id counter : Nat) (xnew : Int) (c : Nat × Int)
    (cs : List (Nat × Int)) (hne : c.1 ≠ id) :
    (c :: cs).flatMap (Arr.insertBody id counter xnew)
      = c :: cs.flatMap (Arr.insertBody id counter xnew) := by
  rw [List.flatMap_cons]
  unfold Arr.insertBody; rw [if_neg hne]; rfl

theorem Arr.flatMap_ne_nil (id counter : Nat) (xnew : Int) (c : Nat × Int)
    (cs : List (Nat × Int)) :
    (c :: cs).flatMap (Arr.insertBody id counter xnew) ≠ [] := by
  rw [List.flatMap_cons]
  unfold Arr.insertBody
  by_cases h : c.1 = id <;> simp [h]

/-- Splicing keeps the head cell as the first element: `(c :: cs)` splices to `c :: ds`. -/
theorem Arr.flatMap_cons_head (id counter : Nat) (xnew : Int) (c : Nat × Int)
    (cs : List (Nat × Int)) :
    ∃ ds, (c :: cs).flatMap (Arr.insertBody id counter xnew) = c :: ds := by
  rw [List.flatMap_cons]
  unfold Arr.insertBody
  by_cases h : c.1 = id
  · rw [if_pos h]; exact ⟨(counter, xnew) :: cs.flatMap (Arr.insertBody id counter xnew), rfl⟩
  · rw [if_neg h]; exact ⟨cs.flatMap (Arr.insertBody id counter xnew), rfl⟩

theorem Arr.insert_cells_eq (σ : Arr) (id : Nat) (x : Int) (hmem : id ∈ σ.cells.map (·.1)) :
    (σ.insert id x).cells = σ.cells.flatMap (Arr.insertBody id σ.counter x) := by
  unfold Arr.insert
  have hany : σ.cells.any (·.1 = id) = true := by
    obtain ⟨p, hp, hpid⟩ := List.mem_map.mp hmem
    rw [List.any_eq_true]; exact ⟨p, hp, by simp [hpid]⟩
  rw [if_pos hany]; rfl

theorem Arr.insert_ids_mem (σ : Arr) (id : Nat) (x : Int) (hmem : id ∈ σ.cells.map (·.1)) (id' : Nat) :
    id' ∈ (σ.insert id x).cells.map (·.1) ↔ (id' = σ.counter ∨ id' ∈ σ.cells.map (·.1)) := by
  rw [Arr.insert_cells_eq σ id x hmem]
  constructor
  · intro h
    rcases Arr.mem_ids_flatMap id σ.counter x σ.cells id' h with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  · intro h
    rcases h with h | h
    · subst h
      obtain ⟨p, hp, hpid⟩ := List.mem_map.mp hmem
      rw [List.mem_map]
      refine ⟨(σ.counter, x), ?_, rfl⟩
      rw [List.mem_flatMap]
      refine ⟨p, hp, ?_⟩
      unfold Arr.insertBody; rw [if_pos hpid]; simp
    · obtain ⟨p, hp, hpid⟩ := List.mem_map.mp h
      rw [List.mem_map]
      refine ⟨p, ?_, hpid⟩
      rw [List.mem_flatMap]
      refine ⟨p, hp, ?_⟩
      unfold Arr.insertBody; by_cases hc : p.1 = id <;> simp [hc]

theorem Arr.insert_counter (σ : Arr) (id : Nat) (x : Int) (hmem : id ∈ σ.cells.map (·.1)) :
    (σ.insert id x).counter = σ.counter + 1 := by
  unfold Arr.insert
  have hany : σ.cells.any (·.1 = id) = true := by
    obtain ⟨p, hp, hpid⟩ := List.mem_map.mp hmem
    rw [List.any_eq_true]; exact ⟨p, hp, by simp [hpid]⟩
  rw [if_pos hany]

def Arr.init_wellFormed (x : Int) : Arr.wellFormed <| Arr.init x := {
  idUqi := by simp [Arr.init, Arr.idUqi]
  counterFresh := by simp [Arr.init]
}

def Arr.insert_wellFormed (arr : Arr) (h : arr.wellFormed) (id : Nat) (val : Int) :
    (Arr.insert arr id val).wellFormed := {
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


def Arr.remove_wellFormed (arr : Arr) (h : arr.wellFormed) (id : Nat) :
    (Arr.remove arr id).wellFormed := {
  idUqi := by
    unfold Arr.remove Arr.idUqi
    have s : List.Sublist ((arr.cells.filter (·.1 ≠ id)).map (·.1)) (arr.cells.map (·.1)) :=
      (List.filter_sublist (l := arr.cells)).map (·.1)
    exact s.nodup h.idUqi
  counterFresh := by
    intro p hp
    simp only [Arr.remove, List.mem_filter] at hp
    exact h.counterFresh p hp.1
}

open Iris.HeapLang
open SpinLock


def Impl.init : Val := hl_val%
  λ x,
    let lk := &newlock #();
    let c  := ref((x, none()));
    (lk, c)

def Impl.insert : Val := hl_val%
  λ node nval,
    let lk := fst(node);
    &acquire(lk);
    let ptr := snd(node);
    let contents := !ptr;
    let val := fst(contents);
    let next := snd(contents);
    -- create a new node with the new value and the old next pointer
    let nlk := &newlock #();
    let nptr := ref((nval, next));
    let nnode := (nlk, nptr);
    let ncontents := (val, some(nnode));
    ptr ← ncontents;
    &release(lk);
    nnode

def Impl.remove : Val := hl_val%
  λ node,
    let lk := fst(node);
    &acquire(lk);
    let ptr := snd(node);
    let contents := !ptr;
    let next := snd(contents);
    match next with
    | none() => &release(lk)
    | some(nnode) =>
      let nlk := fst(nnode);
      &acquire(nlk);
      let nptr := snd(nnode);
      let ncontents := !nptr;
      let nnext := snd(ncontents);
      ptr ← (fst(contents), nnext);
      &release(nlk);
      &release(lk)

section Specs

open Std PartialMap

abbrev ArrNameRF : COFE.OFunctorPre :=
  constOF (Agree (LeibnizO (Val × GName × GName)))

-- abstract-state ghost variable (ExclAuth over the whole Arr): authority in the invariant,
-- fragment in isContents — lets the invariant learn σ (incl σ.counter) at the linearization point.
abbrev ArrStateRF : COFE.OFunctorPre :=
  constOF (ExclAuth.ExclAuthR (A := LeibnizO Arr))

class ArrG (GF : BundledGFunctors) (H': outParam <| Type → Type) [LawfulFiniteMap H' Nat] where
  [dmapG : GhostMapG GF Nat (Loc × Int × Option Nat × Bool) H']
  [rootG : ElemG GF ArrNameRF]
  [stateG : ElemG GF ArrStateRF]

attribute [reducible, instance] ArrG.dmapG ArrG.rootG ArrG.stateG
open Iris.BI

section RA
variable [LawfulFiniteMap H' Nat] [ArrG GF H']

/-- 1/2 and 1/4 fractions used to split each node's `dataPointsto`. -/
abbrev q2 : Qp := Qp.half 1
abbrev q4 : Qp := Qp.half (Qp.half 1)

theorem q4_add_q4 : q4 + q4 = q2 := Qp.half_add_half _
theorem q2_add_q2 : q2 + q2 = 1 := Qp.half_add_half _

-- ===== the single id-keyed node map  (Nat → (Loc × Int × Option Nat × Bool)) =====
-- `dataPointsto γ id loc val succ π` : node with logical `id` lives at physical `loc`,
-- currently holds `val` and points to successor `succ`.  Fractionally split:
--   lock 1/2  +  contents 1/4  +  idRecord 1/4  (the "live token").
def dataMap (γ : GName) (m : H' (Loc × Int × Option Nat × Bool)) : IProp GF := γ ↪●MAP m
def dataPointsto (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (al : Bool) (π : DFrac) : IProp GF :=
  γ ↪◯MAP[id]{π} (loc, v, sl, al)

theorem dataMap_alloc : ⊢@{IProp GF} |==> ∃ γ, dataMap γ (∅ : H' (Loc × Int × Option Nat × Bool)) := by
  unfold dataMap; iapply ghost_map_alloc_empty
theorem dataMap_lookup (γ : GName) (m : H' (Loc × Int × Option Nat × Bool)) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (al : Bool) (π : DFrac) :
    ⊢@{IProp GF} dataMap γ m -∗ dataPointsto γ id loc v sl al π -∗ ⌜get? m id = some (loc, v, sl, al)⌝ := by
  unfold dataMap dataPointsto; iapply ghost_map_lookup
theorem dataPointsto_agree (γ : GName) (id : Nat) (l1 l2 : Loc) (v1 v2 : Int) (s1 s2 : Option Nat) (a1 a2 : Bool) (π1 π2 : DFrac) :
    ⊢@{IProp GF} dataPointsto γ id l1 v1 s1 a1 π1 -∗ dataPointsto γ id l2 v2 s2 a2 π2 -∗ ⌜l1 = l2 ∧ v1 = v2 ∧ s1 = s2 ∧ a1 = a2⌝ := by
  unfold dataPointsto
  iintro H1 H2
  icases ghost_map_elem_agree $$ [$H1 $H2] with %Heq
  ipureintro; injection Heq with h1 h; injection h with h2 h; injection h with h3 h4; exact ⟨h1, h2, h3, h4⟩
theorem dataMap_insert (γ : GName) (m : H' (Loc × Int × Option Nat × Bool)) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (al : Bool)
    (Hfresh : get? m id = none) :
    ⊢@{IProp GF} dataMap γ m ==∗ dataMap γ (insert m id (loc, v, sl, al)) ∗ dataPointsto γ id loc v sl al (.own 1) := by
  unfold dataMap dataPointsto; iapply (ghost_map_insert id (loc, v, sl, al) Hfresh)
theorem dataMap_update (γ : GName) (m : H' (Loc × Int × Option Nat × Bool)) (id : Nat) (loc : Loc) (v : Int) (sl sl' : Option Nat) (al al' : Bool) :
    ⊢@{IProp GF} dataMap γ m -∗ dataPointsto γ id loc v sl al (.own 1) ==∗
      dataMap γ (insert m id (loc, v, sl', al')) ∗ dataPointsto γ id loc v sl' al' (.own 1) := by
  unfold dataMap dataPointsto; iapply (ghost_map_update (loc, v, sl', al'))
theorem dataMap_delete (γ : GName) (m : H' (Loc × Int × Option Nat × Bool)) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (al : Bool) :
    ⊢@{IProp GF} dataMap γ m -∗ dataPointsto γ id loc v sl al (.own 1) ==∗ dataMap γ (delete m id) := by
  unfold dataMap dataPointsto; iapply (ghost_map_delete id (loc, v, sl, al))
instance (γ : GName) (m : H' (Loc × Int × Option Nat × Bool)) : Timeless (PROP := IProp GF) (dataMap γ m) := by
  unfold dataMap; infer_instance
instance (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (al : Bool) (π : DFrac) : Timeless (PROP := IProp GF) (dataPointsto γ id loc v sl al π) := by
  unfold dataPointsto; infer_instance

/-- fractional structure: split/combine a full node fragment along `q1 + q2`. -/
theorem dataPointsto_frac (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (al : Bool) (p q : Qp) :
    (dataPointsto γ id loc v sl al (.own (p + q)) : IProp GF) ⊣⊢
      dataPointsto γ id loc v sl al (.own p) ∗ dataPointsto γ id loc v sl al (.own q) :=
  (@ghost_map_elem_fractional GF Nat (Loc × Int × Option Nat × Bool) H' _ _ γ id (loc, v, sl, al)).fractional p q

theorem one_eq_q2_q4_q4 : (1 : Qp) = q2 + (q4 + q4) := by rw [q4_add_q4, q2_add_q2]

/-- Split a full node share into lock 1/2 + contents 1/4 + record 1/4. -/
theorem data_split3 (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (al : Bool) :
    (dataPointsto γ id loc v sl al (.own 1) : IProp GF) ⊢
      dataPointsto γ id loc v sl al (.own q2) ∗ dataPointsto γ id loc v sl al (.own q4) ∗ dataPointsto γ id loc v sl al (.own q4) := by
  rw [one_eq_q2_q4_q4]
  iintro H
  icases (dataPointsto_frac γ id loc v sl al q2 (q4 + q4)).mp $$ H with ⟨H1, H2⟩
  icases (dataPointsto_frac γ id loc v sl al q4 q4).mp $$ H2 with ⟨H3, H4⟩
  iframe H1 H3 H4

/-- Combine lock 1/2 + contents 1/4 + record 1/4 (same value) into a full node share. -/
theorem data_combine3 (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (al : Bool) :
    (dataPointsto γ id loc v sl al (.own q2) ∗ dataPointsto γ id loc v sl al (.own q4) ∗ dataPointsto γ id loc v sl al (.own q4) : IProp GF) ⊢
      dataPointsto γ id loc v sl al (.own 1) := by
  rw [one_eq_q2_q4_q4]
  iintro ⟨H1, H3, H4⟩
  iapply (dataPointsto_frac γ id loc v sl al q2 (q4 + q4)).mpr
  iframe H1
  iapply (dataPointsto_frac γ id loc v sl al q4 q4).mpr
  iframe H3 H4


def arrRoot (γ : GName) (v : Val) (γL γS : GName) : IProp GF :=
  iOwn (E := ArrG.rootG) γ (toAgree (⟨(v, γL, γS)⟩ : LeibnizO _))

def arrState     (γ : GName) (σ : Arr) : IProp GF := iOwn (E := ArrG.stateG) γ (ExclAuth.auth (⟨σ⟩ : LeibnizO Arr))
def arrStateFrag (γ : GName) (σ : Arr) : IProp GF := iOwn (E := ArrG.stateG) γ (ExclAuth.frag (⟨σ⟩ : LeibnizO Arr))

theorem arrState_alloc (σ : Arr) :
    ⊢@{IProp GF} |==> ∃ γ, arrState γ σ ∗ arrStateFrag γ σ := by
  unfold arrState arrStateFrag
  imod (iOwn_alloc (E := ArrG.stateG) (ExclAuth.auth (⟨σ⟩ : LeibnizO Arr) • ExclAuth.frag (⟨σ⟩ : LeibnizO Arr)) ExclAuth.valid) with ⟨%γ, H⟩
  imodintro; iexists γ; iapply iOwn_op.mp $$ H
theorem arrState_agree (γ : GName) (σ σ' : Arr) :
    ⊢@{IProp GF} arrState γ σ -∗ arrStateFrag γ σ' -∗ ⌜σ = σ'⌝ := by
  unfold arrState arrStateFrag
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact congrArg LeibnizO.car (ExclAuth.agree_L Hvalid)
theorem arrState_update (γ : GName) (σ σ' : Arr) :
    ⊢@{IProp GF} arrState γ σ -∗ arrStateFrag γ σ ==∗ arrState γ σ' ∗ arrStateFrag γ σ' := by
  unfold arrState arrStateFrag
  iintro H1 H2
  ihave H := iOwn_op.mpr $$ [$H1 $H2]
  imod (iOwn_update (ExclAuth.update (a' := (⟨σ'⟩ : LeibnizO Arr)))) $$ H with H
  imodintro; iapply iOwn_op.mp $$ H
instance (γ : GName) (σ : Arr) : Timeless (PROP := IProp GF) (arrState γ σ) := by
  unfold arrState; infer_instance
instance (γ : GName) (σ : Arr) : Timeless (PROP := IProp GF) (arrStateFrag γ σ) := by
  unfold arrStateFrag; infer_instance

-- ===== root binding (Agree, immutable ⇒ no update/insert/delete) =====
theorem arrRoot_alloc (v : Val) (γL γS : GName) :
    ⊢@{IProp GF} |==> ∃ γ, arrRoot γ v γL γS := by
  unfold arrRoot; iapply (iOwn_alloc (E := ArrG.rootG) _ Agree.toAgree_valid)
theorem arrRoot_agree (γ : GName) (v v' : Val) (γL γS γL' γS' : GName) :
    ⊢@{IProp GF} arrRoot γ v γL γS -∗ arrRoot γ v' γL' γS' -∗
      ⌜v = v' ∧ γL = γL' ∧ γS = γS'⌝ := by
  unfold arrRoot
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  have h := congrArg LeibnizO.car (toAgree_op_valid_iff_eq.mp Hvalid)
  injection h with h1 h; injection h with h2 h3
  exact ⟨h1, h2, h3⟩
instance (γ : GName) (v : Val) (γL γS : GName) : Persistent (PROP := IProp GF) (arrRoot γ v γL γS) := by
  unfold arrRoot; infer_instance
instance (γ : GName) (v : Val) (γL γS : GName) : Timeless (PROP := IProp GF) (arrRoot γ v γL γS) := by
  unfold arrRoot; infer_instance

end RA

variable {GF : BundledGFunctors} [LawfulFiniteMap H' Nat]
variable [HeapLangGS hlc GF] [SpinLockG GF] [ArrG GF H']

def isArrLockINV_pre (Ψ : GName → Nat → Val → IProp GF) (γL : GName) (id : Nat) (node : Val) : IProp GF := iprop%
  ∃ (lk : Val) (γlock : GName) (ptr : Loc), ⌜node = hl_val((&lk, #ptr))⌝ ∗
    SpinLock.isLock γlock lk iprop(
      ∃ (x : Int) (nlk : Val) (al : Bool),
        ((dataPointsto γL id ptr x none al (DFrac.own q2)) ∗
          ptr ↦ hl_val((#x, none()))
          ∨
        (∃ (nid : Nat) (loc : Loc), Ψ γL nid hl_val((&nlk, #loc)) ∗
          ptr ↦ hl_val((#x, some((&nlk, #loc)))) ∗
          dataPointsto γL id ptr x (some nid) al (DFrac.own q2))))

instance isArrLockINV_pre.contractive : OFE.Contractive (isArrLockINV_pre (GF := GF)) := by
  rw [contractive_internalEq (PROP := IProp GF)]
  iintro %Ψ₁ %Ψ₂ #HEQ
  iapply fun_extI; iintro %γL
  iapply fun_extI; iintro %id
  iapply fun_extI; iintro %node
  simp only [isArrLockINV_pre]
  iapply prop_ext
  imodintro
  isplit
  · iintro ⟨%lk, %γlock, %ptr, %Hn, H⟩
    iexists lk, γlock, ptr
    isplit
    · ipureintro; exact Hn
    iapply SpinLock.is_lock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne (exists_ne (fun (x : Int) => exists_ne (fun (nlk : Val) => exists_ne (fun (al : Bool) => BI.or_ne.ne .rfl (exists_ne (fun (nid : Nat) => exists_ne (fun (loc : Loc) => BI.sep_ne.ne (h γL nid hl_val((&nlk, #loc))) .rfl))))))) .rfl⟩
    · iapply equiv_wandIff; exact .rfl
  · iintro ⟨%lk, %γlock, %ptr, %Hn, H⟩
    iexists lk, γlock, ptr
    isplit
    · ipureintro; exact Hn
    iapply SpinLock.is_lock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne .rfl (exists_ne (fun (x : Int) => exists_ne (fun (nlk : Val) => exists_ne (fun (al : Bool) => BI.or_ne.ne .rfl (exists_ne (fun (nid : Nat) => exists_ne (fun (loc : Loc) => BI.sep_ne.ne (h γL nid hl_val((&nlk, #loc))) .rfl)))))))⟩
    · iapply equiv_wandIff; exact .rfl

def isArrLockINV : GName → Nat → Val → IProp GF := fixpoint isArrLockINV_pre

theorem isArrLockINV_unfold (γL : GName) (id : Nat) (v : Val) :
    (isArrLockINV γL id v : IProp GF) ⊣⊢ isArrLockINV_pre isArrLockINV γL id v := by
  have _hHH : (H') = (H') := rfl
  exact equiv_iff.mp (fixpoint_unfold
    (f := Function.toContractiveHom (isArrLockINV_pre (GF := GF) (H' := H'))) γL id v)

/-- The body of a node's spin-lock, `defeq` to the `isArrLockINV_pre` body with `Ψ := isArrLockINV`.
A node holds its own ½ share plus its physical cell, either as a last node (`succ = none`) or linked
to a successor (whose lock we also know). `alive` is existential so the lock stays releasable after
the node is logically deleted (`alive := false`). Reusable in the specs to avoid re-spelling it. -/
abbrev lockBody (γL : GName) (id : Nat) (ptr : Loc) : IProp GF := iprop%
  ∃ (x : Int) (nlk : Val) (al : Bool),
    ((dataPointsto γL id ptr x none al (DFrac.own q2)) ∗ ptr ↦ hl_val((#x, none()))
      ∨
     (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk, #loc)) ∗
       ptr ↦ hl_val((#x, some((&nlk, #loc)))) ∗
       dataPointsto γL id ptr x (some nid) al (DFrac.own q2)))

-- fully-spelled-out unfold (defeq to the pre), for destructuring on proofmode hyps
theorem isArrLockINV_unfold' (γL : GName) (id : Nat) (v : Val) :
    (isArrLockINV γL id v : IProp GF) ⊣⊢
      ∃ (lk : Val) (γlock : GName) (ptr : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        SpinLock.isLock γlock lk (lockBody γL id ptr) :=
  isArrLockINV_unfold γL id v

instance isArrLockINV.persistent (γL : GName) (id : Nat) (v : Val) : Persistent (PROP := IProp GF) (isArrLockINV γL id v) := by
  have Hp : Persistent (PROP := IProp GF) (isArrLockINV_pre isArrLockINV γL id v) := by
    unfold isArrLockINV_pre; infer_instance
  exact ⟨(isArrLockINV_unfold γL id v).mp.trans
    (Hp.persistent.trans (persistently_mono (isArrLockINV_unfold γL id v).mpr))⟩

def contents (γL : GName) (v : Val) (ar : List (Nat × Int)) : IProp GF :=
  match ar with
  | [] => iprop(True)
  | [(id, x)] => iprop%
    ∃ (lk : Val) (ptr : Loc),
      ⌜v = hl_val((&lk, #ptr))⌝ ∗
      dataPointsto γL id ptr x none true (DFrac.own q4)
  | (id, x) :: (sid, sx) :: cs => iprop%
    ∃ (lk : Val) (ptr : Loc) (nlk : Val) (next : Loc),
      ⌜v = hl_val((&lk, #ptr))⌝ ∗
      dataPointsto γL id ptr x (some sid) true (DFrac.own q4) ∗
      contents γL hl_val((&nlk, #next)) ((sid, sx) :: cs)


-- ===== `contents` equation lemmas + insert-after splice =====
section ContentsLemmas
variable {GF : BundledGFunctors} {H' : Type → Type}
  [LawfulFiniteMap H' Nat] [ArrG GF H']

theorem contents_eq_nil (γL : GName) (v : Val) :
    (contents γL v ([] : List (Nat × Int)) : IProp GF) = iprop(True) := rfl

theorem contents_eq_single (γL : GName) (v : Val) (id : Nat) (x : Int) :
    (contents γL v [(id, x)] : IProp GF) = iprop(
      ∃ (lk : Val) (ptr : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        dataPointsto γL id ptr x none true (DFrac.own q4)) := rfl

theorem contents_cons_ne (γL : GName) (v : Val) (id : Nat) (x : Int)
    (c : Nat × Int) (cs : List (Nat × Int)) :
    (contents γL v ((id, x) :: c :: cs) : IProp GF) = iprop(
      ∃ (lk : Val) (ptr : Loc) (nlk : Val) (next : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        dataPointsto γL id ptr x (some c.1) true (DFrac.own q4) ∗
        contents γL hl_val((&nlk, #next)) (c :: cs)) := by
  obtain ⟨cid, cx⟩ := c; rfl

/-- Entailment form of `contents_eq_single`, usable on proofmode hypotheses via `$$`. -/
theorem contents_single_elim (γL : GName) (v : Val) (id : Nat) (x : Int) :
    (contents γL v [(id, x)] : IProp GF) ⊢ iprop(
      ∃ (lk : Val) (ptr : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        dataPointsto γL id ptr x none true (DFrac.own q4)) := by
  rw [contents_eq_single]; iintro h; iexact h

/-- Entailment form of `contents_cons_ne`, usable on proofmode hypotheses via `$$`. -/
theorem contents_cons_elim (γL : GName) (v : Val) (id : Nat) (x : Int)
    (c : Nat × Int) (cs : List (Nat × Int)) :
    (contents γL v ((id, x) :: c :: cs) : IProp GF) ⊢ iprop(
      ∃ (lk : Val) (ptr : Loc) (nlk : Val) (next : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        dataPointsto γL id ptr x (some c.1) true (DFrac.own q4) ∗
        contents γL hl_val((&nlk, #next)) (c :: cs)) := by
  rw [contents_cons_ne]; iintro h; iexact h

/-- Locate the node with logical id `id` inside the from-root `contents` chain, hand back its
contents-share (`dataPointsto … q4`, successor-id = `succ`), and return a reinsertion wand that —
given the node's *updated* share (successor now `some counter`) plus the fresh node's own share
(successor `succ`) — rebuilds `contents` for the spliced list. -/
theorem contents_insertAfter_extract (γL : GName) (id counter : Nat) (xnew : Int) :
    ∀ (cells : List (Nat × Int)) (v : Val),
      id ∈ cells.map (·.1) → (cells.map (·.1)).Nodup →
      contents γL v cells ⊢@{IProp GF}
        ∃ (ptr : Loc) (x0 : Int) (succ : Option Nat),
          dataPointsto γL id ptr x0 succ true (DFrac.own q4) ∗
          (∀ (_nlkv : Val) (nptr : Loc),
              (dataPointsto γL id ptr x0 (some counter) true (DFrac.own q4) ∗
               dataPointsto γL counter nptr xnew succ true (DFrac.own q4))
            -∗ contents γL v (cells.flatMap (Arr.insertBody id counter xnew))) := by
  intro cells
  induction cells with
  | nil => intro v hmem _; simp at hmem
  | cons c cs ih =>
    intro v hmem hnd
    obtain ⟨cid, cx⟩ := c
    cases cs with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
      subst hmem
      rw [contents_eq_single]
      iintro ⟨%lk, %ptr, %Hv, Hd⟩
      iexists ptr, cx, none
      iframe Hd
      iintro %nlkv %nptr ⟨Hd', Hdn⟩
      rw [Arr.flatMap_insert_head id counter xnew cx [] (by simp)]
      rw [contents_cons_ne _ _ _ _ (counter, xnew) []]
      iexists lk, ptr, nlkv, nptr
      isplit
      · ipureintro; exact Hv
      iframe Hd'
      rw [contents_eq_single]
      iexists nlkv, nptr
      isplit
      · ipureintro; rfl
      iframe Hdn
    | cons c' cs' =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hcnotin, hndtl⟩ := hnd
      rw [contents_cons_ne _ _ _ _ c' cs']
      by_cases hci : cid = id
      · subst hci
        iintro ⟨%lk, %ptr, %nlk, %next, %Hv, Hd, Hrest⟩
        iexists ptr, cx, (some c'.1)
        iframe Hd
        iintro %nlkv %nptr ⟨Hd', Hdn⟩
        have htl : ∀ y ∈ (c' :: cs'), y.1 ≠ cid := by
          intro y hy heq; exact hcnotin (List.mem_map.mpr ⟨y, hy, heq⟩)
        rw [Arr.flatMap_insert_head cid counter xnew cx (c' :: cs') htl]
        rw [contents_cons_ne _ _ _ _ (counter, xnew) (c' :: cs')]
        iexists lk, ptr, nlkv, nptr
        isplit
        · ipureintro; exact Hv
        iframe Hd'
        rw [contents_cons_ne _ _ _ _ c' cs']
        iexists nlkv, nptr, nlk, next
        isplit
        · ipureintro; rfl
        iframe Hdn Hrest
      · iintro ⟨%lk, %ptr, %nlk, %next, %Hv, Hd, Hrest⟩
        have hmem' : id ∈ (c' :: cs').map (·.1) := by
          rw [List.map_cons, List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd h.symm hci
          · exact h
        icases (ih hl_val((&nlk, #next)) hmem' hndtl) $$ Hrest
          with ⟨%ptr2, %x2, %succ2, Hd2, Hwand⟩
        iexists ptr2, x2, succ2
        iframe Hd2
        iintro %nlkv %nptr Hpieces
        obtain ⟨ds, hds⟩ := Arr.flatMap_cons_head id counter xnew c' cs'
        rw [Arr.flatMap_skip_head id counter xnew (cid, cx) (c' :: cs') hci, hds]
        rw [contents_cons_ne _ _ _ _ c' ds]
        iexists lk, ptr, nlk, next
        isplit
        · ipureintro; exact Hv
        iframe Hd
        rw [← hds]
        iapply Hwand $$ %nlkv %nptr Hpieces

/-- Locate node `id` and its immediate successor `sid` (from `adjacent`) inside the from-root
`contents` chain; hand back `id`'s contents-share (successor-id `sid`) and `sid`'s contents-share
(successor-id `ssucc`), plus a relink wand that — given `id`'s updated share (successor now
`ssucc`) — rebuilds `contents` for the list with `sid` removed. -/
theorem contents_removeAfter_extract (γL : GName) (id sid : Nat) :
    ∀ (pre post : List (Nat × Int)) (x sx : Int) (v : Val),
      ((pre ++ (id, x) :: (sid, sx) :: post).map (·.1)).Nodup →
      contents γL v (pre ++ (id, x) :: (sid, sx) :: post) ⊢@{IProp GF}
        ∃ (ptr sptr : Loc) (x0 : Int) (ssucc : Option Nat),
          dataPointsto γL id ptr x0 (some sid) true (DFrac.own q4) ∗
          dataPointsto γL sid sptr sx ssucc true (DFrac.own q4) ∗
          (dataPointsto γL id ptr x0 ssucc true (DFrac.own q4) -∗
            contents γL v (pre ++ (id, x) :: post)) := by
  intro pre
  induction pre with
  | nil =>
    intro post x sx v hnd
    simp only [List.nil_append]
    cases post with
    | nil =>
      rw [contents_cons_ne _ _ _ _ (sid, sx) []]
      iintro ⟨%lk, %ptr, %nlk, %next, %Hv, Hd, Hrest⟩
      icases (contents_single_elim γL hl_val((&nlk, #next)) sid sx) $$ Hrest
        with ⟨%slk, %sptr, %Hsv, Hsd⟩
      iexists ptr, sptr, x, none
      iframe Hd Hsd
      iintro Hd'
      rw [contents_eq_single]
      iexists lk, ptr
      isplit
      · ipureintro; exact Hv
      iframe Hd'
    | cons t post' =>
      rw [contents_cons_ne _ _ _ _ (sid, sx) (t :: post')]
      iintro ⟨%lk, %ptr, %nlk, %next, %Hv, Hd, Hrest⟩
      icases (contents_cons_elim γL hl_val((&nlk, #next)) sid sx t post') $$ Hrest
        with ⟨%slk, %sptr, %snlk, %snext, %Hsv, Hsd, Hsrest⟩
      iexists ptr, sptr, x, (some t.1)
      iframe Hd Hsd
      iintro Hd'
      rw [contents_cons_ne _ _ _ _ t post']
      iexists lk, ptr, snlk, snext
      isplit
      · ipureintro; exact Hv
      iframe Hd' Hsrest
  | cons c pre' ih =>
    intro post x sx v hnd
    obtain ⟨cid, cx⟩ := c
    have hndtl : ((pre' ++ (id, x) :: (sid, sx) :: post).map (·.1)).Nodup := by
      rw [List.cons_append, List.map_cons, List.nodup_cons] at hnd
      exact hnd.2
    obtain ⟨d, ds1, ds2, hR1, hR2⟩ :=
      Arr.append_cons_head pre' (id, x) ((sid, sx) :: post) post
    rw [List.cons_append, hR1, contents_cons_ne _ _ _ _ d ds1]
    iintro ⟨%lk, %ptr, %nlk, %next, %Hv, Hd, Hrest⟩
    ihave Hrest2 : contents γL hl_val((&nlk, #next)) (pre' ++ (id, x) :: (sid, sx) :: post) $$ [Hrest]
    · rw [hR1]; iexact Hrest
    icases (ih post x sx hl_val((&nlk, #next)) hndtl) $$ Hrest2
      with ⟨%ptr2, %sptr, %x0, %ssucc, Hd2, Hsd, Hwand⟩
    iexists ptr2, sptr, x0, ssucc
    iframe Hd2 Hsd
    iintro Hd'
    rw [List.cons_append, hR2, contents_cons_ne _ _ _ _ d ds2]
    iexists lk, ptr, nlk, next
    isplit
    · ipureintro; exact Hv
    iframe Hd
    rw [← hR2]
    iapply Hwand $$ Hd'

end ContentsLemmas

def isArrINV (γL γA γS : GName) : IProp GF := iprop%
  ∃ (σ : Arr) (v : Val) (m : H' (Loc × Int × Option Nat × Bool)),
    dataMap γL m ∗ arrRoot γA v γL γS ∗ arrState γS σ ∗
  ⌜ (∀ id, id ∈ σ.cells.map (·.1) ↔ ∃ loc x sl, get? m id = some (loc, x, sl, true))
    ∧ (∀ id, dom m id → id < σ.counter)
    ∧ Arr.wellFormed σ ⌝

instance isArrINV_timeless (γL γA γS : GName) :
    Timeless (PROP := IProp GF) (isArrINV γL γA γS) := by
  unfold isArrINV; infer_instance

omit [SpinLockG GF] in
theorem isArrINV_unfold (γL γA γS : GName) :
    (isArrINV γL γA γS : IProp GF) ⊣⊢
      ∃ (σ : Arr) (v : Val) (m : H' (Loc × Int × Option Nat × Bool)),
        dataMap γL m ∗ arrRoot γA v γL γS ∗ arrState γS σ ∗
      ⌜ (∀ id, id ∈ σ.cells.map (·.1) ↔ ∃ loc x sl, get? m id = some (loc, x, sl, true))
        ∧ (∀ id, dom m id → id < σ.counter)
        ∧ Arr.wellFormed σ ⌝ := .rfl


-- CORE PREDICATES
def arrN : Namespace := ndot nroot "arr"
def Arr.isArr (γ : GName) : IProp GF := iprop%
  ∃ (v : Val) (γL γS : GName),
    arrRoot γ v γL γS ∗
    isArrLockINV γL 0 v ∗
    inv arrN (isArrINV γL γ γS)
-- AI: Prove the persistent
instance Arr.isArr_persistent (γ : GName) : Persistent (PROP := IProp GF) (Arr.isArr γ) := by
  unfold Arr.isArr; infer_instance


def Arr.isContents (γ : GName) (σ : Arr) : IProp GF := iprop%
  ∃ (v : Val) (γL γS : GName),
    arrRoot γ v γL γS ∗ arrStateFrag γS σ ∗
    contents γL v σ.cells

omit [SpinLockG GF] in
theorem Arr.isContents_unfold (γ : GName) (σ : Arr) :
    (Arr.isContents γ σ : IProp GF) ⊣⊢
      ∃ (v : Val) (γL γS : GName),
        arrRoot γ v γL γS ∗ arrStateFrag γS σ ∗
        contents γL v σ.cells := .rfl


def Arr.idRecord (γ : GName) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ (v: Val) (γL γS : GName) (lk : Val) (ptr : Loc),
    arrRoot γ v γL γS ∗ ⌜node = hl_val((&lk, #ptr))⌝ ∗
    (∃ (val : Int) (succ : Option Nat), dataPointsto γL id ptr val succ true (DFrac.own q4)) ∗
    isArrLockINV γL id node

-- trivial (defeq) unfolding lemmas, to destruct the def-wrapped predicates on proofmode hyps
theorem Arr.isArr_unfold (γ : GName) :
    (Arr.isArr γ : IProp GF) ⊣⊢
      ∃ v γL γS, arrRoot γ v γL γS ∗ isArrLockINV γL 0 v ∗
        inv arrN (isArrINV γL γ γS) := .rfl
theorem Arr.idRecord_unfold (γ : GName) (node : Val) (id : Nat) :
    (Arr.idRecord γ node id : IProp GF) ⊣⊢
      ∃ (v: Val) (γL γS : GName) (lk : Val) (ptr : Loc),
        arrRoot γ v γL γS ∗ ⌜node = hl_val((&lk, #ptr))⌝ ∗
        (∃ (val : Int) (succ : Option Nat), dataPointsto γL id ptr val succ true (DFrac.own q4)) ∗
        isArrLockINV γL id node := .rfl



theorem Impl.init_spec (x : Int) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.init #x)
    ⦃ v, RET v; ∃ γ, Arr.isArr γ ∗ Arr.isContents γ (Arr.init x) ∗ Arr.idRecord γ v 0 ⦄ := by
  iintro %Φ - Hcont
  unfold Impl.init
  wp_pures
  wp_bind &newlock _
  iapply newlock_spec
  iintro %lk %γlock Hlk
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %c Hc
  iapply fupd_wp
  imod dataMap_alloc with ⟨%γL, HDm⟩
  imod (dataMap_insert γL ∅ 0 c x none true (get?_empty _)) $$ HDm with ⟨HDm, HDf⟩
  imod (arrState_alloc (Arr.init x)) with ⟨%γS, HSauth, HSfrag⟩
  imod (arrRoot_alloc hl_val((&lk, #c)) γL γS) with ⟨%γ, #Hroot⟩
  icases (data_split3 γL 0 c x none true) $$ HDf with ⟨HDlock, HDcont, HDrec⟩
  -- build the node's lock body (LEFT branch: last node, next = none)
  ihave Hbody : lockBody γL 0 c $$ [HDlock Hc]
  · iexists x, lk, true
    ileft; iframe HDlock Hc
  ispecialize Hlk $$ %_ %(⊤) Hbody
  imod Hlk with Hlock
  imod (inv_alloc arrN ⊤ (isArrINV γL γ γS)) $$ [HDm Hroot HSauth] with #Hinv
  · inext
    unfold isArrINV
    iexists (Arr.init x), hl_val((&lk, #c)), _
    iframe HDm Hroot HSauth
    ipureintro
    refine ⟨?_, ?_, Arr.init_wellFormed x⟩
    · intro id
      simp only [Arr.init, List.map_cons, List.map_nil, List.mem_singleton,
        LawfulPartialMap.get?_insert, get?_empty]
      by_cases h0 : id = 0
      · subst h0; simp
      · simp [h0, Ne.symm h0]
    · intro id
      simp only [PartialMap.dom, LawfulPartialMap.get?_insert, get?_empty, Arr.init]
      by_cases h0 : id = 0
      · subst h0; intro _; omega
      · simp [h0, Ne.symm h0]
  ihave #HlockINV : isArrLockINV γL 0 hl_val((&lk, #c)) $$ [Hlock]
  · iapply (isArrLockINV_unfold γL 0 hl_val((&lk, #c))).mpr
    unfold isArrLockINV_pre
    iexists lk, γlock, c
    isplit
    · ipureintro; rfl
    · iexact Hlock
  imodintro
  wp_pures
  imodintro
  iapply Hcont
  iexists γ
  isplitl []
  · unfold Arr.isArr
    iexists hl_val((&lk, #c)), γL, γS
    iframe Hroot HlockINV Hinv
  isplitl [HSfrag HDcont]
  · unfold Arr.isContents
    iexists hl_val((&lk, #c)), γL, γS
    iframe Hroot HSfrag
    rw [Arr.init]
    unfold contents
    iexists lk, c
    isplit
    · ipureintro; rfl
    iframe HDcont
  · unfold Arr.idRecord
    iexists hl_val((&lk, #c)), γL, γS, lk, c
    iframe Hroot
    isplit
    · ipureintro; rfl
    isplitl [HDrec]
    · iexists x, none; iframe HDrec
    · iexact HlockINV

set_option trace.profiler.output "/tmp/profile.json"
set_option trace.profiler.output.pp true

set_option trace.profiler true in
set_option maxRecDepth 8000 in
theorem Impl.insert_spec (γ : GName) (id : Nat) (node : Val) (x : Int) :
  ⊢@{IProp GF}
    Arr.isArr γ -∗
      ⟪ ∀ σ, Arr.isContents γ σ ∗ Arr.idRecord γ node id ⟫
        hl(&Impl.insert &node #x) @ arrN
      ⟪ ∃ nid, Arr.isContents γ (σ.insert id x) ∗ Arr.idRecord γ node id ∗ ⌜nid = σ.counter⌝
        | ret, RET ret; Arr.idRecord γ ret nid ⟫ := by
  iintro Harr %Φ HAU
  icases (Arr.isArr_unfold γ).mp $$ Harr with ⟨%v, %γL, %γS, #Hroot, #HlockRoot, #Hinv⟩
  -- PEEK: `idRecord` now lives *inside* the atomic precondition, but we must acquire
  -- `node`'s lock *before* the linearization point.  So open the AU once and abort it,
  -- keeping only the *persistent* `isArrLockINV` (the lock's `SpinLock.isLock`).
  iapply fupd_wp
  imod (fupd_mask_subseteq (E1 := ⊤) (E2 := ⊤ \ (↑arrN : CoPset)) (by intro x _; exact CoPset.mem_full)) with Hmclose
  iauopen HAU with ⟨%σp, Hαp, Hclosep⟩
  icases Hαp with ⟨Hcontp, Hnodep⟩
  icases (Arr.idRecord_unfold γ node id).mp $$ Hnodep with ⟨%vp, %γLp, %γSp, %lkNp, %ptrNp, #Hrootp, %HnodeEqNp, HidRecp, #HlockNode⟩
  icases (arrRoot_agree γ v vp γL γS γLp γSp) $$ Hroot Hrootp with %Hallp
  obtain ⟨_, HγLp, HγSp⟩ := Hallp
  subst HγLp; subst HγSp
  ihave Hnodep' : Arr.idRecord γ node id $$ [HidRecp]
  · unfold Arr.idRecord
    iexists vp, γL, γS, lkNp, ptrNp
    iframe Hrootp
    isplit
    · ipureintro; exact HnodeEqNp
    isplitl [HidRecp]
    · iexact HidRecp
    · iexact HlockNode
  icases Hclosep with ⟨Habort, -⟩
  imod Habort $$ [Hcontp Hnodep'] with HAU
  · iframe Hcontp Hnodep'
  imod Hmclose
  imodintro
  icases (isArrLockINV_unfold' γL id node).mp $$ HlockNode with ⟨%lk, %γlock, %ptr, %Hnodeeq, #Hlock⟩
  rw [Hnodeeq]
  unfold Impl.insert
  wp_pures
  wp_bind &acquire _
  iapply acquire_spec $$ Hlock
  iintro ⟨Hlocked, HR⟩
  icases HR with ⟨%x0, %nlk, %al0, Hdisj⟩
  wp_pures
  wp_bind !_
  icases Hdisj with (⟨HDlock, Hpt⟩ | ⟨%nid0, %loc0, #HlockSucc, Hpt, HDlock⟩)
  · -- LEFT: node is last (successor `none`)
    iapply wp_load $$ Hpt
    iintro !> Hpt
    wp_pures
    wp_bind &newlock _
    iapply newlock_spec
    iintro %nlkv %γnlock Hnlk
    wp_pures
    wp_bind ref(_)
    iapply wp_alloc
    iintro !> %nptr Hnptr
    wp_pures
    wp_bind (_ ← _)
    iapply wp_store $$ Hpt
    iintro !> Hpt
    wp_pures
    -- LINEARIZATION POINT
    iapply fupd_wp
    iinv Hinv with ⟨HI, Hclinv⟩
    icases (isArrINV_unfold γL γ γS).mp $$ HI with ⟨%σ0, %vI, %m, HDm, #HrootI, HSauth, %Hcoup⟩
    iauopen HAU with ⟨%σ, Hα, Hclose⟩
    icases Hα with ⟨Hcont, Hnode⟩
    icases (Arr.isContents_unfold γ σ).mp $$ Hcont with ⟨%vc, %γLc, %γSc, #Hrootc, HSfrag, Hcontents⟩
    icases (arrRoot_agree γ vI vc γL γS γLc γSc) $$ HrootI Hrootc with %Hall2
    obtain ⟨HvIc, HγLc, HγSc⟩ := Hall2
    subst γLc; subst γSc; subst vI
    icases (arrState_agree γS σ0 σ) $$ HSauth HSfrag with %Hσeq
    subst σ0
    have Hwf := Hcoup.2.2
    icases (Arr.idRecord_unfold γ hl_val((&lk, #ptr)) id).mp $$ Hnode with ⟨%vN, %γLN, %γSN, %lkN, %ptrN, #HrootN, %HnodeEqN, HidRec, #HlockNodeL⟩
    icases (arrRoot_agree γ v vN γL γS γLN γSN) $$ Hroot HrootN with %HallN
    obtain ⟨_, HγLN, HγSN⟩ := HallN
    subst HγLN; subst HγSN
    icases HidRec with ⟨%rval, %rsucc, HDrec⟩
    icases (dataPointsto_agree γL id ptr ptrN x0 rval none rsucc al0 true _ _) $$ HDlock HDrec with %HagN
    obtain ⟨hpN, hrv, hrs, hal⟩ := HagN
    subst hpN; subst hrv; subst hrs; subst hal
    icases (dataMap_lookup γL m id ptr x0 none true _) $$ HDm HDrec with %HgetRec
    have Hmem : id ∈ σ.cells.map (·.1) := (Hcoup.1 id).mpr ⟨ptr, x0, none, HgetRec⟩
    have Hnodup : (σ.cells.map (·.1)).Nodup := Hwf.idUqi
    icases (contents_insertAfter_extract γL id σ.counter x σ.cells vc Hmem Hnodup) $$ Hcontents
      with ⟨%ptr2, %x2, %succ2, HDcont, Hwand⟩
    icases (dataPointsto_agree γL id ptr ptr2 x0 x2 none succ2 true true _ _) $$ HDlock HDcont with %Hag
    obtain ⟨hp2, hx2, hs2, -⟩ := Hag
    subst hp2; subst hx2; subst hs2
    ihave HDfull : dataPointsto γL id ptr x0 none true (DFrac.own 1) $$ [HDlock HDcont HDrec]
    · iapply data_combine3; iframe HDlock HDcont HDrec
    imod (dataMap_update γL m id ptr x0 none (some σ.counter) true true) $$ HDm HDfull with ⟨HDm, HDfull⟩
    icases (data_split3 γL id ptr x0 (some σ.counter) true) $$ HDfull with ⟨HDlock', HDcont', HDrec'⟩
    have hid_lt : id < σ.counter := by
      obtain ⟨p, hp, hpid⟩ := List.mem_map.mp Hmem
      rw [← hpid]; exact Hwf.counterFresh p hp
    have Hfresh : get? (PartialMap.insert m id (ptr, x0, some σ.counter, true)) σ.counter = none := by
      rw [LawfulPartialMap.get?_insert, if_neg (by omega : ¬ id = σ.counter)]
      cases h : get? m σ.counter with
      | none => rfl
      | some val =>
        exfalso
        have hdom : PartialMap.dom m σ.counter := by simp [PartialMap.dom, h]
        exact absurd (Hcoup.2.1 σ.counter hdom) (by omega)
    imod (dataMap_insert γL (PartialMap.insert m id (ptr, x0, some σ.counter, true)) σ.counter nptr x none true Hfresh) $$ HDm with ⟨HDm, HDnew⟩
    icases (data_split3 γL σ.counter nptr x none true) $$ HDnew with ⟨HDnlock, HDncont, HDnrec⟩
    imod (arrState_update γS σ (σ.insert id x)) $$ HSauth HSfrag with ⟨HSauth, HSfrag⟩
    ihave Hcontents' : contents γL vc (σ.cells.flatMap (Arr.insertBody id σ.counter x)) $$ [HDcont' HDncont Hwand]
    · iapply Hwand $$ %nlkv %nptr
      iframe HDcont' HDncont
    icases Hclose with ⟨-, Hcommit⟩
    imod Hcommit $$ %(σ.counter) [Hrootc HSfrag Hcontents' HDrec'] with HΦ
    · isplitl [Hrootc HSfrag Hcontents']
      · unfold Arr.isContents
        iexists vc, γL, γS
        iframe Hrootc HSfrag
        rw [Arr.insert_cells_eq σ id x Hmem]
        iexact Hcontents'
      · isplitl [HDrec']
        · unfold Arr.idRecord
          iexists vN, γL, γS, lkN, ptr
          iframe HrootN
          isplit
          · ipureintro; exact HnodeEqN
          isplitl [HDrec']
          · iexists x0, (some σ.counter); iframe HDrec'
          · iexact HlockNodeL
        · ipureintro; rfl
    -- close the shared invariant with the updated map & state
    ihave HInew : isArrINV γL γ γS $$ [HDm HrootI HSauth]
    · unfold isArrINV
      iexists (σ.insert id x), vc, (PartialMap.insert (PartialMap.insert m id (ptr, x0, some σ.counter, true)) σ.counter (nptr, x, none, true))
      iframe HDm HrootI HSauth
      ipureintro
      refine ⟨?_, ?_, σ.insert_wellFormed Hwf id x⟩
      · intro id'
        rw [Arr.insert_ids_mem σ id x Hmem id']
        by_cases hc : id' = σ.counter
        · subst hc
          constructor
          · intro _; exact ⟨nptr, x, none, by rw [LawfulPartialMap.get?_insert, if_pos rfl]⟩
          · intro _; exact Or.inl rfl
        · rw [LawfulPartialMap.get?_insert, if_neg (fun h => hc h.symm)]
          by_cases hi : id' = id
          · subst hi
            constructor
            · intro _; exact ⟨ptr, x0, some σ.counter, by rw [LawfulPartialMap.get?_insert, if_pos rfl]⟩
            · intro _; exact Or.inr Hmem
          · rw [LawfulPartialMap.get?_insert, if_neg (fun h => hi h.symm), ← Hcoup.1 id']
            constructor
            · rintro (h | h)
              · exact absurd h hc
              · exact h
            · intro h; exact Or.inr h
      · intro id'
        rw [Arr.insert_counter σ id x Hmem]
        intro hdom'
        by_cases hc : id' = σ.counter
        · omega
        · by_cases hi : id' = id
          · omega
          · have heq : get? (PartialMap.insert (PartialMap.insert m id (ptr, x0, some σ.counter, true)) σ.counter (nptr, x, none, true)) id' = get? m id' := by
              rw [LawfulPartialMap.get?_insert, if_neg (fun h => hc h.symm),
                  LawfulPartialMap.get?_insert, if_neg (fun h => hi h.symm)]
            have hd : PartialMap.dom m id' := by
              unfold PartialMap.dom at hdom' ⊢; rw [← heq]; exact hdom'
            have := Hcoup.2.1 id' hd; omega
    imod Hclinv $$ HInew
    -- build the new node's lock (isArrLockINV γL σ.counter (&nlkv,#nptr))
    ihave Hnbody : lockBody γL σ.counter nptr $$ [HDnlock Hnptr]
    · iexists x, lk, true
      ileft; iframe HDnlock Hnptr
    ispecialize Hnlk $$ %_ %(⊤) Hnbody
    imod Hnlk with Hnlock
    ihave #HnlockINV : isArrLockINV γL σ.counter hl_val((&nlkv, #nptr)) $$ [Hnlock]
    · iapply (isArrLockINV_unfold γL σ.counter hl_val((&nlkv, #nptr))).mpr
      unfold isArrLockINV_pre
      iexists nlkv, γnlock, nptr
      isplit
      · ipureintro; rfl
      · iexact Hnlock
    imodintro
    -- rebuild old node's lock body (RIGHT form: succ = some nptr) and release
    ihave HRnew : lockBody γL id ptr $$ [Hpt HDlock' HnlockINV]
    · iexists x0, nlkv, true
      iright; iexists σ.counter, nptr
      iframe HnlockINV Hpt HDlock'
    ihave Hres : iprop(SpinLock.isLock γlock lk (lockBody γL id ptr) ∗ (SpinLock.locked γlock ∗ lockBody γL id ptr)) $$ [Hlock Hlocked HRnew]
    · iframe Hlock Hlocked HRnew
    wp_bind &release _
    iapply release_spec $$ Hres
    iintro -
    wp_pures
    imodintro
    ispecialize HΦ $$ %hl_val((&nlkv, #nptr))
    iunfold wandM at HΦ
    iapply HΦ
    unfold Arr.idRecord
    iexists v, γL, γS, nlkv, nptr
    iframe Hroot
    isplit
    · ipureintro; rfl
    isplitl [HDnrec]
    · iexists x, none; iframe HDnrec
    · iexact HnlockINV
  · -- RIGHT: node already has a successor at `loc0` (value `(&nlk, #loc0)`)
    iapply wp_load $$ Hpt
    iintro !> Hpt
    wp_pures
    wp_bind &newlock _
    iapply newlock_spec
    iintro %nlkv %γnlock Hnlk
    wp_pures
    wp_bind ref(_)
    iapply wp_alloc
    iintro !> %nptr Hnptr
    wp_pures
    wp_bind (_ ← _)
    iapply wp_store $$ Hpt
    iintro !> Hpt
    wp_pures
    -- LINEARIZATION POINT
    iapply fupd_wp
    iinv Hinv with ⟨HI, Hclinv⟩
    icases (isArrINV_unfold γL γ γS).mp $$ HI with ⟨%σ0, %vI, %m, HDm, #HrootI, HSauth, %Hcoup⟩
    iauopen HAU with ⟨%σ, Hα, Hclose⟩
    icases Hα with ⟨Hcont, Hnode⟩
    icases (Arr.isContents_unfold γ σ).mp $$ Hcont with ⟨%vc, %γLc, %γSc, #Hrootc, HSfrag, Hcontents⟩
    icases (arrRoot_agree γ vI vc γL γS γLc γSc) $$ HrootI Hrootc with %Hall2
    obtain ⟨HvIc, HγLc, HγSc⟩ := Hall2
    subst γLc; subst γSc; subst vI
    icases (arrState_agree γS σ0 σ) $$ HSauth HSfrag with %Hσeq
    subst σ0
    have Hwf := Hcoup.2.2
    icases (Arr.idRecord_unfold γ hl_val((&lk, #ptr)) id).mp $$ Hnode with ⟨%vN, %γLN, %γSN, %lkN, %ptrN, #HrootN, %HnodeEqN, HidRec, #HlockNodeL⟩
    icases (arrRoot_agree γ v vN γL γS γLN γSN) $$ Hroot HrootN with %HallN
    obtain ⟨_, HγLN, HγSN⟩ := HallN
    subst HγLN; subst HγSN
    icases HidRec with ⟨%rval, %rsucc, HDrec⟩
    icases (dataPointsto_agree γL id ptr ptrN x0 rval (some nid0) rsucc al0 true _ _) $$ HDlock HDrec with %HagN
    obtain ⟨hpN, hrv, hrs, hal⟩ := HagN
    subst hpN; subst hrv; subst hrs; subst hal
    icases (dataMap_lookup γL m id ptr x0 (some nid0) true _) $$ HDm HDrec with %HgetRec
    have Hmem : id ∈ σ.cells.map (·.1) := (Hcoup.1 id).mpr ⟨ptr, x0, some nid0, HgetRec⟩
    have Hnodup : (σ.cells.map (·.1)).Nodup := Hwf.idUqi
    icases (contents_insertAfter_extract γL id σ.counter x σ.cells vc Hmem Hnodup) $$ Hcontents
      with ⟨%ptr2, %x2, %succ2, HDcont, Hwand⟩
    icases (dataPointsto_agree γL id ptr ptr2 x0 x2 (some nid0) succ2 true true _ _) $$ HDlock HDcont with %Hag
    obtain ⟨hp2, hx2, hs2, -⟩ := Hag
    subst hp2; subst hx2; subst hs2
    ihave HDfull : dataPointsto γL id ptr x0 (some nid0) true (DFrac.own 1) $$ [HDlock HDcont HDrec]
    · iapply data_combine3; iframe HDlock HDcont HDrec
    imod (dataMap_update γL m id ptr x0 (some nid0) (some σ.counter) true true) $$ HDm HDfull with ⟨HDm, HDfull⟩
    icases (data_split3 γL id ptr x0 (some σ.counter) true) $$ HDfull with ⟨HDlock', HDcont', HDrec'⟩
    have hid_lt : id < σ.counter := by
      obtain ⟨p, hp, hpid⟩ := List.mem_map.mp Hmem
      rw [← hpid]; exact Hwf.counterFresh p hp
    have Hfresh : get? (PartialMap.insert m id (ptr, x0, some σ.counter, true)) σ.counter = none := by
      rw [LawfulPartialMap.get?_insert, if_neg (by omega : ¬ id = σ.counter)]
      cases h : get? m σ.counter with
      | none => rfl
      | some val =>
        exfalso
        have hdom : PartialMap.dom m σ.counter := by simp [PartialMap.dom, h]
        exact absurd (Hcoup.2.1 σ.counter hdom) (by omega)
    imod (dataMap_insert γL (PartialMap.insert m id (ptr, x0, some σ.counter, true)) σ.counter nptr x (some nid0) true Hfresh) $$ HDm with ⟨HDm, HDnew⟩
    icases (data_split3 γL σ.counter nptr x (some nid0) true) $$ HDnew with ⟨HDnlock, HDncont, HDnrec⟩
    imod (arrState_update γS σ (σ.insert id x)) $$ HSauth HSfrag with ⟨HSauth, HSfrag⟩
    ihave Hcontents' : contents γL vc (σ.cells.flatMap (Arr.insertBody id σ.counter x)) $$ [HDcont' HDncont Hwand]
    · iapply Hwand $$ %nlkv %nptr
      iframe HDcont' HDncont
    icases Hclose with ⟨-, Hcommit⟩
    imod Hcommit $$ %(σ.counter) [Hrootc HSfrag Hcontents' HDrec'] with HΦ
    · isplitl [Hrootc HSfrag Hcontents']
      · unfold Arr.isContents
        iexists vc, γL, γS
        iframe Hrootc HSfrag
        rw [Arr.insert_cells_eq σ id x Hmem]
        iexact Hcontents'
      · isplitl [HDrec']
        · unfold Arr.idRecord
          iexists vN, γL, γS, lkN, ptr
          iframe HrootN
          isplit
          · ipureintro; exact HnodeEqN
          isplitl [HDrec']
          · iexists x0, (some σ.counter); iframe HDrec'
          · iexact HlockNodeL
        · ipureintro; rfl
    ihave HInew : isArrINV γL γ γS $$ [HDm HrootI HSauth]
    · unfold isArrINV
      iexists (σ.insert id x), vc, (PartialMap.insert (PartialMap.insert m id (ptr, x0, some σ.counter, true)) σ.counter (nptr, x, some nid0, true))
      iframe HDm HrootI HSauth
      ipureintro
      refine ⟨?_, ?_, σ.insert_wellFormed Hwf id x⟩
      · intro id'
        rw [Arr.insert_ids_mem σ id x Hmem id']
        by_cases hc : id' = σ.counter
        · subst hc
          constructor
          · intro _; exact ⟨nptr, x, some nid0, by rw [LawfulPartialMap.get?_insert, if_pos rfl]⟩
          · intro _; exact Or.inl rfl
        · rw [LawfulPartialMap.get?_insert, if_neg (fun h => hc h.symm)]
          by_cases hi : id' = id
          · subst hi
            constructor
            · intro _; exact ⟨ptr, x0, some σ.counter, by rw [LawfulPartialMap.get?_insert, if_pos rfl]⟩
            · intro _; exact Or.inr Hmem
          · rw [LawfulPartialMap.get?_insert, if_neg (fun h => hi h.symm), ← Hcoup.1 id']
            constructor
            · rintro (h | h)
              · exact absurd h hc
              · exact h
            · intro h; exact Or.inr h
      · intro id'
        rw [Arr.insert_counter σ id x Hmem]
        intro hdom'
        by_cases hc : id' = σ.counter
        · omega
        · by_cases hi : id' = id
          · omega
          · have heq : get? (PartialMap.insert (PartialMap.insert m id (ptr, x0, some σ.counter, true)) σ.counter (nptr, x, some nid0, true)) id' = get? m id' := by
              rw [LawfulPartialMap.get?_insert, if_neg (fun h => hc h.symm),
                  LawfulPartialMap.get?_insert, if_neg (fun h => hi h.symm)]
            have hd : PartialMap.dom m id' := by
              unfold PartialMap.dom at hdom' ⊢; rw [← heq]; exact hdom'
            have := Hcoup.2.1 id' hd; omega
    imod Hclinv $$ HInew
    ihave Hnbody : lockBody γL σ.counter nptr $$ [HDnlock Hnptr HlockSucc]
    · iexists x, nlk, true
      iright; iexists nid0, loc0
      iframe HlockSucc Hnptr HDnlock
    ispecialize Hnlk $$ %_ %(⊤) Hnbody
    imod Hnlk with Hnlock
    ihave #HnlockINV : isArrLockINV γL σ.counter hl_val((&nlkv, #nptr)) $$ [Hnlock]
    · iapply (isArrLockINV_unfold γL σ.counter hl_val((&nlkv, #nptr))).mpr
      unfold isArrLockINV_pre
      iexists nlkv, γnlock, nptr
      isplit
      · ipureintro; rfl
      · iexact Hnlock
    imodintro
    ihave HRnew : lockBody γL id ptr $$ [Hpt HDlock' HnlockINV]
    · iexists x0, nlkv, true
      iright; iexists σ.counter, nptr
      iframe HnlockINV Hpt HDlock'
    ihave Hres : iprop(SpinLock.isLock γlock lk (lockBody γL id ptr) ∗ (SpinLock.locked γlock ∗ lockBody γL id ptr)) $$ [Hlock Hlocked HRnew]
    · iframe Hlock Hlocked HRnew
    wp_bind &release _
    iapply release_spec $$ Hres
    iintro -
    wp_pures
    imodintro
    ispecialize HΦ $$ %hl_val((&nlkv, #nptr))
    iunfold wandM at HΦ
    iapply HΦ
    unfold Arr.idRecord
    iexists v, γL, γS, nlkv, nptr
    iframe Hroot
    isplit
    · ipureintro; rfl
    isplitl [HDnrec]
    · iexists x, (some nid0); iframe HDnrec
    · iexact HnlockINV

set_option maxRecDepth 8000 in
/-- Remove-after: `Impl.remove node` physically unlinks `node`'s successor. `node`'s record
(`id`) is returned; `snode`'s record (`sid`) is consumed — logically deleting `sid`. Note `snode`
is a purely logical parameter: only its record token matters (its physical `Val` is forced equal
to `node`'s successor by the ghost agreements), so the caller effectively just supplies `sid`. -/
theorem Impl.remove_spec (γ : GName) (id sid : Nat) (node snode : Val) :
  ⊢@{IProp GF}
    Arr.isArr γ -∗
      ⟪ ∀ σ, Arr.isContents γ σ ∗ Arr.idRecord γ node id ∗ Arr.idRecord γ snode sid ∗ ⌜Arr.adjacent σ id sid⌝  ⟫
        hl(&Impl.remove &node) @ arrN
      ⟪ Arr.isContents γ (σ.remove sid) ∗ Arr.idRecord γ node id | RET hl_val(#()) ⟫ := by
  iintro Harr %Φ HAU
  icases (Arr.isArr_unfold γ).mp $$ Harr with ⟨%v, %γL, %γS, #Hroot, #HlockRoot, #Hinv⟩
  -- PEEK (see insert_spec): grab node's persistent lock before the LP.
  iapply fupd_wp
  imod (fupd_mask_subseteq (E1 := ⊤) (E2 := ⊤ \ (↑arrN : CoPset)) (by intro x _; exact CoPset.mem_full)) with Hmclose
  iauopen HAU with ⟨%σp, Hαp, Hclosep⟩
  icases Hαp with ⟨Hcontp, Hnodep, Hsnodep, %Hadjp⟩
  icases (Arr.idRecord_unfold γ node id).mp $$ Hnodep with ⟨%vp, %γLp, %γSp, %lkNp, %ptrNp, #Hrootp, %HnodeEqNp, HidRecp, #HlockNode⟩
  icases (arrRoot_agree γ v vp γL γS γLp γSp) $$ Hroot Hrootp with %Hallp
  obtain ⟨_, HγLp, HγSp⟩ := Hallp
  subst HγLp; subst HγSp
  ihave Hnodep' : Arr.idRecord γ node id $$ [HidRecp]
  · unfold Arr.idRecord
    iexists vp, γL, γS, lkNp, ptrNp
    iframe Hrootp
    isplit
    · ipureintro; exact HnodeEqNp
    isplitl [HidRecp]
    · iexact HidRecp
    · iexact HlockNode
  icases Hclosep with ⟨Habort, -⟩
  imod Habort $$ [Hcontp Hnodep' Hsnodep] with HAU
  · iframe Hcontp Hnodep' Hsnodep
    ipureintro; exact Hadjp
  imod Hmclose
  imodintro
  icases (isArrLockINV_unfold' γL id node).mp $$ HlockNode with ⟨%lk, %γlock, %ptr, %Hnodeeq, #Hlock⟩
  rw [Hnodeeq]
  unfold Impl.remove
  wp_pures
  wp_bind &acquire _
  iapply acquire_spec $$ Hlock
  iintro ⟨Hlocked, HR⟩
  icases HR with ⟨%x0, %nlk, %al0, Hdisj⟩
  wp_pures
  wp_bind !_
  icases Hdisj with (⟨HDlock, Hpt⟩ | ⟨%nid0, %loc0, #HlockSucc, Hpt, HDlock⟩)
  · -- LEFT: node.next = none — impossible under `adjacent σ id sid`
    iapply wp_load $$ Hpt
    iintro !> Hpt
    wp_pures
    iapply fupd_wp
    iinv Hinv with ⟨HI, Hclinv⟩
    icases (isArrINV_unfold γL γ γS).mp $$ HI with ⟨%σ0, %vI, %m, HDm, #HrootI, HSauth, %Hcoup⟩
    iauopen HAU with ⟨%σ, Hpre, Hclose⟩
    icases Hpre with ⟨Hcont, Hnode, Hsnode, %Hadj⟩
    icases (Arr.isContents_unfold γ σ).mp $$ Hcont with ⟨%vc, %γLc, %γSc, #Hrootc, HSfrag, Hcontents⟩
    icases (arrRoot_agree γ vI vc γL γS γLc γSc) $$ HrootI Hrootc with %Hall2
    obtain ⟨HvIc, HγLc, HγSc⟩ := Hall2
    subst γLc; subst γSc; subst vI
    icases (arrState_agree γS σ0 σ) $$ HSauth HSfrag with %Hσeq
    subst σ0
    have Hwf := Hcoup.2.2
    obtain ⟨pre, post, xx, sx, hcells⟩ := Hadj
    ihave Hc2 : contents γL vc (pre ++ (id, xx) :: (sid, sx) :: post) $$ [Hcontents]
    · rw [← hcells]; iexact Hcontents
    icases (contents_removeAfter_extract γL id sid pre post xx sx vc (hcells ▸ Hwf.idUqi)) $$ Hc2
      with ⟨%ptrc, %sptrc, %x0c, %ssucc, HDcontNode, HDcontS, Hwand⟩
    icases (dataPointsto_agree γL id ptr ptrc x0 x0c none (some sid) al0 true _ _) $$ HDlock HDcontNode with %Hag
    obtain ⟨_, _, hs, _⟩ := Hag
    simp at hs
  · -- RIGHT: node.next = some(&nlk, #loc0)
    iapply wp_load $$ Hpt
    iintro !> Hpt
    wp_pures
    wp_bind &acquire _
    icases (isArrLockINV_unfold' γL nid0 hl_val((&nlk, #loc0))).mp $$ HlockSucc with ⟨%slk, %sγlock, %sptr0, %HseqV, #HlockS⟩
    obtain ⟨rfl, rfl⟩ : nlk = slk ∧ loc0 = sptr0 := by
      injection HseqV with h1 h2; injection h2 with h3; injection h3 with h4; exact ⟨h1, h4⟩
    iapply acquire_spec $$ HlockS
    iintro ⟨HlockedS, HRS⟩
    icases HRS with ⟨%nx, %nnlk, %nal, HdisjS⟩
    wp_pures
    wp_bind !_
    icases HdisjS with (⟨HDlockS, HptS⟩ | ⟨%snid, %sloc, #HlockSS, HptS, HDlockS⟩)
    · -- LEFT-S: successor `sid` is the last node (its succ = none)
      iapply wp_load $$ HptS
      iintro !> HptS
      wp_pures
      wp_bind (_ ← _)
      iapply wp_store $$ Hpt
      iintro !> Hpt
      wp_pures
      -- LINEARIZATION POINT (store relinked node past sid)
      iapply fupd_wp
      iinv Hinv with ⟨HI, Hclinv⟩
      icases (isArrINV_unfold γL γ γS).mp $$ HI with ⟨%σ0, %vI, %m, HDm, #HrootI, HSauth, %Hcoup⟩
      iauopen HAU with ⟨%σ, Hpre, Hclose⟩
      icases Hpre with ⟨Hcont, Hnode, Hsnode, %Hadj⟩
      icases (Arr.isContents_unfold γ σ).mp $$ Hcont with ⟨%vc, %γLc, %γSc, #Hrootc, HSfrag, Hcontents⟩
      icases (arrRoot_agree γ vI vc γL γS γLc γSc) $$ HrootI Hrootc with %Hall2
      obtain ⟨HvIc, HγLc, HγSc⟩ := Hall2
      subst γLc; subst γSc; subst vI
      icases (arrState_agree γS σ0 σ) $$ HSauth HSfrag with %Hσeq
      subst σ0
      have Hwf := Hcoup.2.2
      obtain ⟨pre, post, xx, sx, hcells⟩ := Hadj
      obtain ⟨hidsid, hpreS, hpostS⟩ := Arr.nodup_ne_sid id sid xx sx pre post (hcells ▸ Hwf.idUqi)
      have Hmemid : id ∈ σ.cells.map (·.1) := List.mem_map.mpr ⟨(id, xx), by rw [hcells]; simp, rfl⟩
      have Hmemsid : sid ∈ σ.cells.map (·.1) := List.mem_map.mpr ⟨(sid, sx), by rw [hcells]; simp, rfl⟩
      have hidlt : id < σ.counter := by
        obtain ⟨p, hp, hpid⟩ := List.mem_map.mp Hmemid; rw [← hpid]; exact Hwf.counterFresh p hp
      have hsidlt : sid < σ.counter := by
        obtain ⟨p, hp, hpid⟩ := List.mem_map.mp Hmemsid; rw [← hpid]; exact Hwf.counterFresh p hp
      have hrcells : (σ.remove sid).cells = pre ++ (id, xx) :: post := by
        show σ.cells.filter (·.1 ≠ sid) = _
        rw [hcells]; exact Arr.filter_removeAfter id sid xx sx pre post hidsid hpreS hpostS
      ihave Hc2 : contents γL vc (pre ++ (id, xx) :: (sid, sx) :: post) $$ [Hcontents]
      · rw [← hcells]; iexact Hcontents
      icases (contents_removeAfter_extract γL id sid pre post xx sx vc (hcells ▸ Hwf.idUqi)) $$ Hc2
        with ⟨%ptrc, %sptrc, %x0c, %ssucc, HDcontNode, HDcontS, Hwand⟩
      -- node lock ↔ node contents: learn nid0 = sid, al0 = true, ptr/x0 unify
      icases (dataPointsto_agree γL id ptr ptrc x0 x0c (some nid0) (some sid) al0 true _ _) $$ HDlock HDcontNode with %Hag
      obtain ⟨hpc, hxc, hnid, hal⟩ := Hag
      injection hnid with hnideq
      subst hpc; subst hxc; subst nid0; subst hal
      -- node lock ↔ node record
      icases (Arr.idRecord_unfold γ hl_val((&lk, #ptr)) id).mp $$ Hnode with ⟨%vN, %γLN, %γSN, %_lkNr, %ptrN, #HrootN, %_HnodeEqNr, HidRec, -⟩
      icases (arrRoot_agree γ v vN γL γS γLN γSN) $$ Hroot HrootN with %HallN
      obtain ⟨_, HγLN, HγSN⟩ := HallN
      subst HγLN; subst HγSN
      icases (Arr.idRecord_unfold γ snode sid).mp $$ Hsnode with ⟨%vsN, %γLsN, %γSsN, %_lkSr, %ptrSN, #HrootsN, %_HsnodeEqNr, HsRec, -⟩
      icases (arrRoot_agree γ v vsN γL γS γLsN γSsN) $$ Hroot HrootsN with %HallsN
      obtain ⟨_, HγLsN, HγSsN⟩ := HallsN
      subst HγLsN; subst HγSsN
      icases HidRec with ⟨%rval, %rsucc, HDrec⟩
      icases (dataPointsto_agree γL id ptr ptrN x0 rval (some sid) rsucc true true _ _) $$ HDlock HDrec with %HagR
      obtain ⟨hpN, hrv, hrs, -⟩ := HagR
      subst hpN; subst hrv; subst hrs
      -- sid contents ↔ sid lock: learn ssucc = none, nal = true
      icases (dataPointsto_agree γL sid sptrc loc0 sx nx ssucc none true nal _ _) $$ HDcontS HDlockS with %HagS
      obtain ⟨hspc, hsx, hssucc, hnal⟩ := HagS
      subst sptrc; subst sx; subst hssucc; subst nal
      -- snode record ↔ sid lock
      icases HsRec with ⟨%sval, %ssucc0, HsDrec⟩
      icases (dataPointsto_agree γL sid loc0 ptrSN nx sval none ssucc0 true true _ _) $$ HDlockS HsDrec with %HagSR
      obtain ⟨hpSN, hsvS, hssS, -⟩ := HagSR
      subst hpSN; subst hsvS; subst hssS
      -- node: gather own-1, update succ (some sid → none)
      ihave HDnodeFull : dataPointsto γL id ptr x0 (some sid) true (DFrac.own 1) $$ [HDlock HDcontNode HDrec]
      · iapply data_combine3; iframe HDlock HDcontNode HDrec
      imod (dataMap_update γL m id ptr x0 (some sid) none true true) $$ HDm HDnodeFull with ⟨HDm, HDnodeFull⟩
      icases (data_split3 γL id ptr x0 none true) $$ HDnodeFull with ⟨HDlock', HDcontNode', HDrec'⟩
      -- sid: gather own-1, flip alive true → false
      ihave HDsidFull : dataPointsto γL sid loc0 nx none true (DFrac.own 1) $$ [HDlockS HDcontS HsDrec]
      · iapply data_combine3; iframe HDlockS HDcontS HsDrec
      imod (dataMap_update γL (PartialMap.insert m id (ptr, x0, none, true)) sid loc0 nx none none true false) $$ HDm HDsidFull with ⟨HDm, HDsidFull⟩
      icases (data_split3 γL sid loc0 nx none false) $$ HDsidFull with ⟨HDlockS', HDcontS', HsDrec'⟩
      imod (arrState_update γS σ (σ.remove sid)) $$ HSauth HSfrag with ⟨HSauth, HSfrag⟩
      ihave Hcontents' : contents γL vc (pre ++ (id, xx) :: post) $$ [HDcontNode' Hwand]
      · iapply Hwand $$ HDcontNode'
      icases Hclose with ⟨-, Hcommit⟩
      imod Hcommit $$ [Hrootc HSfrag Hcontents' HDrec'] with HΦ
      · isplitl [Hrootc HSfrag Hcontents']
        · unfold Arr.isContents
          iexists vc, γL, γS
          iframe Hrootc HSfrag
          rw [hrcells]; iexact Hcontents'
        · unfold Arr.idRecord
          iexists v, γL, γS, lk, ptr
          iframe Hroot
          isplit
          · ipureintro; rfl
          isplitl [HDrec']
          · iexists x0, none; iframe HDrec'
          · iexact HlockNode
      ihave HInew : isArrINV γL γ γS $$ [HDm HrootI HSauth]
      · unfold isArrINV
        iexists (σ.remove sid), vc, (PartialMap.insert (PartialMap.insert m id (ptr, x0, none, true)) sid (loc0, nx, none, false))
        iframe HDm HrootI HSauth
        ipureintro
        refine ⟨?_, ?_, Arr.remove_wellFormed σ Hwf sid⟩
        · intro id'
          rw [Arr.remove_ids_mem σ sid id']
          by_cases hsi : id' = sid
          · subst hsi
            constructor
            · rintro ⟨h, _⟩; exact absurd rfl h
            · rintro ⟨loc, xv, sl, hg⟩
              rw [LawfulPartialMap.get?_insert, if_pos rfl] at hg
              exact absurd hg (by simp)
          · rw [LawfulPartialMap.get?_insert, if_neg (fun h => hsi h.symm)]
            by_cases hii : id' = id
            · subst hii
              constructor
              · rintro _; exact ⟨ptr, x0, none, by rw [LawfulPartialMap.get?_insert, if_pos rfl]⟩
              · rintro _; exact ⟨hidsid, Hmemid⟩
            · rw [LawfulPartialMap.get?_insert, if_neg (fun h => hii h.symm), ← Hcoup.1 id']
              constructor
              · rintro ⟨_, h⟩; exact h
              · intro h; exact ⟨hsi, h⟩
        · intro id'
          intro hdom'
          show id' < (σ.remove sid).counter
          by_cases hsi : id' = sid
          · subst hsi; exact hsidlt
          · by_cases hii : id' = id
            · subst hii; exact hidlt
            · have heq : get? (PartialMap.insert (PartialMap.insert m id (ptr, x0, none, true)) sid (loc0, nx, none, false)) id' = get? m id' := by
                rw [LawfulPartialMap.get?_insert, if_neg (fun h => hsi h.symm),
                    LawfulPartialMap.get?_insert, if_neg (fun h => hii h.symm)]
              have hd : PartialMap.dom m id' := by
                unfold PartialMap.dom at hdom' ⊢; rw [← heq]; exact hdom'
              exact Hcoup.2.1 id' hd
      imod Hclinv $$ HInew
      imodintro
      -- release sid's lock (LEFT form: alive=false, succ=none)
      ihave HRSbody : lockBody γL sid loc0 $$ [HDlockS' HptS]
      · iexists nx, nnlk, false
        ileft; iframe HDlockS' HptS
      ihave HresS : iprop(SpinLock.isLock sγlock nlk (lockBody γL sid loc0) ∗ (SpinLock.locked sγlock ∗ lockBody γL sid loc0)) $$ [HlockS HlockedS HRSbody]
      · iframe HlockS HlockedS HRSbody
      wp_bind &release _
      iapply release_spec $$ HresS
      iintro -
      wp_pures
      -- release node's lock (LEFT form: alive=true, succ=none)
      ihave HRNbody : lockBody γL id ptr $$ [HDlock' Hpt]
      · iexists x0, nlk, true
        ileft; iframe HDlock' Hpt
      ihave HresN : iprop(SpinLock.isLock γlock lk (lockBody γL id ptr) ∗ (SpinLock.locked γlock ∗ lockBody γL id ptr)) $$ [Hlock Hlocked HRNbody]
      · iframe Hlock Hlocked HRNbody
      wp_bind &release _
      iapply release_spec $$ HresN
      iintro -
      wp_pures
      iexact HΦ
    · -- RIGHT-S: successor `sid` itself has a successor `snid`
      iapply wp_load $$ HptS
      iintro !> HptS
      wp_pures
      wp_bind (_ ← _)
      iapply wp_store $$ Hpt
      iintro !> Hpt
      wp_pures
      -- LINEARIZATION POINT
      iapply fupd_wp
      iinv Hinv with ⟨HI, Hclinv⟩
      icases (isArrINV_unfold γL γ γS).mp $$ HI with ⟨%σ0, %vI, %m, HDm, #HrootI, HSauth, %Hcoup⟩
      iauopen HAU with ⟨%σ, Hpre, Hclose⟩
      icases Hpre with ⟨Hcont, Hnode, Hsnode, %Hadj⟩
      icases (Arr.isContents_unfold γ σ).mp $$ Hcont with ⟨%vc, %γLc, %γSc, #Hrootc, HSfrag, Hcontents⟩
      icases (arrRoot_agree γ vI vc γL γS γLc γSc) $$ HrootI Hrootc with %Hall2
      obtain ⟨HvIc, HγLc, HγSc⟩ := Hall2
      subst γLc; subst γSc; subst vI
      icases (arrState_agree γS σ0 σ) $$ HSauth HSfrag with %Hσeq
      subst σ0
      have Hwf := Hcoup.2.2
      obtain ⟨pre, post, xx, sx, hcells⟩ := Hadj
      obtain ⟨hidsid, hpreS, hpostS⟩ := Arr.nodup_ne_sid id sid xx sx pre post (hcells ▸ Hwf.idUqi)
      have Hmemid : id ∈ σ.cells.map (·.1) := List.mem_map.mpr ⟨(id, xx), by rw [hcells]; simp, rfl⟩
      have Hmemsid : sid ∈ σ.cells.map (·.1) := List.mem_map.mpr ⟨(sid, sx), by rw [hcells]; simp, rfl⟩
      have hidlt : id < σ.counter := by
        obtain ⟨p, hp, hpid⟩ := List.mem_map.mp Hmemid; rw [← hpid]; exact Hwf.counterFresh p hp
      have hsidlt : sid < σ.counter := by
        obtain ⟨p, hp, hpid⟩ := List.mem_map.mp Hmemsid; rw [← hpid]; exact Hwf.counterFresh p hp
      have hrcells : (σ.remove sid).cells = pre ++ (id, xx) :: post := by
        show σ.cells.filter (·.1 ≠ sid) = _
        rw [hcells]; exact Arr.filter_removeAfter id sid xx sx pre post hidsid hpreS hpostS
      ihave Hc2 : contents γL vc (pre ++ (id, xx) :: (sid, sx) :: post) $$ [Hcontents]
      · rw [← hcells]; iexact Hcontents
      icases (contents_removeAfter_extract γL id sid pre post xx sx vc (hcells ▸ Hwf.idUqi)) $$ Hc2
        with ⟨%ptrc, %sptrc, %x0c, %ssucc, HDcontNode, HDcontS, Hwand⟩
      icases (dataPointsto_agree γL id ptr ptrc x0 x0c (some nid0) (some sid) al0 true _ _) $$ HDlock HDcontNode with %Hag
      obtain ⟨hpc, hxc, hnid, hal⟩ := Hag
      injection hnid with hnideq
      subst hpc; subst hxc; subst nid0; subst hal
      icases (Arr.idRecord_unfold γ hl_val((&lk, #ptr)) id).mp $$ Hnode with ⟨%vN, %γLN, %γSN, %_lkNr, %ptrN, #HrootN, %_HnodeEqNr, HidRec, -⟩
      icases (arrRoot_agree γ v vN γL γS γLN γSN) $$ Hroot HrootN with %HallN
      obtain ⟨_, HγLN, HγSN⟩ := HallN
      subst HγLN; subst HγSN
      icases (Arr.idRecord_unfold γ snode sid).mp $$ Hsnode with ⟨%vsN, %γLsN, %γSsN, %_lkSr, %ptrSN, #HrootsN, %_HsnodeEqNr, HsRec, -⟩
      icases (arrRoot_agree γ v vsN γL γS γLsN γSsN) $$ Hroot HrootsN with %HallsN
      obtain ⟨_, HγLsN, HγSsN⟩ := HallsN
      subst HγLsN; subst HγSsN
      icases HidRec with ⟨%rval, %rsucc, HDrec⟩
      icases (dataPointsto_agree γL id ptr ptrN x0 rval (some sid) rsucc true true _ _) $$ HDlock HDrec with %HagR
      obtain ⟨hpN, hrv, hrs, -⟩ := HagR
      subst hpN; subst hrv; subst hrs
      icases (dataPointsto_agree γL sid sptrc loc0 sx nx ssucc (some snid) true nal _ _) $$ HDcontS HDlockS with %HagS
      obtain ⟨hspc, hsx, hssucc, hnal⟩ := HagS
      subst sptrc; subst sx; subst ssucc; subst nal
      icases HsRec with ⟨%sval, %ssucc0, HsDrec⟩
      icases (dataPointsto_agree γL sid loc0 ptrSN nx sval (some snid) ssucc0 true true _ _) $$ HDlockS HsDrec with %HagSR
      obtain ⟨hpSN, hsvS, hssS, -⟩ := HagSR
      subst hpSN; subst hsvS; subst hssS
      -- node: gather own-1, update succ (some sid → some snid)
      ihave HDnodeFull : dataPointsto γL id ptr x0 (some sid) true (DFrac.own 1) $$ [HDlock HDcontNode HDrec]
      · iapply data_combine3; iframe HDlock HDcontNode HDrec
      imod (dataMap_update γL m id ptr x0 (some sid) (some snid) true true) $$ HDm HDnodeFull with ⟨HDm, HDnodeFull⟩
      icases (data_split3 γL id ptr x0 (some snid) true) $$ HDnodeFull with ⟨HDlock', HDcontNode', HDrec'⟩
      -- sid: gather own-1, flip alive true → false
      ihave HDsidFull : dataPointsto γL sid loc0 nx (some snid) true (DFrac.own 1) $$ [HDlockS HDcontS HsDrec]
      · iapply data_combine3; iframe HDlockS HDcontS HsDrec
      imod (dataMap_update γL (PartialMap.insert m id (ptr, x0, some snid, true)) sid loc0 nx (some snid) (some snid) true false) $$ HDm HDsidFull with ⟨HDm, HDsidFull⟩
      icases (data_split3 γL sid loc0 nx (some snid) false) $$ HDsidFull with ⟨HDlockS', HDcontS', HsDrec'⟩
      imod (arrState_update γS σ (σ.remove sid)) $$ HSauth HSfrag with ⟨HSauth, HSfrag⟩
      ihave Hcontents' : contents γL vc (pre ++ (id, xx) :: post) $$ [HDcontNode' Hwand]
      · iapply Hwand $$ HDcontNode'
      icases Hclose with ⟨-, Hcommit⟩
      imod Hcommit $$ [Hrootc HSfrag Hcontents' HDrec'] with HΦ
      · isplitl [Hrootc HSfrag Hcontents']
        · unfold Arr.isContents
          iexists vc, γL, γS
          iframe Hrootc HSfrag
          rw [hrcells]; iexact Hcontents'
        · unfold Arr.idRecord
          iexists v, γL, γS, lk, ptr
          iframe Hroot
          isplit
          · ipureintro; rfl
          isplitl [HDrec']
          · iexists x0, (some snid); iframe HDrec'
          · iexact HlockNode
      ihave HInew : isArrINV γL γ γS $$ [HDm HrootI HSauth]
      · unfold isArrINV
        iexists (σ.remove sid), vc, (PartialMap.insert (PartialMap.insert m id (ptr, x0, some snid, true)) sid (loc0, nx, some snid, false))
        iframe HDm HrootI HSauth
        ipureintro
        refine ⟨?_, ?_, Arr.remove_wellFormed σ Hwf sid⟩
        · intro id'
          rw [Arr.remove_ids_mem σ sid id']
          by_cases hsi : id' = sid
          · subst hsi
            constructor
            · rintro ⟨h, _⟩; exact absurd rfl h
            · rintro ⟨loc, xv, sl, hg⟩
              rw [LawfulPartialMap.get?_insert, if_pos rfl] at hg
              exact absurd hg (by simp)
          · rw [LawfulPartialMap.get?_insert, if_neg (fun h => hsi h.symm)]
            by_cases hii : id' = id
            · subst hii
              constructor
              · rintro _; exact ⟨ptr, x0, some snid, by rw [LawfulPartialMap.get?_insert, if_pos rfl]⟩
              · rintro _; exact ⟨hidsid, Hmemid⟩
            · rw [LawfulPartialMap.get?_insert, if_neg (fun h => hii h.symm), ← Hcoup.1 id']
              constructor
              · rintro ⟨_, h⟩; exact h
              · intro h; exact ⟨hsi, h⟩
        · intro id'
          intro hdom'
          show id' < (σ.remove sid).counter
          by_cases hsi : id' = sid
          · subst hsi; exact hsidlt
          · by_cases hii : id' = id
            · subst hii; exact hidlt
            · have heq : get? (PartialMap.insert (PartialMap.insert m id (ptr, x0, some snid, true)) sid (loc0, nx, some snid, false)) id' = get? m id' := by
                rw [LawfulPartialMap.get?_insert, if_neg (fun h => hsi h.symm),
                    LawfulPartialMap.get?_insert, if_neg (fun h => hii h.symm)]
              have hd : PartialMap.dom m id' := by
                unfold PartialMap.dom at hdom' ⊢; rw [← heq]; exact hdom'
              exact Hcoup.2.1 id' hd
      imod Hclinv $$ HInew
      imodintro
      -- release sid's lock (RIGHT form: alive=false, succ=some snid)
      ihave HRSbody : lockBody γL sid loc0 $$ [HDlockS' HptS HlockSS]
      · iexists nx, nnlk, false
        iright; iexists snid, sloc
        iframe HlockSS HptS HDlockS'
      ihave HresS : iprop(SpinLock.isLock sγlock nlk (lockBody γL sid loc0) ∗ (SpinLock.locked sγlock ∗ lockBody γL sid loc0)) $$ [HlockS HlockedS HRSbody]
      · iframe HlockS HlockedS HRSbody
      wp_bind &release _
      iapply release_spec $$ HresS
      iintro -
      wp_pures
      -- release node's lock (RIGHT form: alive=true, succ=some snid)
      ihave HRNbody : lockBody γL id ptr $$ [HDlock' Hpt HlockSS]
      · iexists x0, nnlk, true
        iright; iexists snid, sloc
        iframe HlockSS Hpt HDlock'
      ihave HresN : iprop(SpinLock.isLock γlock lk (lockBody γL id ptr) ∗ (SpinLock.locked γlock ∗ lockBody γL id ptr)) $$ [Hlock Hlocked HRNbody]
      · iframe Hlock Hlocked HRNbody
      wp_bind &release _
      iapply release_spec $$ HresN
      iintro -
      wp_pures
      iexact HΦ

end Specs

end Iris.Examples.HeapLang
