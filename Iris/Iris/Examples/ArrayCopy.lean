module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Lib.SpinLock
public import Iris.HeapLang.Lib.IInv
public import Iris.Algebra.Lib.ExclAuth
public import Iris.ProgramLogic.Atomic

@[expose] public section
namespace Iris.Examples.HeapLang

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
  constOF (Agree (LeibnizO (Val × GName × GName × GName × GName)))

-- abstract-state ghost variable (ExclAuth over the whole Arr): authority in the invariant,
-- fragment in isContents — lets the invariant learn σ (incl σ.counter) at the linearization point.
abbrev ArrStateRF : COFE.OFunctorPre :=
  constOF (ExclAuth.ExclAuthR (A := LeibnizO Arr))

class ArrG (GF : BundledGFunctors) (H': outParam <| Type → Type) [LawfulFiniteMap H' Nat] where
  [dmapG : GhostMapG GF Nat (Loc × Int × Option Nat) H']
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

-- ===== the single id-keyed node map  (Nat → (Loc × Int × Option Nat)) =====
-- `dataPointsto γ id loc val succ π` : node with logical `id` lives at physical `loc`,
-- currently holds `val` and points to successor `succ`.  Fractionally split:
--   lock 1/2  +  contents 1/4  +  idRecord 1/4  (the "live token").
def dataMap (γ : GName) (m : H' (Loc × Int × Option Nat)) : IProp GF := γ ↪●MAP m
def dataPointsto (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (π : DFrac) : IProp GF :=
  γ ↪◯MAP[id]{π} (loc, v, sl)

theorem dataMap_alloc : ⊢@{IProp GF} |==> ∃ γ, dataMap γ (∅ : H' (Loc × Int × Option Nat)) := by
  unfold dataMap; iapply ghost_map_alloc_empty
theorem dataMap_lookup (γ : GName) (m : H' (Loc × Int × Option Nat)) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (π : DFrac) :
    ⊢@{IProp GF} dataMap γ m -∗ dataPointsto γ id loc v sl π -∗ ⌜get? m id = some (loc, v, sl)⌝ := by
  unfold dataMap dataPointsto; iapply ghost_map_lookup
theorem dataPointsto_agree (γ : GName) (id : Nat) (l1 l2 : Loc) (v1 v2 : Int) (s1 s2 : Option Nat) (π1 π2 : DFrac) :
    ⊢@{IProp GF} dataPointsto γ id l1 v1 s1 π1 -∗ dataPointsto γ id l2 v2 s2 π2 -∗ ⌜l1 = l2 ∧ v1 = v2 ∧ s1 = s2⌝ := by
  unfold dataPointsto
  iintro H1 H2
  icases ghost_map_elem_agree $$ [$H1 $H2] with %Heq
  ipureintro; injection Heq with h1 h; injection h with h2 h3; exact ⟨h1, h2, h3⟩
theorem dataMap_insert (γ : GName) (m : H' (Loc × Int × Option Nat)) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat)
    (Hfresh : get? m id = none) :
    ⊢@{IProp GF} dataMap γ m ==∗ dataMap γ (insert m id (loc, v, sl)) ∗ dataPointsto γ id loc v sl (.own 1) := by
  unfold dataMap dataPointsto; iapply (ghost_map_insert id (loc, v, sl) Hfresh)
theorem dataMap_update (γ : GName) (m : H' (Loc × Int × Option Nat)) (id : Nat) (loc : Loc) (v : Int) (sl sl' : Option Nat) :
    ⊢@{IProp GF} dataMap γ m -∗ dataPointsto γ id loc v sl (.own 1) ==∗
      dataMap γ (insert m id (loc, v, sl')) ∗ dataPointsto γ id loc v sl' (.own 1) := by
  unfold dataMap dataPointsto; iapply (ghost_map_update (loc, v, sl'))
theorem dataMap_delete (γ : GName) (m : H' (Loc × Int × Option Nat)) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) :
    ⊢@{IProp GF} dataMap γ m -∗ dataPointsto γ id loc v sl (.own 1) ==∗ dataMap γ (delete m id) := by
  unfold dataMap dataPointsto; iapply (ghost_map_delete id (loc, v, sl))
instance (γ : GName) (m : H' (Loc × Int × Option Nat)) : Timeless (PROP := IProp GF) (dataMap γ m) := by
  unfold dataMap; infer_instance
instance (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (π : DFrac) : Timeless (PROP := IProp GF) (dataPointsto γ id loc v sl π) := by
  unfold dataPointsto; infer_instance

/-- fractional structure: split/combine a full node fragment along `q1 + q2`. -/
theorem dataPointsto_frac (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) (p q : Qp) :
    (dataPointsto γ id loc v sl (.own (p + q)) : IProp GF) ⊣⊢
      dataPointsto γ id loc v sl (.own p) ∗ dataPointsto γ id loc v sl (.own q) :=
  (@ghost_map_elem_fractional GF Nat (Loc × Int × Option Nat) H' _ _ γ id (loc, v, sl)).fractional p q

theorem one_eq_q2_q4_q4 : (1 : Qp) = q2 + (q4 + q4) := by rw [q4_add_q4, q2_add_q2]

/-- Split a full node share into lock 1/2 + contents 1/4 + record 1/4. -/
theorem data_split3 (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) :
    (dataPointsto γ id loc v sl (.own 1) : IProp GF) ⊢
      dataPointsto γ id loc v sl (.own q2) ∗ dataPointsto γ id loc v sl (.own q4) ∗ dataPointsto γ id loc v sl (.own q4) := by
  rw [one_eq_q2_q4_q4]
  iintro H
  icases (dataPointsto_frac γ id loc v sl q2 (q4 + q4)).mp $$ H with ⟨H1, H2⟩
  icases (dataPointsto_frac γ id loc v sl q4 q4).mp $$ H2 with ⟨H3, H4⟩
  iframe H1 H3 H4

/-- Combine lock 1/2 + contents 1/4 + record 1/4 (same value) into a full node share. -/
theorem data_combine3 (γ : GName) (id : Nat) (loc : Loc) (v : Int) (sl : Option Nat) :
    (dataPointsto γ id loc v sl (.own q2) ∗ dataPointsto γ id loc v sl (.own q4) ∗ dataPointsto γ id loc v sl (.own q4) : IProp GF) ⊢
      dataPointsto γ id loc v sl (.own 1) := by
  rw [one_eq_q2_q4_q4]
  iintro ⟨H1, H3, H4⟩
  iapply (dataPointsto_frac γ id loc v sl q2 (q4 + q4)).mpr
  iframe H1
  iapply (dataPointsto_frac γ id loc v sl q4 q4).mpr
  iframe H3 H4


def arrRoot (γ : GName) (v : Val) (γL γI γH γS : GName) : IProp GF :=
  iOwn (E := ArrG.rootG) γ (toAgree (⟨(v, γL, γI, γH, γS)⟩ : LeibnizO _))

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
theorem arrRoot_alloc (v : Val) (γL γI γH γS : GName) :
    ⊢@{IProp GF} |==> ∃ γ, arrRoot γ v γL γI γH γS := by
  unfold arrRoot; iapply (iOwn_alloc (E := ArrG.rootG) _ Agree.toAgree_valid)
theorem arrRoot_agree (γ : GName) (v v' : Val) (γL γI γH γS γL' γI' γH' γS' : GName) :
    ⊢@{IProp GF} arrRoot γ v γL γI γH γS -∗ arrRoot γ v' γL' γI' γH' γS' -∗
      ⌜v = v' ∧ γL = γL' ∧ γI = γI' ∧ γH = γH' ∧ γS = γS'⌝ := by
  unfold arrRoot
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  have h := congrArg LeibnizO.car (toAgree_op_valid_iff_eq.mp Hvalid)
  injection h with h1 h; injection h with h2 h; injection h with h3 h; injection h with h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩
instance (γ : GName) (v : Val) (γL γI γH γS : GName) : Persistent (PROP := IProp GF) (arrRoot γ v γL γI γH γS) := by
  unfold arrRoot; infer_instance
instance (γ : GName) (v : Val) (γL γI γH γS : GName) : Timeless (PROP := IProp GF) (arrRoot γ v γL γI γH γS) := by
  unfold arrRoot; infer_instance

end RA

variable {GF : BundledGFunctors} [LawfulFiniteMap H' Nat]
variable [HeapLangGS hlc GF] [SpinLockG GF] [ArrG GF H']

def isArrLockINV_pre (Ψ : GName → Nat → Val → IProp GF) (γL : GName) (id : Nat) (node : Val) : IProp GF := iprop%
  ∃ (lk : Val) (γlock : GName) (ptr : Loc), ⌜node = hl_val((&lk, #ptr))⌝ ∗
    SpinLock.isLock γlock lk iprop(
      ∃ (x : Int) (nlk : Val),
        ((dataPointsto γL id ptr x none (DFrac.own q2)) ∗
          ptr ↦ hl_val((#x, none()))
          ∨
        (∃ (nid : Nat) (loc : Loc), Ψ γL nid hl_val((&nlk, #loc)) ∗
          ptr ↦ hl_val((#x, some((&nlk, #loc)))) ∗
          dataPointsto γL id ptr x (some nid) (DFrac.own q2))))

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
    · exact ⟨fun _ _ _ h => wandIff_ne.ne (exists_ne (fun (x : Int) => exists_ne (fun (nlk : Val) => BI.or_ne.ne .rfl (exists_ne (fun (nid : Nat) => exists_ne (fun (loc : Loc) => BI.sep_ne.ne (h γL nid hl_val((&nlk, #loc))) .rfl)))))) .rfl⟩
    · iapply equiv_wandIff; exact .rfl
  · iintro ⟨%lk, %γlock, %ptr, %Hn, H⟩
    iexists lk, γlock, ptr
    isplit
    · ipureintro; exact Hn
    iapply SpinLock.is_lock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne .rfl (exists_ne (fun (x : Int) => exists_ne (fun (nlk : Val) => BI.or_ne.ne .rfl (exists_ne (fun (nid : Nat) => exists_ne (fun (loc : Loc) => BI.sep_ne.ne (h γL nid hl_val((&nlk, #loc))) .rfl))))))⟩
    · iapply equiv_wandIff; exact .rfl

def isArrLockINV : GName → Nat → Val → IProp GF := fixpoint isArrLockINV_pre

theorem isArrLockINV_unfold (γL : GName) (id : Nat) (v : Val) :
    (isArrLockINV γL id v : IProp GF) ⊣⊢ isArrLockINV_pre isArrLockINV γL id v := by
  have _hHH : (H') = (H') := rfl
  exact equiv_iff.mp (fixpoint_unfold
    (f := Function.toContractiveHom (isArrLockINV_pre (GF := GF) (H' := H'))) γL id v)

-- fully-spelled-out unfold (defeq to the pre), for destructuring on proofmode hyps
theorem isArrLockINV_unfold' (γL : GName) (id : Nat) (v : Val) :
    (isArrLockINV γL id v : IProp GF) ⊣⊢
      ∃ (lk : Val) (γlock : GName) (ptr : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        SpinLock.isLock γlock lk iprop(
          ∃ (x : Int) (nlk : Val),
            ((dataPointsto γL id ptr x none (DFrac.own q2)) ∗ ptr ↦ hl_val((#x, none()))
              ∨
             (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk, #loc)) ∗
               ptr ↦ hl_val((#x, some((&nlk, #loc)))) ∗
               dataPointsto γL id ptr x (some nid) (DFrac.own q2)))) :=
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
      dataPointsto γL id ptr x none (DFrac.own q4)
  | (id, x) :: (sid, sx) :: cs => iprop%
    ∃ (lk : Val) (ptr : Loc) (nlk : Val) (next : Loc),
      ⌜v = hl_val((&lk, #ptr))⌝ ∗
      dataPointsto γL id ptr x (some sid) (DFrac.own q4) ∗
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
        dataPointsto γL id ptr x none (DFrac.own q4)) := rfl

theorem contents_cons_ne (γL : GName) (v : Val) (id : Nat) (x : Int)
    (c : Nat × Int) (cs : List (Nat × Int)) :
    (contents γL v ((id, x) :: c :: cs) : IProp GF) = iprop(
      ∃ (lk : Val) (ptr : Loc) (nlk : Val) (next : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        dataPointsto γL id ptr x (some c.1) (DFrac.own q4) ∗
        contents γL hl_val((&nlk, #next)) (c :: cs)) := by
  obtain ⟨cid, cx⟩ := c; rfl

/-- Entailment form of `contents_eq_single`, usable on proofmode hypotheses via `$$`. -/
theorem contents_single_elim (γL : GName) (v : Val) (id : Nat) (x : Int) :
    (contents γL v [(id, x)] : IProp GF) ⊢ iprop(
      ∃ (lk : Val) (ptr : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        dataPointsto γL id ptr x none (DFrac.own q4)) := by
  rw [contents_eq_single]; iintro h; iexact h

/-- Entailment form of `contents_cons_ne`, usable on proofmode hypotheses via `$$`. -/
theorem contents_cons_elim (γL : GName) (v : Val) (id : Nat) (x : Int)
    (c : Nat × Int) (cs : List (Nat × Int)) :
    (contents γL v ((id, x) :: c :: cs) : IProp GF) ⊢ iprop(
      ∃ (lk : Val) (ptr : Loc) (nlk : Val) (next : Loc), ⌜v = hl_val((&lk, #ptr))⌝ ∗
        dataPointsto γL id ptr x (some c.1) (DFrac.own q4) ∗
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
          dataPointsto γL id ptr x0 succ (DFrac.own q4) ∗
          (∀ (nlkv : Val) (nptr : Loc),
              (dataPointsto γL id ptr x0 (some counter) (DFrac.own q4) ∗
               dataPointsto γL counter nptr xnew succ (DFrac.own q4))
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
          dataPointsto γL id ptr x0 (some sid) (DFrac.own q4) ∗
          dataPointsto γL sid sptr sx ssucc (DFrac.own q4) ∗
          (dataPointsto γL id ptr x0 ssucc (DFrac.own q4) -∗
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

def isArrINV (γL γI γA γH γS : GName) : IProp GF := iprop%
  ∃ (σ : Arr) (v : Val) (m : H' (Loc × Int × Option Nat)),
    dataMap γL m ∗ arrRoot γA v γL γI γH γS ∗ arrState γS σ ∗
  ⌜ ∀ id, dom m id ↔ id ∈ σ.cells.map (·.1) ⌝

instance isArrINV_timeless (γL γI γA γH γS : GName) :
    Timeless (PROP := IProp GF) (isArrINV γL γI γA γH γS) := by
  unfold isArrINV; infer_instance

theorem isArrINV_unfold (γL γI γA γH γS : GName) :
    (isArrINV γL γI γA γH γS : IProp GF) ⊣⊢
      ∃ (σ : Arr) (v : Val) (m : H' (Loc × Int × Option Nat)),
        dataMap γL m ∗ arrRoot γA v γL γI γH γS ∗ arrState γS σ ∗
      ⌜ ∀ id, dom m id ↔ id ∈ σ.cells.map (·.1) ⌝ := .rfl


-- CORE PREDICATES
def arrN : Namespace := ndot nroot "arr"
def Arr.isArr (γ : GName) : IProp GF := iprop%
  ∃ (v : Val) (γL γI γH γS : GName),
    arrRoot γ v γL γI γH γS ∗
    isArrLockINV γL 0 v ∗
    inv arrN (isArrINV γL γI γ γH γS)
-- AI: Prove the persistent
instance Arr.isArr_persistent (γ : GName) : Persistent (PROP := IProp GF) (Arr.isArr γ) := by
  unfold Arr.isArr; infer_instance


def Arr.isContents (γ : GName) (σ : Arr) : IProp GF := iprop%
  ∃ (v : Val) (γL γI γH γS : GName),
    arrRoot γ v γL γI γH γS ∗ arrStateFrag γS σ ∗
    contents γL v σ.cells

theorem Arr.isContents_unfold (γ : GName) (σ : Arr) :
    (Arr.isContents γ σ : IProp GF) ⊣⊢
      ∃ (v : Val) (γL γI γH γS : GName),
        arrRoot γ v γL γI γH γS ∗ arrStateFrag γS σ ∗
        contents γL v σ.cells := .rfl


def Arr.idRecord (γ : GName) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ (v: Val) (γL γI γH γS : GName) (lk : Val) (ptr : Loc),
    arrRoot γ v γL γI γH γS ∗ ⌜node = hl_val((&lk, #ptr))⌝ ∗
    (∃ (val : Int) (succ : Option Nat), dataPointsto γL id ptr val succ (DFrac.own q4)) ∗
    isArrLockINV γL id node

-- trivial (defeq) unfolding lemmas, to destruct the def-wrapped predicates on proofmode hyps
theorem Arr.isArr_unfold (γ : GName) :
    (Arr.isArr γ : IProp GF) ⊣⊢
      ∃ v γL γI γH γS, arrRoot γ v γL γI γH γS ∗ isArrLockINV γL 0 v ∗
        inv arrN (isArrINV γL γI γ γH γS) := .rfl
theorem Arr.idRecord_unfold (γ : GName) (node : Val) (id : Nat) :
    (Arr.idRecord γ node id : IProp GF) ⊣⊢
      ∃ (v: Val) (γL γI γH γS : GName) (lk : Val) (ptr : Loc),
        arrRoot γ v γL γI γH γS ∗ ⌜node = hl_val((&lk, #ptr))⌝ ∗
        (∃ (val : Int) (succ : Option Nat), dataPointsto γL id ptr val succ (DFrac.own q4)) ∗
        isArrLockINV γL id node := .rfl


theorem Impl.init_spec (x : Int) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.init #x)
    ⦃ v, RET v; ∃ γ id, Arr.isArr γ ∗ Arr.isContents γ (Arr.init x) ∗ Arr.idRecord γ v id ⦄ := by
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
  imod (dataMap_insert γL ∅ 0 c x none (get?_empty _)) $$ HDm with ⟨HDm, HDf⟩
  imod (arrState_alloc (Arr.init x)) with ⟨%γS, HSauth, HSfrag⟩
  imod (arrRoot_alloc hl_val((&lk, #c)) γL γL γL γS) with ⟨%γ, #Hroot⟩
  icases (data_split3 γL 0 c x none) $$ HDf with ⟨HDlock, HDcont, HDrec⟩
  -- build the node's lock body (LEFT branch: last node, next = none)
  ihave Hbody : iprop(∃ (x0 : Int) (nlk : Val),
      ((dataPointsto γL 0 c x0 none (DFrac.own q2)) ∗ c ↦ hl_val((#x0, none()))
        ∨
       (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk, #loc)) ∗
         c ↦ hl_val((#x0, some((&nlk, #loc)))) ∗
         dataPointsto γL 0 c x0 (some nid) (DFrac.own q2)))) $$ [HDlock Hc]
  · iexists x, lk
    ileft; iframe HDlock Hc
  ispecialize Hlk $$ %_ %(⊤) Hbody
  imod Hlk with Hlock
  imod (inv_alloc arrN ⊤ (isArrINV γL γL γ γL γS)) $$ [HDm Hroot HSauth] with #Hinv
  · inext
    unfold isArrINV
    iexists (Arr.init x), hl_val((&lk, #c)), _
    iframe HDm Hroot HSauth
    ipureintro
    intro id
    simp only [PartialMap.dom, LawfulPartialMap.get?_insert, get?_empty, Arr.init,
      List.map_cons, List.map_nil, List.mem_singleton]
    by_cases h0 : id = 0
    · subst h0; simp
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
  iexists γ, 0
  isplitl []
  · unfold Arr.isArr
    iexists hl_val((&lk, #c)), γL, γL, γL, γS
    iframe Hroot HlockINV Hinv
  isplitl [HSfrag HDcont]
  · unfold Arr.isContents
    iexists hl_val((&lk, #c)), γL, γL, γL, γS
    iframe Hroot HSfrag
    rw [Arr.init]
    unfold contents
    iexists lk, c
    isplit
    · ipureintro; rfl
    iframe HDcont
  · unfold Arr.idRecord
    iexists hl_val((&lk, #c)), γL, γL, γL, γS, lk, c
    iframe Hroot
    isplit
    · ipureintro; rfl
    isplitl [HDrec]
    · iexists x, none; iframe HDrec
    · iexact HlockINV

set_option maxRecDepth 8000 in
theorem Impl.insert_spec (γ : GName) (id : Nat) (node : Val) (x : Int) :
  ⊢@{IProp GF}
    Arr.isArr γ -∗ Arr.idRecord γ node id -∗
      ⟪ ∀ σ, Arr.isContents γ σ ∗ ⌜Arr.wellFormed σ⌝ ⟫
        hl(&Impl.insert &node #x) @ arrN
      ⟪ ∃ nid, Arr.isContents γ (σ.insert id x) | ret, RET ret; Arr.idRecord γ node id ∗ Arr.idRecord γ ret nid ⟫ := by
  iintro Harr Hnode %Φ HAU
  icases (Arr.isArr_unfold γ).mp $$ Harr with ⟨%v, %γL, %γI, %γH, %γS, #Hroot, #HlockRoot, #Hinv⟩
  icases (Arr.idRecord_unfold γ node id).mp $$ Hnode with ⟨%v', %γL', %γI', %γH', %γS', %lkN, %ptrN, #Hroot', %HnodeEqN, HidRec, #HlockNode⟩
  icases (arrRoot_agree γ v v' γL γI γH γS γL' γI' γH' γS') $$ Hroot Hroot' with %Hall
  obtain ⟨_, HγL, HγI, HγH, HγS⟩ := Hall
  subst HγL; subst HγI; subst HγH; subst HγS
  icases (isArrLockINV_unfold' γL id node).mp $$ HlockNode with ⟨%lk, %γlock, %ptr, %Hnodeeq, #Hlock⟩
  rw [Hnodeeq]
  unfold Impl.insert
  wp_pures
  wp_bind &acquire _
  iapply acquire_spec $$ Hlock
  iintro ⟨Hlocked, HR⟩
  icases HR with ⟨%x0, %nlk, Hdisj⟩
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
    icases (isArrINV_unfold γL γI γ γH γS).mp $$ HI with ⟨%σ0, %vI, %m, HDm, #HrootI, HSauth, %Hcoup⟩
    iauopen HAU with ⟨%σ, Hpre, Hclose⟩
    icases Hpre with ⟨Hcont, %Hwf⟩
    icases (Arr.isContents_unfold γ σ).mp $$ Hcont with ⟨%vc, %γLc, %γIc, %γHc, %γSc, #Hrootc, HSfrag, Hcontents⟩
    icases (arrRoot_agree γ vI vc γL γI γH γS γLc γIc γHc γSc) $$ HrootI Hrootc with %Hall2
    obtain ⟨HvIc, HγLc, HγIc, HγHc, HγSc⟩ := Hall2
    subst γLc; subst γIc; subst γHc; subst γSc; subst vI
    icases (arrState_agree γS σ0 σ) $$ HSauth HSfrag with %Hσeq
    subst σ0
    icases HidRec with ⟨%rval, %rsucc, HDrec⟩
    icases (dataPointsto_agree γL id ptr ptrN x0 rval none rsucc _ _) $$ HDlock HDrec with %HagN
    obtain ⟨hpN, hrv, hrs⟩ := HagN
    subst hpN; subst hrv; subst hrs
    icases (dataMap_lookup γL m id ptr x0 none _) $$ HDm HDrec with %HgetRec
    have Hmem : id ∈ σ.cells.map (·.1) := (Hcoup id).mp (by simp [PartialMap.dom, HgetRec])
    have Hnodup : (σ.cells.map (·.1)).Nodup := Hwf.idUqi
    icases (contents_insertAfter_extract γL id σ.counter x σ.cells vc Hmem Hnodup) $$ Hcontents
      with ⟨%ptr2, %x2, %succ2, HDcont, Hwand⟩
    icases (dataPointsto_agree γL id ptr ptr2 x0 x2 none succ2 _ _) $$ HDlock HDcont with %Hag
    obtain ⟨hp2, hx2, hs2⟩ := Hag
    subst hp2; subst hx2; subst hs2
    ihave HDfull : dataPointsto γL id ptr x0 none (DFrac.own 1) $$ [HDlock HDcont HDrec]
    · iapply data_combine3; iframe HDlock HDcont HDrec
    imod (dataMap_update γL m id ptr x0 none (some σ.counter)) $$ HDm HDfull with ⟨HDm, HDfull⟩
    icases (data_split3 γL id ptr x0 (some σ.counter)) $$ HDfull with ⟨HDlock', HDcont', HDrec'⟩
    have hid_lt : id < σ.counter := by
      obtain ⟨p, hp, hpid⟩ := List.mem_map.mp Hmem
      rw [← hpid]; exact Hwf.counterFresh p hp
    have Hfresh : get? (PartialMap.insert m id (ptr, x0, some σ.counter)) σ.counter = none := by
      rw [LawfulPartialMap.get?_insert, if_neg (by omega : ¬ id = σ.counter)]
      cases h : get? m σ.counter with
      | none => rfl
      | some val =>
        exfalso
        have hdom : PartialMap.dom m σ.counter := by simp [PartialMap.dom, h]
        obtain ⟨p, hp, hpc⟩ := List.mem_map.mp ((Hcoup σ.counter).mp hdom)
        have := Hwf.counterFresh p hp; rw [hpc] at this; omega
    imod (dataMap_insert γL (PartialMap.insert m id (ptr, x0, some σ.counter)) σ.counter nptr x none Hfresh) $$ HDm with ⟨HDm, HDnew⟩
    icases (data_split3 γL σ.counter nptr x none) $$ HDnew with ⟨HDnlock, HDncont, HDnrec⟩
    imod (arrState_update γS σ (σ.insert id x)) $$ HSauth HSfrag with ⟨HSauth, HSfrag⟩
    ihave Hcontents' : contents γL vc (σ.cells.flatMap (Arr.insertBody id σ.counter x)) $$ [HDcont' HDncont Hwand]
    · iapply Hwand $$ %nlkv %nptr
      iframe HDcont' HDncont
    icases Hclose with ⟨-, Hcommit⟩
    imod Hcommit $$ %(σ.counter) [Hrootc HSfrag Hcontents'] with HΦ
    · unfold Arr.isContents
      iexists vc, γL, γI, γH, γS
      iframe Hrootc HSfrag
      rw [Arr.insert_cells_eq σ id x Hmem]
      iexact Hcontents'
    -- close the shared invariant with the updated map & state
    ihave HInew : isArrINV γL γI γ γH γS $$ [HDm HrootI HSauth]
    · unfold isArrINV
      iexists (σ.insert id x), vc, (PartialMap.insert (PartialMap.insert m id (ptr, x0, some σ.counter)) σ.counter (nptr, x, none))
      iframe HDm HrootI HSauth
      ipureintro
      intro id'
      rw [Arr.insert_ids_mem σ id x Hmem id']
      rw [LawfulPartialMap.dom_insert_iff, LawfulPartialMap.dom_insert_iff, Hcoup id']
      constructor
      · rintro (h | h | h)
        · exact Or.inl h.symm
        · exact Or.inr (h ▸ Hmem)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
    imod Hclinv $$ HInew
    -- build the new node's lock (isArrLockINV γL σ.counter (&nlkv,#nptr))
    ihave Hnbody : iprop(∃ (x0' : Int) (nlk' : Val),
        ((dataPointsto γL σ.counter nptr x0' none (DFrac.own q2)) ∗ nptr ↦ hl_val((#x0', none()))
          ∨
         (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk', #loc)) ∗
           nptr ↦ hl_val((#x0', some((&nlk', #loc)))) ∗
           dataPointsto γL σ.counter nptr x0' (some nid) (DFrac.own q2)))) $$ [HDnlock Hnptr]
    · iexists x, lk
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
    ihave HRnew : iprop(∃ (x0' : Int) (nlk' : Val),
        ((dataPointsto γL id ptr x0' none (DFrac.own q2)) ∗ ptr ↦ hl_val((#x0', none()))
          ∨
         (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk', #loc)) ∗
           ptr ↦ hl_val((#x0', some((&nlk', #loc)))) ∗
           dataPointsto γL id ptr x0' (some nid) (DFrac.own q2)))) $$ [Hpt HDlock' HnlockINV]
    · iexists x0, nlkv
      iright; iexists σ.counter, nptr
      iframe HnlockINV Hpt HDlock'
    ihave Hres : iprop(SpinLock.isLock γlock lk
        iprop(∃ (x0' : Int) (nlk' : Val),
          ((dataPointsto γL id ptr x0' none (DFrac.own q2)) ∗ ptr ↦ hl_val((#x0', none()))
            ∨
           (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk', #loc)) ∗
             ptr ↦ hl_val((#x0', some((&nlk', #loc)))) ∗
             dataPointsto γL id ptr x0' (some nid) (DFrac.own q2)))) ∗
        (SpinLock.locked γlock ∗ ∃ (x0' : Int) (nlk' : Val),
          ((dataPointsto γL id ptr x0' none (DFrac.own q2)) ∗ ptr ↦ hl_val((#x0', none()))
            ∨
           (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk', #loc)) ∗
             ptr ↦ hl_val((#x0', some((&nlk', #loc)))) ∗
             dataPointsto γL id ptr x0' (some nid) (DFrac.own q2))))) $$ [Hlock Hlocked HRnew]
    · iframe Hlock Hlocked HRnew
    wp_bind &release _
    iapply release_spec $$ Hres
    iintro -
    wp_pures
    imodintro
    ispecialize HΦ $$ %hl_val((&nlkv, #nptr))
    iunfold wandM at HΦ
    iapply HΦ
    isplitl [HDrec']
    · unfold Arr.idRecord
      iexists v, γL, γI, γH, γS, lk, ptr
      iframe Hroot
      isplit
      · ipureintro; rfl
      isplitl [HDrec']
      · iexists x0, (some σ.counter); iframe HDrec'
      · iexact HlockNode
    · unfold Arr.idRecord
      iexists v, γL, γI, γH, γS, nlkv, nptr
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
    icases (isArrINV_unfold γL γI γ γH γS).mp $$ HI with ⟨%σ0, %vI, %m, HDm, #HrootI, HSauth, %Hcoup⟩
    iauopen HAU with ⟨%σ, Hpre, Hclose⟩
    icases Hpre with ⟨Hcont, %Hwf⟩
    icases (Arr.isContents_unfold γ σ).mp $$ Hcont with ⟨%vc, %γLc, %γIc, %γHc, %γSc, #Hrootc, HSfrag, Hcontents⟩
    icases (arrRoot_agree γ vI vc γL γI γH γS γLc γIc γHc γSc) $$ HrootI Hrootc with %Hall2
    obtain ⟨HvIc, HγLc, HγIc, HγHc, HγSc⟩ := Hall2
    subst γLc; subst γIc; subst γHc; subst γSc; subst vI
    icases (arrState_agree γS σ0 σ) $$ HSauth HSfrag with %Hσeq
    subst σ0
    icases HidRec with ⟨%rval, %rsucc, HDrec⟩
    icases (dataPointsto_agree γL id ptr ptrN x0 rval (some nid0) rsucc _ _) $$ HDlock HDrec with %HagN
    obtain ⟨hpN, hrv, hrs⟩ := HagN
    subst hpN; subst hrv; subst hrs
    icases (dataMap_lookup γL m id ptr x0 (some nid0) _) $$ HDm HDrec with %HgetRec
    have Hmem : id ∈ σ.cells.map (·.1) := (Hcoup id).mp (by simp [PartialMap.dom, HgetRec])
    have Hnodup : (σ.cells.map (·.1)).Nodup := Hwf.idUqi
    icases (contents_insertAfter_extract γL id σ.counter x σ.cells vc Hmem Hnodup) $$ Hcontents
      with ⟨%ptr2, %x2, %succ2, HDcont, Hwand⟩
    icases (dataPointsto_agree γL id ptr ptr2 x0 x2 (some nid0) succ2 _ _) $$ HDlock HDcont with %Hag
    obtain ⟨hp2, hx2, hs2⟩ := Hag
    subst hp2; subst hx2; subst hs2
    ihave HDfull : dataPointsto γL id ptr x0 (some nid0) (DFrac.own 1) $$ [HDlock HDcont HDrec]
    · iapply data_combine3; iframe HDlock HDcont HDrec
    imod (dataMap_update γL m id ptr x0 (some nid0) (some σ.counter)) $$ HDm HDfull with ⟨HDm, HDfull⟩
    icases (data_split3 γL id ptr x0 (some σ.counter)) $$ HDfull with ⟨HDlock', HDcont', HDrec'⟩
    have hid_lt : id < σ.counter := by
      obtain ⟨p, hp, hpid⟩ := List.mem_map.mp Hmem
      rw [← hpid]; exact Hwf.counterFresh p hp
    have Hfresh : get? (PartialMap.insert m id (ptr, x0, some σ.counter)) σ.counter = none := by
      rw [LawfulPartialMap.get?_insert, if_neg (by omega : ¬ id = σ.counter)]
      cases h : get? m σ.counter with
      | none => rfl
      | some val =>
        exfalso
        have hdom : PartialMap.dom m σ.counter := by simp [PartialMap.dom, h]
        obtain ⟨p, hp, hpc⟩ := List.mem_map.mp ((Hcoup σ.counter).mp hdom)
        have := Hwf.counterFresh p hp; rw [hpc] at this; omega
    imod (dataMap_insert γL (PartialMap.insert m id (ptr, x0, some σ.counter)) σ.counter nptr x (some nid0) Hfresh) $$ HDm with ⟨HDm, HDnew⟩
    icases (data_split3 γL σ.counter nptr x (some nid0)) $$ HDnew with ⟨HDnlock, HDncont, HDnrec⟩
    imod (arrState_update γS σ (σ.insert id x)) $$ HSauth HSfrag with ⟨HSauth, HSfrag⟩
    ihave Hcontents' : contents γL vc (σ.cells.flatMap (Arr.insertBody id σ.counter x)) $$ [HDcont' HDncont Hwand]
    · iapply Hwand $$ %nlkv %nptr
      iframe HDcont' HDncont
    icases Hclose with ⟨-, Hcommit⟩
    imod Hcommit $$ %(σ.counter) [Hrootc HSfrag Hcontents'] with HΦ
    · unfold Arr.isContents
      iexists vc, γL, γI, γH, γS
      iframe Hrootc HSfrag
      rw [Arr.insert_cells_eq σ id x Hmem]
      iexact Hcontents'
    ihave HInew : isArrINV γL γI γ γH γS $$ [HDm HrootI HSauth]
    · unfold isArrINV
      iexists (σ.insert id x), vc, (PartialMap.insert (PartialMap.insert m id (ptr, x0, some σ.counter)) σ.counter (nptr, x, some nid0))
      iframe HDm HrootI HSauth
      ipureintro
      intro id'
      rw [Arr.insert_ids_mem σ id x Hmem id']
      rw [LawfulPartialMap.dom_insert_iff, LawfulPartialMap.dom_insert_iff, Hcoup id']
      constructor
      · rintro (h | h | h)
        · exact Or.inl h.symm
        · exact Or.inr (h ▸ Hmem)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
    imod Hclinv $$ HInew
    ihave Hnbody : iprop(∃ (x0' : Int) (nlk' : Val),
        ((dataPointsto γL σ.counter nptr x0' none (DFrac.own q2)) ∗ nptr ↦ hl_val((#x0', none()))
          ∨
         (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk', #loc)) ∗
           nptr ↦ hl_val((#x0', some((&nlk', #loc)))) ∗
           dataPointsto γL σ.counter nptr x0' (some nid) (DFrac.own q2)))) $$ [HDnlock Hnptr HlockSucc]
    · iexists x, nlk
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
    ihave HRnew : iprop(∃ (x0' : Int) (nlk' : Val),
        ((dataPointsto γL id ptr x0' none (DFrac.own q2)) ∗ ptr ↦ hl_val((#x0', none()))
          ∨
         (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk', #loc)) ∗
           ptr ↦ hl_val((#x0', some((&nlk', #loc)))) ∗
           dataPointsto γL id ptr x0' (some nid) (DFrac.own q2)))) $$ [Hpt HDlock' HnlockINV]
    · iexists x0, nlkv
      iright; iexists σ.counter, nptr
      iframe HnlockINV Hpt HDlock'
    ihave Hres : iprop(SpinLock.isLock γlock lk
        iprop(∃ (x0' : Int) (nlk' : Val),
          ((dataPointsto γL id ptr x0' none (DFrac.own q2)) ∗ ptr ↦ hl_val((#x0', none()))
            ∨
           (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk', #loc)) ∗
             ptr ↦ hl_val((#x0', some((&nlk', #loc)))) ∗
             dataPointsto γL id ptr x0' (some nid) (DFrac.own q2)))) ∗
        (SpinLock.locked γlock ∗ ∃ (x0' : Int) (nlk' : Val),
          ((dataPointsto γL id ptr x0' none (DFrac.own q2)) ∗ ptr ↦ hl_val((#x0', none()))
            ∨
           (∃ (nid : Nat) (loc : Loc), isArrLockINV γL nid hl_val((&nlk', #loc)) ∗
             ptr ↦ hl_val((#x0', some((&nlk', #loc)))) ∗
             dataPointsto γL id ptr x0' (some nid) (DFrac.own q2))))) $$ [Hlock Hlocked HRnew]
    · iframe Hlock Hlocked HRnew
    wp_bind &release _
    iapply release_spec $$ Hres
    iintro -
    wp_pures
    imodintro
    ispecialize HΦ $$ %hl_val((&nlkv, #nptr))
    iunfold wandM at HΦ
    iapply HΦ
    isplitl [HDrec']
    · unfold Arr.idRecord
      iexists v, γL, γI, γH, γS, lk, ptr
      iframe Hroot
      isplit
      · ipureintro; rfl
      isplitl [HDrec']
      · iexists x0, (some σ.counter); iframe HDrec'
      · iexact HlockNode
    · unfold Arr.idRecord
      iexists v, γL, γI, γH, γS, nlkv, nptr
      iframe Hroot
      isplit
      · ipureintro; rfl
      isplitl [HDnrec]
      · iexists x, (some nid0); iframe HDnrec
      · iexact HnlockINV

theorem Impl.remove_spec (γ : GName) (id sid : Nat) (node snode : Val) :
  ⊢@{IProp GF}
    Arr.isArr γ -∗ Arr.idRecord γ node id -∗ Arr.idRecord γ snode sid -∗
      ⟪ ∀ σ, Arr.isContents γ σ ∗ ⌜Arr.wellFormed σ ∧ Arr.adjacent σ id sid⌝  ⟫
        hl(&Impl.remove &node) @ arrN
      ⟪ ∃ u, Arr.isContents γ (σ.remove sid) ∗ ⌜u = sid⌝ | ret, RET ret; Arr.idRecord γ node id ⟫ := by
  sorry

end Specs

end Iris.Examples.HeapLang
