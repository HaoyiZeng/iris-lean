module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Lib.SpinLock
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
    &release(lk)
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
      free(nptr);
      let nnext := snd(ncontents);
      ptr ← (fst(contents), nnext);
      &release(nlk);
      &release(lk)

section Specs

open Std PartialMap

abbrev ArrNameRF : COFE.OFunctorPre :=
  constOF (Agree (LeibnizO (Val × GName × GName × GName)))

class ArrG (GF : BundledGFunctors) (H H': outParam <| Type → Type) [LawfulFiniteMap H' Nat]  [LawfulFiniteMap H Loc] where
  [vmapG : GhostMapG GF Loc (Int × (Option Loc)) H]
  [nmapG : GhostMapG GF Loc Nat H]
  [rmapG : GhostMapG GF Nat Val H']
  [rootG : ElemG GF ArrNameRF]

attribute [reducible, instance] ArrG.vmapG ArrG.nmapG ArrG.rootG ArrG.rmapG
open Iris.BI

section RA
variable [LawfulFiniteMap H Loc] [LawfulFiniteMap H' Nat] [ArrG GF H H']

def idMap (γ : GName) (m : H Nat) : IProp GF := γ ↪●MAP m
def idPointsto (γ : GName) (loc : Loc) (id : Nat) (π : DFrac) : IProp GF :=  γ ↪◯MAP[loc]{π} id

-- ===== id map  (Loc → Nat) =====
theorem idMap_alloc : ⊢@{IProp GF} |==> ∃ γ, idMap γ (∅ : H Nat) := by
  unfold idMap; iapply ghost_map_alloc_empty
theorem idMap_lookup (γ : GName) (n : H Nat) (loc : Loc) (id : Nat) (π : DFrac) :
    ⊢@{IProp GF} idMap γ n -∗ idPointsto γ loc id π -∗ ⌜get? n loc = some id⌝ := by
 unfold idMap idPointsto; iapply ghost_map_lookup
theorem idPointsto_agree (γ : GName) (loc : Loc) (i1 i2 : Nat) (π1 π2 : DFrac) :
    ⊢@{IProp GF} idPointsto γ loc i1 π1 -∗ idPointsto γ loc i2 π2 -∗ ⌜i1 = i2⌝ := by
  unfold idPointsto
  iintro H1 H2
  icases ghost_map_elem_agree $$ [$H1 $H2] with %Heq
  ipureintro; exact Heq
theorem idMap_insert (γ : GName) (n : H Nat) (loc : Loc) (id : Nat) (Hfresh : get? n loc = none) :
    ⊢@{IProp GF} idMap γ n ==∗ idMap γ (insert n loc id) ∗ idPointsto γ loc id (.own 1) := by
  unfold idMap idPointsto; iapply (ghost_map_insert loc id Hfresh)
theorem idMap_update (γ : GName) (n : H Nat) (loc : Loc) (id id' : Nat) :
    ⊢@{IProp GF} idMap γ n -∗ idPointsto γ loc id (.own 1) ==∗
      idMap γ (insert n loc id') ∗ idPointsto γ loc id' (.own 1) := by
  unfold idMap idPointsto; iapply (ghost_map_update id')
theorem idMap_delete (γ : GName) (n : H Nat) (loc : Loc) (id : Nat) :
    ⊢@{IProp GF} idMap γ n -∗ idPointsto γ loc id (.own 1) ==∗ idMap γ (delete n loc) := by
  unfold idMap idPointsto; iapply (ghost_map_delete loc id)
instance (γ : GName) (n : H Nat) : Timeless (PROP := IProp GF) (idMap γ n) := by
  unfold idMap; infer_instance
instance (γ : GName) (loc : Loc) (id : Nat) (π : DFrac) : Timeless (PROP := IProp GF) (idPointsto γ loc id π) := by
  unfold idPointsto; infer_instance
instance (γ : GName) (loc : Loc) (id : Nat) : Persistent (PROP := IProp GF) (idPointsto γ loc id .discard) := by
  unfold idPointsto; infer_instance
theorem idPointsto_exclusive (γ : GName) (loc : Loc) (i1 i2 : Nat) :
    ⊢@{IProp GF} idPointsto γ loc i1 (.own 1) -∗ idPointsto γ loc i2 (.own 1) -∗ ⌜False⌝ := by
  unfold idPointsto
  iintro H1 H2
  icombine H1 H2 gives ⟨%Hv, %_⟩
  ipureintro
  exact absurd (DFrac.valid_own_op Hv) (by have : (1 : Qp).val = 1 := rfl; grind)

-- fractional structure of id fragments ⇒ `icases H with ⟨H1, H2⟩` splits a full fragment into halves
instance idPointsto_fractional (γ : GName) (loc : Loc) (id : Nat) :
    Fractional (PROP := IProp GF) (fun q => idPointsto γ loc id (.own q)) :=
  @ghost_map_elem_fractional GF Loc Nat H _ _ γ loc id
instance idPointsto_asFractional (γ : GName) (loc : Loc) (id : Nat) (q : Qp) :
    AsFractional (PROP := IProp GF) (idPointsto γ loc id (.own q))
      (fun q => idPointsto γ loc id (.own q)) q where
  as_fractional := .rfl
  as_fractional_fractional := idPointsto_fractional γ loc id
instance idPointsto_intoSep (γ : GName) (loc : Loc) (id : Nat) :
    Iris.ProofMode.IntoSep (idPointsto γ loc id (.own 1) : IProp GF)
      (idPointsto γ loc id (.own (Qp.half 1))) (idPointsto γ loc id (.own (Qp.half 1))) where
  into_sep := by
    have h := (@ghost_map_elem_fractional GF Loc Nat H _ _ γ loc id).fractional (Qp.half 1) (Qp.half 1)
    rw [Qp.half_add_half] at h; exact h.1
instance idPointsto_fromSep (γ : GName) (loc : Loc) (id : Nat) :
    Iris.ProofMode.FromSep (idPointsto γ loc id (.own 1) : IProp GF)
      (idPointsto γ loc id (.own (Qp.half 1))) (idPointsto γ loc id (.own (Qp.half 1))) where
  from_sep := by
    have h := (@ghost_map_elem_fractional GF Loc Nat H _ _ γ loc id).fractional (Qp.half 1) (Qp.half 1)
    rw [Qp.half_add_half] at h; exact h.2

def arrMap (γ : GName) (m : H (Int × (Option Loc))) : IProp GF := γ ↪●MAP m
def arrPointsto (γ : GName) (loc : Loc) (v : Int) (sl : Option Loc) (π : DFrac) : IProp GF := γ ↪◯MAP[loc]{π} (v, sl)


-- ===== arr map  (Loc → Int × Option Loc) =====
theorem arrMap_alloc : ⊢@{IProp GF} |==> ∃ γ, arrMap γ (∅ : H (Int × Option Loc)) := by
  unfold arrMap; iapply ghost_map_alloc_empty
theorem arrMap_lookup (γ : GName) (m : H (Int × Option Loc)) (loc : Loc) (v : Int) (sl : Option Loc) (π : DFrac) :
    ⊢@{IProp GF} arrMap γ m -∗ arrPointsto γ loc v sl π -∗ ⌜get? m loc = some (v, sl)⌝ := by
  unfold arrMap arrPointsto; iapply ghost_map_lookup
theorem arrPointsto_agree (γ : GName) (loc : Loc) (v1 v2 : Int) (sl1 sl2 : Option Loc) (π1 π2 : DFrac) :
    ⊢@{IProp GF} arrPointsto γ loc v1 sl1 π1 -∗ arrPointsto γ loc v2 sl2 π2 -∗ ⌜v1 = v2 ∧ sl1 = sl2⌝ := by
  unfold arrPointsto
  iintro H1 H2
  icases ghost_map_elem_agree $$ [$H1 $H2] with %Heq
  ipureintro; injection Heq with h1 h2; exact ⟨h1, h2⟩
theorem arrMap_insert (γ : GName) (m : H (Int × Option Loc)) (loc : Loc) (v : Int) (sl : Option Loc)
    (Hfresh : get? m loc = none) :
    ⊢@{IProp GF} arrMap γ m ==∗ arrMap γ (insert m loc (v, sl)) ∗ arrPointsto γ loc v sl (.own 1) := by
  unfold arrMap arrPointsto; iapply (ghost_map_insert loc (v, sl) Hfresh)
theorem arrMap_update (γ : GName) (m : H (Int × Option Loc)) (loc : Loc) (v : Int) (sl : Option Loc) (w : Int) (sl' : Option Loc) :
    ⊢@{IProp GF} arrMap γ m -∗ arrPointsto γ loc v sl (.own 1) ==∗
      arrMap γ (insert m loc (w, sl')) ∗ arrPointsto γ loc w sl' (.own 1) := by
  unfold arrMap arrPointsto; iapply (ghost_map_update (w, sl'))
theorem arrMap_delete (γ : GName) (m : H (Int × Option Loc)) (loc : Loc) (v : Int) (sl : Option Loc) :
    ⊢@{IProp GF} arrMap γ m -∗ arrPointsto γ loc v sl (.own 1) ==∗ arrMap γ (delete m loc) := by
  unfold arrMap arrPointsto; iapply (ghost_map_delete loc (v, sl))
instance (γ : GName) (m : H (Int × Option Loc)) : Timeless (PROP := IProp GF) (arrMap γ m) := by
  unfold arrMap; infer_instance
instance (γ : GName) (loc : Loc) (v : Int) (sl : Option Loc) (π : DFrac) : Timeless (PROP := IProp GF) (arrPointsto γ loc v sl π) := by
  unfold arrPointsto; infer_instance
theorem arrPointsto_exclusive (γ : GName) (loc : Loc) (v1 v2 : Int) (sl1 sl2 : Option Loc) :
    ⊢@{IProp GF} arrPointsto γ loc v1 sl1 (.own 1) -∗ arrPointsto γ loc v2 sl2 (.own 1) -∗ ⌜False⌝ := by
  unfold arrPointsto
  iintro H1 H2
  icombine H1 H2 gives ⟨%Hv, %_⟩
  ipureintro
  exact absurd (DFrac.valid_own_op Hv) (by have : (1 : Qp).val = 1 := rfl; grind)
instance arrPointsto_fractional (γ : GName) (loc : Loc) (v : Int) (sl : Option Loc) :
    Fractional (PROP := IProp GF) (fun q => arrPointsto γ loc v sl (.own q)) :=
  @ghost_map_elem_fractional GF Loc (Int × Option Loc) H _ _ γ loc (v, sl)
instance arrPointsto_asFractional (γ : GName) (loc : Loc) (v : Int) (sl : Option Loc) (q : Qp) :
    AsFractional (PROP := IProp GF) (arrPointsto γ loc v sl (.own q))
      (fun q => arrPointsto γ loc v sl (.own q)) q where
  as_fractional := .rfl
  as_fractional_fractional := arrPointsto_fractional γ loc v sl
-- explicit half-split so `icases H with ⟨H1, H2⟩` / `isplit` fire directly
instance arrPointsto_intoSep (γ : GName) (loc : Loc) (v : Int) (sl : Option Loc) :
    Iris.ProofMode.IntoSep (arrPointsto γ loc v sl (.own 1) : IProp GF)
      (arrPointsto γ loc v sl (.own (Qp.half 1))) (arrPointsto γ loc v sl (.own (Qp.half 1))) where
  into_sep := by
    have h := (@ghost_map_elem_fractional GF Loc (Int × Option Loc) H _ _ γ loc (v, sl)).fractional (Qp.half 1) (Qp.half 1)
    rw [Qp.half_add_half] at h; exact h.1
instance arrPointsto_fromSep (γ : GName) (loc : Loc) (v : Int) (sl : Option Loc) :
    Iris.ProofMode.FromSep (arrPointsto γ loc v sl (.own 1) : IProp GF)
      (arrPointsto γ loc v sl (.own (Qp.half 1))) (arrPointsto γ loc v sl (.own (Qp.half 1))) where
  from_sep := by
    have h := (@ghost_map_elem_fractional GF Loc (Int × Option Loc) H _ _ γ loc (v, sl)).fractional (Qp.half 1) (Qp.half 1)
    rw [Qp.half_add_half] at h; exact h.2

def arrRoot (γ : GName) (v : Val) (γL γI γH : GName) : IProp GF :=
  iOwn (E := ArrG.rootG) γ (toAgree (⟨(v, γL, γI, γH)⟩ : LeibnizO _))

def histAuth  (γ : GName) (m : H' Val) : IProp GF := γ ↪●MAP m
def histView  (γ : GName) (node : Val) (id : Nat) : IProp GF := γ ↪◯MAP[id]{.discard} node

-- ===== root binding (Agree, immutable ⇒ no update/insert/delete) =====
theorem arrRoot_alloc (v : Val) (γL γI γH : GName) :
    ⊢@{IProp GF} |==> ∃ γ, arrRoot γ v γL γI γH := by
  unfold arrRoot; iapply (iOwn_alloc (E := ArrG.rootG) _ Agree.toAgree_valid)
theorem arrRoot_agree (γ : GName) (v v' : Val) (γL γI γH γL' γI' γH' : GName) :
    ⊢@{IProp GF} arrRoot γ v γL γI γH -∗ arrRoot γ v' γL' γI' γH' -∗
      ⌜v = v' ∧ γL = γL' ∧ γI = γI' ∧ γH = γH'⌝ := by
  unfold arrRoot
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  have h := congrArg LeibnizO.car (toAgree_op_valid_iff_eq.mp Hvalid)
  injection h with h1 h; injection h with h2 h; injection h with h3 h4
  exact ⟨h1, h2, h3, h4⟩
instance (γ : GName) (v : Val) (γL γI γH : GName) : Persistent (PROP := IProp GF) (arrRoot γ v γL γI γH) := by
  unfold arrRoot; infer_instance
instance (γ : GName) (v : Val) (γL γI γH : GName) : Timeless (PROP := IProp GF) (arrRoot γ v γL γI γH) := by
  unfold arrRoot; infer_instance

-- ===== history map  (Nat → Val) : views are always persistent (discarded) =====
theorem histAuth_alloc : ⊢@{IProp GF} |==> ∃ γ, histAuth γ (∅ : H' Val) := by
  unfold histAuth; iapply ghost_map_alloc_empty
theorem histAuth_lookup (γ : GName) (h : H' Val) (node : Val) (id : Nat) :
    ⊢@{IProp GF} histAuth γ h -∗ histView γ node id -∗ ⌜get? h id = some node⌝ := by
  unfold histAuth histView; iapply ghost_map_lookup
theorem histView_agree (γ : GName) (id : Nat) (node1 node2 : Val) :
    ⊢@{IProp GF} histView γ node1 id -∗ histView γ node2 id -∗ ⌜node1 = node2⌝ := by
  unfold histView
  iintro H1 H2
  icases ghost_map_elem_agree $$ [$H1 $H2] with %Heq
  ipureintro; exact Heq

theorem histAuth_insert (γ : GName) (h : H' Val) (node : Val) (id : Nat) (Hfresh : get? h id = none) :
    ⊢@{IProp GF} histAuth γ h ==∗ histAuth γ (insert h id node) ∗ histView γ node id := by
  unfold histAuth histView; iapply (ghost_map_insert_persist id node Hfresh)
instance (γ : GName) (h : H' Val) : Timeless (PROP := IProp GF) (histAuth γ h) := by
  unfold histAuth; infer_instance
instance (γ : GName) (node : Val) (id : Nat) : Persistent (PROP := IProp GF) (histView γ node id) := by
  unfold histView; infer_instance
instance (γ : GName) (node : Val) (id : Nat) : Timeless (PROP := IProp GF) (histView γ node id) := by
  unfold histView; infer_instance

end RA

variable {GF : BundledGFunctors} [LawfulFiniteMap H' Nat] [LawfulFiniteMap H Loc]
variable [HeapLangGS hlc GF] [SpinLockG GF] [ArrG GF H H']

def isArrLockINV_pre (Ψ : GName → GName → Val → IProp GF) (γL γI : GName) (node : Val) : IProp GF := iprop%
  ∃ (lk : Val) (γlock : GName) (ptr : Loc), ⌜node = hl_val((&lk, #ptr))⌝ ∗
    SpinLock.isLock γlock lk iprop(
      ∃ (x : Int) (nlk : Val),
        (∃ id, idPointsto γI ptr id (DFrac.own (Qp.half 1))) ∗ -- do we really need this?
        ((arrPointsto γL ptr x none (DFrac.own (Qp.half 1))) ∗
          ptr ↦ hl_val((#x, none()))
          ∨
        (∃ loc: Loc, Ψ γL γI hl_val((&nlk, #loc)) ∗
          ptr ↦ hl_val((#x, some((&nlk, #loc)))) ∗
          arrPointsto γL ptr x (some loc) (DFrac.own (Qp.half 1)))))


-- TODO understand why this is so long
instance isArrLockINV_pre.contractive : OFE.Contractive (isArrLockINV_pre (GF := GF)) := by
  rw [contractive_internalEq (PROP := IProp GF)]
  iintro %Ψ₁ %Ψ₂ #HEQ
  iapply fun_extI; iintro %γL
  iapply fun_extI; iintro %γI
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
    · exact ⟨fun _ _ _ h => wandIff_ne.ne (exists_ne (fun (x : Int) => exists_ne (fun (nlk : Val) => BI.sep_ne.ne .rfl (BI.or_ne.ne .rfl (exists_ne (fun (loc : Loc) => BI.sep_ne.ne (h γL γI hl_val((&nlk, #loc))) .rfl)))))) .rfl⟩
    · iapply equiv_wandIff; exact .rfl
  · iintro ⟨%lk, %γlock, %ptr, %Hn, H⟩
    iexists lk, γlock, ptr
    isplit
    · ipureintro; exact Hn
    iapply SpinLock.is_lock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne .rfl (exists_ne (fun (x : Int) => exists_ne (fun (nlk : Val) => BI.sep_ne.ne .rfl (BI.or_ne.ne .rfl (exists_ne (fun (loc : Loc) => BI.sep_ne.ne (h γL γI hl_val((&nlk, #loc))) .rfl))))))⟩
    · iapply equiv_wandIff; exact .rfl


def isArrLockINV : GName → GName → Val → IProp GF := fixpoint isArrLockINV_pre

theorem isArrLockINV_unfold (γL γI : GName) (v : Val) :
    isArrLockINV γL γI v ⊣⊢@{IProp GF} isArrLockINV_pre isArrLockINV γL γI v :=
    equiv_iff.mp (fixpoint_unfold
      (f := Function.toContractiveHom (isArrLockINV_pre (GF := GF) (H := H) (H' := H'))) γL γI v)

instance isArrLockINV.persistent (γL γI : GName) (v : Val) : Persistent (PROP := IProp GF) (isArrLockINV γL γI v) := by
  have _hHH : (H, H') = (H, H') := rfl   -- pull phantom H, H' into local scope so `Contractive` can synthesize
  have Hunf : isArrLockINV γL γI v ⊣⊢ isArrLockINV_pre isArrLockINV γL γI v :=
    equiv_iff.mp (fixpoint_unfold
      (f := Function.toContractiveHom (isArrLockINV_pre (GF := GF) (H := H) (H' := H'))) γL γI v)
  have Hp : Persistent (PROP := IProp GF) (isArrLockINV_pre isArrLockINV γL γI v) := by
    unfold isArrLockINV_pre; infer_instance
  exact ⟨Hunf.mp.trans (Hp.persistent.trans (persistently_mono Hunf.mpr))⟩

def contents (γL γI : GName) (v : Val) (ar : List (Nat × Int)) : IProp GF :=
  match ar with
  | [] => iprop(True)
  | [(id, x)] => iprop%
    ∃ (lk : Val) (ptr : Loc),
      ⌜v = hl_val((&lk, #ptr))⌝ ∗
      arrPointsto γL ptr x none (DFrac.own (Qp.half 1)) ∗
      idPointsto γI ptr id (DFrac.own (Qp.half 1))
  | (id, x) :: cs => iprop%
    ∃ (lk : Val) (ptr : Loc) (nlk : Val) (next : Loc),
      ⌜v = hl_val((&lk, #ptr))⌝ ∗
      arrPointsto γL ptr x (some next) (DFrac.own (Qp.half 1)) ∗
      idPointsto γI ptr id (DFrac.own (Qp.half 1)) ∗
      contents γL γI hl_val((&nlk, #next)) cs


def isArrINV (γL γI γA γH: GName) : IProp GF := iprop%
  ∃ (v : Val) (m : H (Int × (Option Loc))) (n : H Nat) (h : H' Val),
    arrMap γL m ∗ idMap γI n ∗ arrRoot γA v γL γI γH ∗ histAuth γH h ∗
  ⌜ (∀ k, dom m k ↔ dom n k) ∧
    (∀ p₁ p₂ i, get? n p₁ = some i → get? n p₂ = some i → p₁ = p₂) ∧
    (∀ ptr id, get? n ptr = some id → ∃ lk, get? h id = some hl_val((&lk, #ptr))) ⌝
-- Requires a lot of work


-- CORE PREDICATES
def arrN : Namespace := ndot nroot "arr"
def Arr.isArr (γ : GName) : IProp GF := iprop%
  ∃ (v : Val) (γL γI γH : GName),
    arrRoot γ v γL γI γH ∗
    isArrLockINV γL γI v ∗
    inv arrN (isArrINV γL γI γ γH)
-- AI: Prove the persistent
instance Arr.isArr_persistent (γ : GName) : Persistent (PROP := IProp GF) (Arr.isArr γ) := by
  unfold Arr.isArr; infer_instance


def Arr.isContents (γ : GName) (σ : Arr) : IProp GF := iprop%
  ∃ (v : Val) (γL γI γH : GName),
    arrRoot γ v γL γI γH ∗
    contents γL γI v σ.cells


def Arr.idRecord (γ : GName) (node : Val) (id : Nat) : IProp GF := iprop%
  ∃ (v: Val) (γL γI γH : GName),
    arrRoot γ v γL γI γH ∗ histView γH node id

instance Arr.idRecord_persistent (γ : GName) (n : Val) (id : Nat) :
  Persistent (PROP := IProp GF) (Arr.idRecord γ n id) := by
  unfold Arr.idRecord; infer_instance -- (was wrongly `unfold Arr.isContents`)


theorem Impl.init_spec (x : Int) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.init #x)
    ⦃ v, RET v; ∃ γ id, Arr.isArr γ ∗ Arr.isContents γ (Arr.init x) ∗ Arr.idRecord γ v id ⦄ := by
  iintro %Φ - H
  unfold Impl.init
  wp_pures
  wp_bind &newlock _
  iapply newlock_spec
  iintro %lk %γ Hlk
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %ptr Hptr
  iapply fupd_wp
  imod arrMap_alloc with ⟨%γL, HAm⟩
  imod idMap_alloc with ⟨%γI, HIm⟩
  imod histAuth_alloc with ⟨%γH, HAh⟩
  imod arrMap_insert γL (∅ : H (Int × Option Loc)) ptr x none $$ HAm with ⟨HAm', Hpt⟩
  sorry
  -- icases Hpt with ⟨Hpt, Hpt'⟩
  imod idMap_insert γI (∅ : H Nat) ptr 0 $$ HIm with ⟨HIm', Hpt2⟩
  sorry
  imod histAuth_insert γH (∅ : H' Val) hl_val((&lk, #ptr)) 0 $$ HAh with ⟨HAh', Hpt3⟩
  sorry
  icases Hpt with ⟨Hpt, Hpt'⟩
  icases Hpt2 with ⟨Hpt2, Hpt2'⟩

  imod arrRoot_alloc hl_val((&lk, #ptr)) γL γI γH with ⟨%γ, #Hroot⟩
  -- allocate new ghost state
  --
  imodintro
  wp_pures
  imodintro
  iapply H
  iexists γ, 0
  rw [Arr.init]
  rw [Arr.isContents]
  unfold contents
  isplitr
  unfold Arr.isArr
  iexists hl_val((&lk, #ptr)), γL, γI, γH
  iframe Hroot
  unfold isArrLockINV
  sorry
  isplitr
  iexists hl_val((&lk, #ptr)), γL, γI, γH
  iframe Hroot
  iexists lk, ptr
  isplitr
  itrivial
  sorry
  sorry

theorem Impl.insert_spec (γ : GName) (id : Nat) (node : Val) (x : Int) :
  ⊢@{IProp GF}
    Arr.isArr γ -∗ Arr.idRecord γ node id -∗
      ⟪ ∀ σ, Arr.isContents γ σ ∗ ⌜Arr.wellFormed σ⌝ ⟫
        hl(&Impl.insert &node #x) @ arrN
      ⟪ ∃ nid, Arr.isContents γ (σ.insert id x) | ret, RET ret; Arr.idRecord γ ret nid ⟫ := by
  iintro Harr Hnode %Φ HAU
  unfold Impl.insert
  wp_pures

  sorry

theorem Impl.remove_spec (γ : GName) (id : Nat) (node : Val) :
  ⊢@{IProp GF}
    Arr.isArr γ -∗ Arr.idRecord γ node id -∗
      ⟪ ∀ σ, Arr.isContents γ σ ∗ ⌜Arr.wellFormed σ⌝  ⟫
        hl(&Impl.remove &node) @ arrN
      ⟪ Arr.isContents γ (σ.remove id) | RET hl_val(#()) ⟫ := by sorry

end Specs

end Iris.Examples.HeapLang
