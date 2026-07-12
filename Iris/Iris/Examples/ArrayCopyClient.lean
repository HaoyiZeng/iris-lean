module

public import Iris.Examples.ArrayCopy
public import Iris.HeapLang.Lib.Par

@[expose] public section
namespace Iris.Examples.HeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Std PartialMap Spawn SpinLock

section Clients

variable {H' : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H' Nat]
variable [HeapLangGS hlc GF] [ArrG GF H'] [SpawnG GF]

/-- **Sequential Hoare view of `insert`.** Because the caller privately owns `isContents σ`,
the logically-atomic `insert_spec` collapses (via `atomicWP_seq`) to an ordinary Hoare triple:
after the call the abstract list is exactly `σ.insert id x`, and we recover both node records. -/
theorem Impl.insert_hoare (γ : GName) (id : Nat) (node : Val) (x : Int) (σ : Arr) :
    ⊢@{IProp GF}
      Arr.isArr γ -∗ Arr.idRecord γ node id -∗ ⌜Arr.wellFormed σ⌝ -∗ Arr.isContents γ σ -∗
      WP hl(&Impl.insert &node #x)
        {{ v, ∃ nid, Arr.isContents γ (σ.insert id x) ∗
                Arr.idRecord γ node id ∗ Arr.idRecord γ v nid }} := by
  iintro HisArr HidRec %Hwf Hcont
  ihave Hspec := (Impl.insert_spec γ id node x) $$ HisArr HidRec
  iapply atomicWP_seq _ _ _ _ _ _ $$ Hspec
    %(fun v => iprop(∃ nid, Arr.isContents γ (σ.insert id x) ∗
        Arr.idRecord γ node id ∗ Arr.idRecord γ v nid))
    %(⟨σ, ⟨⟩⟩) [Hcont] []
  · itele_reduce
    isplitl [Hcont]
    · iexact Hcont
    · ipureintro; exact Hwf
  · itele_reduce
    iintro %nid Hβ %ret
    simp only [wandM]
    iintro ⟨Hrec1, Hrec2⟩
    iexists nid
    iframe Hβ Hrec1 Hrec2

/-- A fully sequential client: create a one-element list, then insert twice after the root.
The postcondition witnesses that the final heap represents *some* concrete abstract list. -/
def Impl.seqClient : Val := hl_val%
  λ _,
    let node := &Impl.init #0;
    let _n1 := &Impl.insert node #1;
    let _n2 := &Impl.insert node #2;
    #()

theorem Impl.seqClient_spec :
    ⊢@{IProp GF}
      WP hl(&Impl.seqClient #())
        {{ _v, ∃ (γ : GName) (σ : Arr), Arr.isContents γ σ }} := by
  unfold Impl.seqClient
  wp_pures
  wp_bind (&Impl.init _)
  iapply Impl.init_spec
  · itrivial
  inext
  iintro %r ⟨%γ, %id, #HisArr, Hcont, HidRec⟩
  wp_pures
  wp_bind (&Impl.insert _ _)
  ihave Hw1 := (Impl.insert_hoare γ id r 1 (Arr.init 0)) $$
    HisArr HidRec %(Arr.init_wellFormed 0) Hcont
  iapply wp_wand $$ Hw1
  iintro %n1 ⟨%nid1, Hcont, HidRec, -⟩
  wp_pures
  wp_bind (&Impl.insert _ _)
  ihave Hw2 := (Impl.insert_hoare γ id r 2 ((Arr.init 0).insert id 1)) $$
    HisArr HidRec %((Arr.init 0).insert_wellFormed (Arr.init_wellFormed 0) id 1) Hcont
  iapply wp_wand $$ Hw2
  iintro %n2 ⟨%nid2, Hcont, -, -⟩
  wp_pures
  iexists γ, (((Arr.init 0).insert id 1).insert id 2)
  iexact Hcont

/-- Namespace for the shared "some abstract list exists" invariant of the concurrent client. -/
def clientN : Namespace := ndot nroot "arrconc"

omit [SpawnG GF] in
/-- `contents` is timeless (built from timeless `dataPointsto` shares and pure facts). -/
theorem contents_timeless_thm (γL : GName) : ∀ (ar : List (Nat × Int)) (v : Val),
    Timeless (PROP := IProp GF) (contents γL v ar)
  | [], v => by unfold contents; infer_instance
  | [(_, _)], v => by unfold contents; infer_instance
  | (id, x) :: (sid, sx) :: cs, v => by
    haveI := contents_timeless_thm γL ((sid, sx) :: cs)
    rw [contents_cons_ne _ _ _ _ (sid, sx) cs]
    infer_instance

instance isContents_timeless (γ : GName) (σ : Arr) :
    Timeless (PROP := IProp GF) (Arr.isContents γ σ) := by
  rw [Arr.isContents]
  haveI : ∀ (γL : GName) (v : Val), Timeless (PROP := IProp GF) (contents γL v σ.cells) :=
    fun γL v => contents_timeless_thm γL σ.cells v
  infer_instance

set_option maxRecDepth 10000 in
/-- **Per-thread concurrent insert.** With a shared invariant that always holds *some*
well-formed abstract list, a thread owning a node record can insert; the logically-atomic
`insert_spec` linearizes against the invariant (opened only at the single commit point). -/
theorem Impl.insert_conc (γ : GName) (id : Nat) (node : Val) (x : Int) :
    ⊢@{IProp GF}
      Arr.isArr γ -∗
      inv clientN iprop(∃ σ, Arr.isContents γ σ ∗ ⌜Arr.wellFormed σ⌝) -∗
      Arr.idRecord γ node id -∗
      WP hl(&Impl.insert &node #x) {{ _v, True }} := by
  iintro #HisArr #Hinv HidRec
  iapply (Impl.insert_spec γ id node x) $$ HisArr HidRec
  iauintro
  have Hsub : (↑clientN : CoPset) ⊆ ((⊤ : CoPset) \ ↑arrN) := by
    have hd : (↑clientN : CoPset) ## ↑arrN :=
      ndot_ne_disjoint nroot (by decide : "arrconc" ≠ "arr")
    intro y hy
    rw [CoPset.in_diff]
    exact ⟨CoPset.mem_full, fun hya => hd y ⟨hy, hya⟩⟩
  iapply aacc_inv _ _ _ _ Hsub $$ Hinv
  iintro Hbody
  icases Hbody with ⟨%σ, Hcont, %Hwf⟩
  ihave Hα : iprop(Arr.isContents γ σ ∗ ⌜Arr.wellFormed σ⌝) $$ [Hcont]
  · iframe Hcont; ipureintro; exact Hwf
  iaaccintro' with Hα
  · -- abort: peeked but did not linearize; restore the invariant body unchanged
    iintro Hα
    icases Hα with ⟨Hcont, %Hwf'⟩
    imodintro
    isplitl [Hcont]
    · iexists σ; iframe Hcont; ipureintro; exact Hwf'
    · iframe HisArr Hinv
  · -- commit: `insert` linearized; store the updated (still well-formed) list back
    iintro %nid Hcont'
    imodintro
    isplitl [Hcont']
    · iexists (σ.insert id x); iframe Hcont'
      ipureintro; exact σ.insert_wellFormed Hwf id x
    · itele_reduce
      iintro %ret
      simp only [wandM]
      iintro -
      itrivial

/-- Two threads insert concurrently after two independently-owned nodes. The postcondition is
trivial; the *interesting* guarantee is that the shared invariant — "the heap always represents
some well-formed abstract list" — is preserved across the interleaving. -/
theorem Impl.parClient_spec (γ : GName) (id1 id2 : Nat) (node1 node2 : Val) :
    ⊢@{IProp GF}
      Arr.isArr γ -∗
      inv clientN iprop(∃ σ, Arr.isContents γ σ ∗ ⌜Arr.wellFormed σ⌝) -∗
      Arr.idRecord γ node1 id1 -∗ Arr.idRecord γ node2 id2 -∗
      WP hl(&Impl.insert &node1 #1 ‖ &Impl.insert &node2 #2) {{ _v, True }} := by
  iintro #HisArr #Hinv Hrec1 Hrec2
  iapply (Par.wp_par (fun _ => iprop(True)) (fun _ => iprop(True)) _ _) $$
    [Hrec1] [Hrec2] []
  · iapply (Impl.insert_conc γ id1 node1 1) $$ HisArr Hinv Hrec1
  · iapply (Impl.insert_conc γ id2 node2 2) $$ HisArr Hinv Hrec2
  · iintro %v1 %v2 -
    inext; itrivial

end Clients

end Iris.Examples.HeapLang
