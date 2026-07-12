module

public import Iris.Examples.ArrayCopy
public import Iris.HeapLang.Lib.Par

@[expose] public section
namespace Iris.Examples.HeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Std PartialMap Spawn SpinLock

section Clients

variable {H' : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H' Nat]
variable [HeapLangGS hlc GF] [SpinLockG GF] [ArrG GF H'] [SpawnG GF]

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
        {{ v, ∃ (γ : GName) (σ : Arr), Arr.isContents γ σ }} := by
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

end Clients

end Iris.Examples.HeapLang
