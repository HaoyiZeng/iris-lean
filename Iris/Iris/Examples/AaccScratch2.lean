module

public import Iris.BI.Lib.Atomic
public import Iris.HeapLang.Lib.IInv
public import Iris.ProgramLogic.Atomic

@[expose] public section
namespace Iris.Scratch
open Iris BI

inductive St where | free | write
deriving DecidableEq

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]

/-- Reproduction of the `nodeSlotShared_write_acquire_spec` goal shape:
the client AU has `TA = nil` (`Slot`), the RwLock AU has `TA = cons St`.
Closed entirely by `aacc_aupd_commit` + `iaaccintro'` — no manual
`simp only [atomicAcc]; iexists; isplitl; isplit` boilerplate. -/
example (Slot Guard P Ψ : IProp GF) (Lock : St → IProp GF)
    (Hu : Slot ⊣⊢ iprop(∃ s, Lock s ∗ (match s with | .free => P | .write => emp))) :
    (AU ⟪ Slot ⟫ @ ⊤, ∅ ⟪ Slot ∗ Guard ∗ P, COMM Ψ ⟫ : IProp GF) ⊢
    (AU ⟪ ∃ s, Lock s ⟫ @ ⊤, ∅
       ⟪ Lock St.write ∗ Guard ∗ ⌜s = St.free⌝, COMM Ψ ⟫ : IProp GF) := by
  iintro HAU
  iauintro
  iapply aacc_aupd_commit _ _ _ ⊤ ⊤ ∅ ∅ _ _ _ _ Std.LawfulSet.subset_refl $$ HAU
  iintro %_ HSlot
  itele_reduce
  icases Hu.mp $$ HSlot with ⟨%s, HLock, Hrest⟩
  iaaccintro' with HLock
  · -- abort: rebuild `Slot`, hand the client AU back unchanged
    iintro HLock
    imodintro
    isplitl [HLock Hrest]
    · iapply Hu.mpr; iexists s; iframe
    · iintro HAU; imodintro; iexact HAU
  · -- commit: `s = free`, so `Hrest : P`; rebuild `Slot` in state `write`
    iintro %y Hpost
    itele_reduce
    icases Hpost with ⟨HLock, HGuard, %hs⟩
    subst hs
    imodintro
    iexists PUnit.unit
    isplitl [HLock HGuard Hrest]
    · isplitl [HLock]
      · iapply Hu.mpr; iexists St.write; iframe
      · iframe
    · iintro HΨ; imodintro; iexact HΨ

end Iris.Scratch
