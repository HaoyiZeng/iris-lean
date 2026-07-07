module

public import Iris.BI.Lib.Atomic
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.ProgramLogic.Atomic

@[expose] public section

namespace Iris.Tests
open Iris

section AtomicUpdateNotation

set_option linter.unusedVariables false

variable (PROP : Type _) [BI PROP] [BIFUpdate PROP]
variable (Eo Ei : CoPset)
variable (α : Nat → PROP)
variable (β Φ : Nat → Bool → PROP)
variable (P : PROP)

/--
info: AU ⟪ ∃ x, α x ⟫ @ Eo, Ei ⟪ ∀ y, β x y, COMM Φ x y ⟫ : PROP
-/
#guard_msgs in
#check (AU ⟪ ∃ x, α x ⟫ @ Eo, Ei ⟪ ∀ y, β x y, COMM Φ x y ⟫ : PROP)

end AtomicUpdateNotation

section AtomicUpdateTactics

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele}
variable (E : CoPset)
variable (α : TA → PROP)
variable (β Φ : TA → TB → PROP)

example (x : TA) :
    α x -∗ (∀ y, β x y -∗ Φ x y) -∗
    atomicUpdate E ∅ α β Φ := by
  iintro Hα HΦ
  iAuIntro
  iAaccIntro with Hα
  · iintro Hα
    imodintro
    isplitl [Hα]
    · iexact Hα
    · iexact HΦ
  · iintro %y Hβ
    imodintro
    iapply HΦ $$ %y Hβ

end AtomicUpdateTactics

section AtomicWpNotation

set_option linter.unusedVariables false

open ProgramLogic Language.Notation Std

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [IrisGS_gen hlc Expr GF]
variable (e : Expr) (E : CoPset)
variable (α : Nat → IProp GF)
variable (β : Nat → Bool → IProp GF)
variable (POST : Nat → Bool → Val → IProp GF)
variable (f : Nat → Bool → Val → Val)

/--
info: ⟪∀ x, α x⟫e @ E⟪∃ y, β x y | z, RET f x y z; POST x y z⟫ : IProp GF
-/
#guard_msgs in
#check (⟪ ∀ x, α x ⟫ e @ E ⟪ ∃ y, β x y | z, RET f x y z; POST x y z ⟫ : IProp GF)

end AtomicWpNotation

section CounterExample

open BI ProgramLogic Language.Notation Std
open Iris.HeapLang

variable {hlc : outParam HasLC}
variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

def inc : Val := hl_val(
  rec inc l :=
    let n := !l;
    if snd(cmpXchg(l, n, n + #1))
      then n
      else inc l)

abbrev incTA : Tele := Tele.cons (λ _ : Int => Tele.nil)
abbrev incTB : Tele := Tele.cons (λ _ : Bool => Tele.nil)
abbrev incTP : Tele := Tele.cons (λ _ : Bool => Tele.nil)

abbrev incPre (l : Loc) : incTA → IProp GF
  | ⟨n, _⟩ => l ↦ some hl_val(#n)

abbrev incPost (l : Loc) : incTA → incTB → IProp GF
  | ⟨n, _⟩, ⟨b, _⟩ => iprop(l ↦ some hl_val(#(n + (1 : Int))) ∗ ⌜b = true⌝)

abbrev incPriv : incTA → incTB → incTP → Option (IProp GF)
  | _, _, ⟨b, _⟩ => some iprop(⌜b = true⌝)

def incRet : incTA → incTB → incTP → Val
  | ⟨n, _⟩, _, _ => hl_val(#n)

private theorem wandM_some_elim {PROP : Type _} [BI PROP] (P Q : PROP) :
    P -∗ wandM (some P) Q -∗ Q := by
  simp [wandM]
  iintro HP Hwand
  iapply Hwand $$ HP

theorem inc_spec (l : Loc) :
  ⊢ ⟪ ∀ n, l ↦ some hl_val(#(n : Int)) ⟫
      hl(&inc v(#l)) @ ∅
    ⟪ ∃ b, l ↦ some hl_val(#(n + 1: Int)) ∗ ⌜b = true⌝
      | z, RET hl_val(#(n : Int)); ⌜z = true⌝ ⟫ := by
  change ⊢ atomicWP hl(&inc v(#l)) ∅ (incPre (GF := GF) l) (incPost (GF := GF) l)
    (incPriv (GF := GF)) incRet
  unfold atomicWP inc
  rw [LawfulSet.diff_empty]
  iintro %Φ HAU
  iloeb as IH
  wp_rec
  wp_bind !_
  iapply wp_atomic (s := Stuckness.NotStuck) (E1 := ⊤) (E2 := ∅)
  ihave Hacc := aupd_acc _ _ _ ⊤ ∅ ⊤ LawfulSet.subset_refl $$ HAU
  imod Hacc with ⟨%x, Hl, Hclose⟩
  rcases x with ⟨n, _⟩
  imodintro
  iapply wp_load $$ Hl
  iintro !> Hl
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ Hl with HAU
  imodintro
  wp_pures
  wp_bind cmpXchg(_,_,_)
  iapply wp_atomic (s := Stuckness.NotStuck) (E1 := ⊤) (E2 := ∅)
  ihave Hacc := aupd_acc _ _ _ ⊤ ∅ ⊤ LawfulSet.subset_refl $$ HAU
  imod Hacc with ⟨%x, Hl, Hclose⟩
  rcases x with ⟨w, _⟩
  imodintro
  by_cases Heq : hl_val(#n) = hl_val(#w)
  · simp only [Val.lit.injEq, BaseLit.int.injEq] at Heq
    subst Heq
    iapply wp_wand $$ [Hl]
    · iapply wp_cmpXchg_true rfl rfl $$ Hl <;>
        simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
    iintro %v Hres
    icases Hres with ⟨%Hv, Hl⟩
    subst Hv
    icases Hclose with ⟨-, Hcommit⟩
    ihave Hβ : iprop(l ↦ some hl_val(#(n + (1 : Int))) ∗ ⌜true = true⌝) $$ [Hl]
    · isplitl [Hl]
      · iexact Hl
      · ipureintro; rfl
    imod Hcommit $$ %⟨true, PUnit.unit⟩ Hβ with HΦ
    imodintro
    wp_pures
    imodintro
    iclear IH
    ihave HΦforall : biTforall (fun z : incTP =>
        wandM (incPriv (GF := GF) ⟨n, PUnit.unit⟩ ⟨true, PUnit.unit⟩ z)
          (Φ (incRet ⟨n, PUnit.unit⟩ ⟨true, PUnit.unit⟩ z))) $$ [HΦ]
    · rw [Tele.app_bind, Tele.app_bind]
      exact .rfl
    ihave HΦ' := HΦforall $$ %⟨true, PUnit.unit⟩
    ihave HΦ'' : wandM (PROP := IProp GF) (some iprop(⌜true = true⌝)) (Φ hl_val(#n)) $$ [HΦ']
    · unfold incPriv incRet
      exact .rfl
    iapply wandM_some_elim (P := iprop(⌜true = true⌝)) (Q := Φ hl_val(#n))
    · ipureintro; rfl
    · iexact HΦ''
  · iapply wp_wand $$ [Hl]
    · iapply wp_cmpXchg_fail rfl rfl $$ Hl
      · trivial
      · simp
        intro hw
        apply Heq
        subst hw
        rfl
    iintro %v Hres
    icases Hres with ⟨%Hv, Hl⟩
    subst Hv
    icases Hclose with ⟨Habort, -⟩
    imod Habort $$ Hl with HAU
    imodintro
    wp_pure
    wp_pure
    iapply IH $$ HAU


end CounterExample

end Iris.Tests
