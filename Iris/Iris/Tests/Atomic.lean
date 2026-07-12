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
  iauintro
  iaaccintro with Hα
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
info: ⟪∀ x, α x⟫ e @ E ⟪∃ y, β x y | z, RET f x y z; POST x y z⟫ : IProp GF
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

theorem inc_spec (l : Loc) :
  ⊢ ⟪ ∀ n, l ↦ some hl_val(#(n : Int)) ⟫
      hl(&inc v(#l)) @ ∅
    ⟪ l ↦ some hl_val(#(n + 1: Int)) | RET hl_val(#(n : Int)) ⟫ := by

  iintro %Φ HAU
  iloeb as IH
  wp_rec
  wp_bind !_
  -- For some reason i have to apply wp_atomic manually
  iapply wp_atomic (E2 := ∅)

  -- one-step open+destruct (peeling `IntoExists` instances give an ordinary `n`,
  -- no packed `Sigma`/`PUnit`); then reduce the applied telescope functions so
  -- `Hl : l ↦ some hl_val(#n)`
  iauopen HAU with ⟨%n, Hl, Hclose⟩

  -- remove the fancy upd introced by wp_atomic
  imodintro
  iapply wp_load $$ Hl
  iintro !> Hl
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ Hl with HAU
  imodintro
  wp_pures
  wp_bind cmpXchg(_,_,_)
  -- again, for some reason i have to apply wp_atomic manually
  iapply wp_atomic (E2 := ∅)

  iauopen HAU with ⟨%w, Hl, Hclose⟩

  imodintro
  by_cases Heq : (w = n)
  · iclear IH
    rw [Heq]

    -- because wp_cmpXchg_true cosumes a later points-to
    iapply wp_wand $$ [Hl]
    · iapply wp_cmpXchg_true rfl rfl $$ Hl <;>
        simp [Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]
    · iintro %v ⟨%Hv, Hl⟩
      icases Hclose with ⟨-, Hcommit⟩

      imod Hcommit $$ Hl with Hcommit
      imodintro
      rw [Hv]
      wp_pures
      imodintro
      itrivial
  · iapply wp_wand $$ [Hl]
    · iapply wp_cmpXchg_fail rfl rfl $$ Hl
      · trivial
      · simp_all
    · iintro %v ⟨%Hv, Hl⟩
      icases Hclose with ⟨Habort, -⟩
      imod Habort $$ Hl with HAU
      imodintro
      rw [Hv]
      wp_pures
      iapply IH $$ HAU


end CounterExample

end Iris.Tests
