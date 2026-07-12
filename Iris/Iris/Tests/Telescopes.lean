module

public import Iris.BI.Telescopes
public import Iris.ProofMode

@[expose] public section

namespace Iris.Tests
open Iris BI

section StdTelescopes

set_option linter.unusedVariables false

variable (P : Nat → Prop)
variable (Q : Nat → Bool → Prop)
variable (R : (n : Nat) → Fin (n + 1) → Prop)

example :
    Tele.tforall (TT := Tele.cons (λ _ : Nat => Tele.nil))
      (λ a => match a with | ⟨x, _⟩ => P x) ↔ ∀ x, P x := by
  rfl

example :
    Tele.texist (TT := Tele.cons (λ _ : Nat => Tele.nil))
      (λ a => match a with | ⟨x, _⟩ => P x) ↔ ∃ x, P x := by
  rfl

/--
info: Tele.tforall fun a =>
  match a with
  | ⟨x, xs⟩ =>
    match xs with
    | ⟨y, snd⟩ => Q x y : Prop
-/
#guard_msgs in
#check (Tele.tforall (TT := Tele.cons (λ _ : Nat => Tele.cons (λ _ : Bool => Tele.nil)))
  (λ a => match a with | ⟨x, xs⟩ => match xs with | ⟨y, _⟩ => Q x y))

/--
info: Tele.texist fun a =>
  match a with
  | ⟨x, xs⟩ =>
    match xs with
    | ⟨y, snd⟩ => R x y : Prop
-/
#guard_msgs in
#check (Tele.texist (TT := Tele.cons (λ x : Nat => Tele.cons (λ _ : Fin (x + 1) => Tele.nil)))
  (λ a => match a with | ⟨x, xs⟩ => match xs with | ⟨y, _⟩ => R x y))

example (f : Nat → Bool) (x : Nat) :
    Tele.app (Tele.bind (TT := Tele.cons (λ _ : Nat => Tele.nil))
      (λ a => match a with | ⟨x, _⟩ => f x)) ⟨x, PUnit.unit⟩ = f x := by
  exact Tele.app_bind _ _

example (f : Nat → Bool) (x : Nat) :
    Tele.app (Tele.map (TT := Tele.cons (λ _ : Nat => Tele.nil)) f
      (Tele.bind (TT := Tele.cons (λ _ : Nat => Tele.nil))
        (λ a => match a with | ⟨x, _⟩ => x)))
      ⟨x, PUnit.unit⟩ = f x := by
  rw [Tele.map_app]
  exact congrArg f (Tele.app_bind
    (TT := Tele.cons (λ _ : Nat => Tele.nil)) (U := Nat)
    (λ a => match a with | ⟨x, _⟩ => x) ⟨x, PUnit.unit⟩)

example (f : Bool → String) (g : Nat → Bool) (x : Nat) :
    Tele.app (Tele.funComp
      (TT1 := Tele.cons (λ _ : Nat => Tele.nil))
      (TT2 := Tele.cons (λ _ : Bool => Tele.nil))
      (TT3 := Tele.cons (λ _ : String => Tele.nil))
      (Tele.bind (TT := Tele.cons (λ _ : Bool => Tele.nil))
        (λ a => match a with | ⟨b, _⟩ => ⟨f b, PUnit.unit⟩))
      (Tele.bind (TT := Tele.cons (λ _ : Nat => Tele.nil))
        (λ a => match a with | ⟨n, _⟩ => ⟨g n, PUnit.unit⟩)))
      ⟨x, PUnit.unit⟩ = ⟨f (g x), PUnit.unit⟩ := by
  rw [Tele.funComp_eq]
  simp [Tele.app_bind]

end StdTelescopes

section BITelescopes

variable (PROP : Type _) [BI PROP]
variable {TT : Tele} (Φ Ψ : TT → PROP)

/-- info: iprop(∀.. x, Φ x) : PROP -/
#guard_msgs in #check (iprop(∀.. x, Φ x) : PROP)

/-- info: iprop(∃.. x, Φ x) : PROP -/
#guard_msgs in #check (iprop(∃.. x, Φ x) : PROP)

section AtomicShape

variable [BIFUpdate PROP]
variable (Eo Ei : CoPset)
variable {TA TB : Tele}
variable (α : TA → PROP)
variable (β Φ₂ : TA → TB → PROP)
variable (P : PROP)

/--
info: iprop(|={Eo, Ei}=> ∃.. x, α x ∗ (α x ={Ei, Eo}=∗ P) ∧ ∀.. y, β x y ={Ei, Eo}=∗ Φ₂ x y) : PROP
-/
#guard_msgs in
#check (iprop(|={Eo, Ei}=> ∃.. x, α x ∗ ((α x ={Ei, Eo}=∗ P) ∧
  (∀.. y, β x y ={Ei, Eo}=∗ Φ₂ x y))) : PROP)

end AtomicShape

example : biTforall Φ ⊣⊢ iprop(∀ x, Φ x) :=
  biTforall_forall Φ

example : biTexist Φ ⊣⊢ iprop(∃ x, Φ x) :=
  biTexist_exist Φ

example (h : ∀ x, Φ x ⊣⊢ Ψ x) :
    biTforall Φ ⊣⊢ biTforall Ψ :=
  biTforall_proper h

example (h : ∀ x, Φ x ⊣⊢ Ψ x) :
    biTexist Φ ⊣⊢ biTexist Ψ :=
  biTexist_proper h

example [∀ x, Absorbing (Φ x)] : Absorbing (biTforall Φ) :=
  inferInstance

example [∀ x, Affine (Φ x)] : Affine (biTexist Φ) :=
  inferInstance

example [∀ x, Persistent (Φ x)] : Persistent (biTexist Φ) :=
  inferInstance

example [∀ x, Timeless (Φ x)] : Timeless (biTforall Φ) :=
  inferInstance

example [∀ x, Timeless (Φ x)] : Timeless (biTexist Φ) :=
  inferInstance

end BITelescopes

section ProofModeTelescopes

variable {PROP : Type _} [BI PROP]
variable {TT : Tele} (Φ Ψ : TT → PROP)

example : ⊢@{PROP} biTforall (λ x => iprop(Φ x -∗ Φ x)) := by
  iintro %x H
  iexact H

example : biTforall Φ -∗ biTforall Φ := by
  iintro H %x
  iapply H $$ %x

example : biTexist Φ -∗ biTexist Φ := by
  iintro H
  icases H with ⟨%x, H⟩
  iexists x
  iexact H

example : biTforall (λ x => iprop(Φ x -∗ Ψ x)) -∗ biTforall Φ -∗ biTforall Ψ := by
  iintro Hwand HΦ %x
  iapply Hwand $$ %x
  iapply HΦ $$ %x

end ProofModeTelescopes

end Iris.Tests
