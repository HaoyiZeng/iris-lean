module

public import Iris.BI.Lib.AtomicF

@[expose] public section
namespace Iris.AtomicFExamples

open Iris Iris.OFE BI

/-!
# Atomic updates without telescopes -- worked examples

Each example writes its binders as ordinary `∃`/`∀` inside the accessor. The
arity never reaches the type level: `atomicUpdateOf` takes `PROP → PROP`, and the
fixpoint runs over `Unit → PROP` whatever the binders are.
-/

section
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

/-! ## Zero binders -/

section Zero
variable (α P₀ : PROP)

def accZero (P : PROP) : PROP :=
  iprop(|={⊤,∅}=> α ∗ ((α ={∅,⊤}=∗ P) ∧ (α ={∅,⊤}=∗ P₀)))

example [AccMono (accZero α P₀)] : PROP := atomicUpdateOf (accZero α P₀)
end Zero

/-! ## One binder -/

section One
variable {A : Type} (α : A → PROP) (β : A → PROP)

def accOne (P : PROP) : PROP :=
  iprop(|={⊤,∅}=> ∃ x, α x ∗ ((α x ={∅,⊤}=∗ P) ∧ (α x ={∅,⊤}=∗ β x)))

example [AccMono (accOne α β)] : PROP := atomicUpdateOf (accOne α β)
end One

/-! ## Three binders on the left, two on the right

Nothing about the definition changed -- only what is written inside the
accessor. Compare with the telescoped encoding, where this needs
`Tele.cons (λ _ => Tele.cons (λ _ => Tele.cons (λ _ => Tele.nil)))` and three
layers of `Tele.app`/`ULift.up`. -/

section Many
variable {A B C D E : Type}
variable (α : A → B → C → PROP) (β Φ : A → B → C → D → E → PROP)

def accMany (P : PROP) : PROP :=
  iprop(|={⊤,∅}=> ∃ x y z, α x y z ∗
    ((α x y z ={∅,⊤}=∗ P) ∧ (∀ u v, β x y z u v ={∅,⊤}=∗ Φ x y z u v)))

example [AccMono (accMany α β Φ)] : PROP := atomicUpdateOf (accMany α β Φ)
end Many

/-! ## The multi-shot cycle

This is the property a CAS-retry loop depends on, and the reason an atomic update
is a *greatest* fixpoint: open it, decline to commit, and get the update back so
the next iteration can try again.

The proof is the same shape the HeapLang spin-lock proof uses -- open with `imod`,
choose the abort branch of the `∧` with `icases … ⟨Habort, -⟩`, fire it -- except
that no `itele_reduce` is needed, because there is no telescope to reduce. -/

section MultiShot
variable {A B C : Type} (α : A → B → PROP) (β Φ : A → B → C → PROP)

def accTwo (P : PROP) : PROP :=
  iprop(|={⊤,∅}=> ∃ x y, α x y ∗
    ((α x y ={∅,⊤}=∗ P) ∧ (∀ z, β x y z ={∅,⊤}=∗ Φ x y z)))

/-- The one obligation per accessor: monotonicity in the abort slot.

Only the two lines naming the binders depend on their number. -/
instance instAccTwo [hne : NonExpansive (accTwo α β Φ)] : AccMono (accTwo α β Φ) where
  toNonExpansive := hne
  mono := by
    intro P Q
    unfold accTwo
    iintro #HPQ H
    imod H with ⟨%x, %y, Hα, Hclose⟩
    imodintro
    iexists x, y
    isplitl [Hα]
    · iexact Hα
    · isplit
      · iintro Hα'
        icases Hclose with ⟨Habort, -⟩
        imod Habort $$ Hα' with HP
        imodintro
        iapply HPQ $$ HP
      · iapply and_elim_r $$ Hclose

variable [AccMono (accTwo α β Φ)]

/-- Unfolding, with the accessor's body written out.

`auOf_unfold` already gives this -- the statement below is definitionally its
type -- but spelling the body out is what lets `imod` see the `fupd` without
unfolding a `def` first. In real use the notation that builds the accessor would
emit this alongside it. -/
theorem accTwo_unfold : atomicUpdateOf (accTwo α β Φ) ⊢
    iprop(|={⊤,∅}=> ∃ x y, α x y ∗
      ((α x y ={∅,⊤}=∗ atomicUpdateOf (accTwo α β Φ)) ∧
       (∀ z, β x y z ={∅,⊤}=∗ Φ x y z))) :=
  auOf_unfold (accTwo α β Φ)

/-- Abort, and recover the update. -/
example : atomicUpdateOf (accTwo α β Φ) ⊢
    iprop(|={⊤,⊤}=> atomicUpdateOf (accTwo α β Φ)) := by
  iintro HAU
  ihave H := accTwo_unfold α β Φ $$ HAU
  imod H with ⟨%x, %y, Hα, Hclose⟩
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ Hα with HAU'
  imodintro
  iexact HAU'

end MultiShot

/-! ## Committing

The other branch of the same `∧` is reached with `icases … ⟨-, Hcommit⟩`, exactly
as the HeapLang spin-lock proof does (`SpinRwLock.lean:885`). The branch itself is
an ordinary conjunction of wands here -- there is no telescope in the way -- so
nothing about committing is specific to this encoding.
-/



end

end Iris.AtomicFExamples
