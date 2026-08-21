module

public import Iris.BI.Lib.Atomic

@[expose] public section

namespace Iris.Tests
open Iris BI

/-! Packed atomic-update regression tests replacing the old telescope scratch file. -/

section PackedExistentials

variable {PROP : Type _} [BI PROP]
variable (Ψ : Nat × Bool → PROP)

/-- Product existentials are peeled binder-by-binder by the packed `IntoExists` instance. -/
example : iprop(∃ p : Nat × Bool, Ψ p) ⊢ True := by
  iintro H
  icases H with ⟨%n, %b, HΨ⟩
  itrivial

end PackedExistentials

section PackedAtomic

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable (Eo Ei : CoPset)
variable (α : Nat → Bool → PROP)
variable (β Φ : Nat → Bool → Unit → PROP)

/-- Multi-binder `AU` notation elaborates without telescopes. -/
example :
    (AU ⟪ ∃ n b, α n b ⟫ @ Eo, Ei ⟪ ∀ r, β n b r, COMM Φ n b r ⟫ : PROP) ⊢
    (AU ⟪ ∃ n b, α n b ⟫ @ Eo, Ei ⟪ ∀ r, β n b r, COMM Φ n b r ⟫ : PROP) := by
  iintro H
  iexact H

end PackedAtomic

end Iris.Tests
