module

public import Iris.Algebra.DFrac
public import Iris.Algebra.Agree
meta import Iris.Std.RocqPorting

/-!
# Local (exposed) copy of the DFrac-Agree camera helpers

The upstream `Iris.Algebra.Lib.DFracAgree` module is a `module` without an
`@[expose] public section` (unlike its siblings `Frac`/`DFrac`/`Agree`/`MonoNat`),
so none of its declarations are exported and it cannot be consumed from another
module. Rather than modify that upstream file, this local file re-provides — in a
distinct `FracAgree` namespace — exactly the subset used by `AtomicLock`:
the camera `DFracAgreeR`, the constructors `mk`/`Frac.mk`, and the lemmas
`mk_op`/`op_valid`/`op_valid_L`/`update₂`. The proofs only use the (exposed)
`DFrac`/`Agree` cameras.
-/

namespace Iris
open OFE CMRA DFrac

@[expose] public section

namespace FracAgree

/-- The DFrac-Agree camera: a discardable fraction paired with an agreement. -/
abbrev DFracAgreeR (A : Type _) [OFE A] := DFrac × Agree A

/-- Constructor from a `DFrac` and a value. -/
def mk [OFE A] (d : DFrac) (a : A) : DFracAgreeR A := (d, toAgree a)

variable {A : Type _} [OFE A]

instance mk_ne {d : DFrac} : NonExpansive (mk d : A → DFracAgreeR A) where
  ne _ _ _ h := ⟨.rfl, NonExpansive.ne (f := toAgree) h⟩

instance mk_exclusive {a : A} : Exclusive (mk (.own (1 : Qp)) a) := one_exclusive_left

instance mk_discrete {d : DFrac} {a : A} [DiscreteE a] : DiscreteE (mk d a) :=
  ⟨fun h => ⟨is_discrete.discrete h.1, Agree.toAgree.is_discrete.discrete h.2⟩⟩

theorem mk_op {d₁ d₂ : DFrac} {a : A} : mk (d₁ • d₂) a ≡ mk d₁ a • mk d₂ a :=
  ⟨Equiv.rfl, Agree.idemp.symm⟩

theorem op_valid {d₁ d₂ : DFrac} {a₁ a₂ : A} :
    ✓ (mk d₁ a₁ • mk d₂ a₂) ↔ ✓ (d₁ • d₂) ∧ a₁ ≡ a₂ := by
  simp only [Valid, Prod.Valid, Prod.op, CMRA.op, mk]
  exact and_congr_right fun _ => Agree.toAgree_op_valid_iff_equiv

theorem op_valid_L [Leibniz A] {d₁ d₂ : DFrac} {a₁ a₂ : A} :
    ✓ (mk d₁ a₁ • mk d₂ a₂) ↔ ✓ (d₁ • d₂) ∧ a₁ = a₂ := by
  rw [op_valid]
  exact and_congr_right fun _ => Leibniz.leibniz

theorem update₂ {d₁ d₂ : DFrac} {a₁ a₂ a' : A} (hd : d₁ • d₂ = .own 1) :
    mk d₁ a₁ • mk d₂ a₂ ~~> mk d₁ a' • mk d₂ a' := by
  have : mk d₁ a₁ • mk d₂ a₂ ≡ (own (1 : Qp), toAgree a₁ • toAgree a₂) :=
    ⟨hd ▸ Equiv.rfl, Equiv.rfl⟩
  calc
    _ ≡ (own (1 : Qp), toAgree a₁ • toAgree a₂) := this
    _ ~~> mk d₁ a' • mk d₂ a' :=
      @Update.exclusive _ _ _ _ one_exclusive_left
        (op_valid.mpr ⟨hd ▸ valid_own_one, .rfl⟩)

/-! ## Frac variants (full ownership fraction, no discard) -/

namespace Frac

def mk [OFE A] (q : Qp) (a : A) : DFracAgreeR A := FracAgree.mk (.own q) a

variable {A : Type _} [OFE A]

theorem mk_op {q₁ q₂ : Qp} {a : A} : mk (q₁ + q₂) a ≡ mk q₁ a • mk q₂ a :=
  FracAgree.mk_op (d₁ := .own q₁) (d₂ := .own q₂)

theorem op_valid_L [Leibniz A] {q₁ q₂ : Qp} {a₁ a₂ : A} :
    ✓ (mk q₁ a₁ • mk q₂ a₂) ↔ (q₁ + q₂).val ≤ 1 ∧ a₁ = a₂ := FracAgree.op_valid_L

theorem update₂ {q₁ q₂ : Qp} {a₁ a₂ a' : A} (hq : q₁ + q₂ = 1) :
    mk q₁ a₁ • mk q₂ a₂ ~~> mk q₁ a' • mk q₂ a' :=
  FracAgree.update₂ (show own q₁ • own q₂ = .own 1 from congrArg _ hq)

end Frac

end FracAgree

end

end Iris
