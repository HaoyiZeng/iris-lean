module
public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates
public import Iris.Algebra.LocalUpdates

@[expose] public section

/-!
# `ULift` instances for the Iris algebra hierarchy

Lean 4 has no universe cumulativity, so a `Type 0` CMRA is *not* a `Type 1`
CMRA. Since `BundledGFunctors := GType → GFunctor` uses a *single* `GFunctor`
type, every slot of a bundle shares one universe — so raising `iProp` to
`Type 1` forces every existing `Type 0` resource (`DFrac`, `Qp`, the invariant
machinery's `CoPsetDisjL`, …) through `ULift`.

This file measures that cost: it transports the whole hierarchy
`OFE → IsCOFE → CMRA → UCMRA` along `ULift.up`/`ULift.down`.

(In Rocq none of this is needed: `Type@{0} ⊆ Type@{1}` by cumulativity.)
-/

namespace Iris.Algebra

open Iris Iris.Algebra CMRA OFE

universe u v

variable {α : Type u}

/-! ## OFE -/

instance instOFEULift [OFE α] : OFE (ULift.{v} α) where
  Equiv x y := OFE.Equiv x.down y.down
  Dist n x y := OFE.Dist n x.down y.down
  dist_eqv := OFE.dist_eqv
  equiv_dist := OFE.equiv_dist
  dist_lt := OFE.Dist.lt

@[simp] theorem uLift_dist [OFE α] {n} {x y : ULift.{v} α} :
    x ≡{n}≡ y ↔ x.down ≡{n}≡ y.down := .rfl

@[simp] theorem uLift_equiv [OFE α] {x y : ULift.{v} α} :
    x ≡ y ↔ x.down ≡ y.down := .rfl

/-- Push a chain down through the lift. -/
def downChain [OFE α] (c : Chain (ULift.{v} α)) : Chain α where
  chain n := (c n).down
  cauchy h := c.cauchy h

/-! ## COFE -/

instance instIsCOFEULift [COFE α] : IsCOFE (ULift.{v} α) where
  compl c := ⟨COFE.compl (downChain c)⟩
  conv_compl := COFE.conv_compl (c := downChain _)

/-! ## CMRA -/

instance instCMRAULift [CMRA α] : CMRA (ULift.{v} α) where
  pcore x := (CMRA.pcore x.down).map ULift.up
  op x y := ⟨CMRA.op x.down y.down⟩
  ValidN n x := CMRA.ValidN n x.down
  Valid x := CMRA.Valid x.down
  op_ne := ⟨fun _ _ _ h => CMRA.op_ne.ne h⟩
  pcore_ne := by
    intro n x y cx h he
    rcases hx : CMRA.pcore x.down with _ | c
    · simp [hx] at he
    · simp only [hx, Option.map_some] at he
      obtain ⟨cy, hcy, hd⟩ := CMRA.pcore_ne (n := n) h hx
      obtain rfl := Option.some.inj he
      exact ⟨⟨cy⟩, by simp [hcy], hd⟩
  validN_ne h hv := CMRA.validN_ne h hv
  valid_iff_validN := CMRA.valid_iff_validN
  validN_succ := CMRA.validN_succ
  validN_op_left := CMRA.validN_op_left
  assoc := CMRA.assoc
  comm := CMRA.comm
  pcore_op_left := by
    intro x cx h
    rcases hx : CMRA.pcore x.down with _ | c
    · simp [hx] at h
    · simp only [hx, Option.map_some] at h
      obtain rfl := Option.some.inj h
      exact CMRA.pcore_op_left hx
  pcore_idem := by
    intro x cx h
    rcases hx : CMRA.pcore x.down with _ | c
    · simp [hx] at h
    · simp only [hx, Option.map_some] at h
      obtain rfl := Option.some.inj h
      have := CMRA.pcore_idem hx
      rcases hc : CMRA.pcore c with _ | c'
      · simp [hc] at this
      · simp only [hc, Option.map_some]
        simp only [hc] at this
        exact this
  pcore_op_mono := by
    intro x cx h y
    rcases hx : CMRA.pcore x.down with _ | c
    · simp [hx] at h
    · simp only [hx, Option.map_some] at h
      obtain rfl := Option.some.inj h
      obtain ⟨cy, hcy⟩ := CMRA.pcore_op_mono hx y.down
      refine ⟨⟨cy⟩, ?_⟩
      rcases hxy : CMRA.pcore (CMRA.op x.down y.down) with _ | z
      · simp [hxy] at hcy
      · simp only [hxy, Option.map_some]
        simp only [hxy] at hcy
        exact hcy
  extend := by
    intro n x y₁ y₂ hv he
    obtain ⟨z₁, z₂, h, h1, h2⟩ := CMRA.extend hv he
    exact ⟨⟨z₁⟩, ⟨z₂⟩, h, h1, h2⟩

/-! ## UCMRA -/

instance instUCMRAULift [UCMRA α] : UCMRA (ULift.{v} α) where
  unit := ⟨UCMRA.unit⟩
  unit_valid := UCMRA.unit_valid
  unit_left_id := UCMRA.unit_left_id
  pcore_unit := by
    have := UCMRA.pcore_unit (α := α)
    rcases h : CMRA.pcore (UCMRA.unit : α) with _ | c
    · simp [h] at this
    · simp only [h] at this
      show (Option.map ULift.up (CMRA.pcore (UCMRA.unit : α))) ≡ _
      simp only [h, Option.map_some]
      exact this


/-! ## Bridging lemmas

These are what make the lift usable in practice: every operation on `ULift α`
reduces definitionally to the operation on `α`, so ported proofs need only these
three rewrites rather than a rewrite per lemma. -/

section Bridge
variable [CMRA α]

@[simp] theorem uLift_op (a b : α) :
    CMRA.op (⟨a⟩ : ULift.{v} α) ⟨b⟩ = (⟨CMRA.op a b⟩ : ULift.{v} α) := rfl
@[simp] theorem uLift_validN {n} {x : ULift.{v} α} : ✓{n} x ↔ ✓{n} x.down := .rfl
@[simp] theorem uLift_valid {x : ULift.{v} α} : ✓ x ↔ ✓ x.down := .rfl

@[simp] theorem uLift_opM (a : α) (mz : Option α) :
    (⟨a⟩ : ULift.{v} α) •? (mz.map ULift.up) = ⟨a •? mz⟩ := by
  cases mz <;> rfl

theorem uLift_eqv [OFE α] {a b : α} (h : a ≡ b) : (⟨a⟩ : ULift.{v} α) ≡ ⟨b⟩ := h
theorem uLift_distn [OFE α] {n} {a b : α} (h : a ≡{n}≡ b) : (⟨a⟩ : ULift.{v} α) ≡{n}≡ ⟨b⟩ := h

/-- Frame-preserving updates transport along the lift. -/
theorem UpdateP.uLift {a : α} {P : α → Prop} (h : UpdateP a P) :
    UpdateP (⟨a⟩ : ULift.{v} α) (fun y => P y.down) := by
  intro n mz hv
  obtain ⟨b, hPb, hvb⟩ := h n (mz.map ULift.down) (by cases mz <;> exact hv)
  exact ⟨⟨b⟩, hPb, by cases mz <;> exact hvb⟩

theorem Update.uLift {a b : α} (h : Update a b) :
    Update (⟨a⟩ : ULift.{v} α) (⟨b⟩ : ULift.{v} α) := by
  intro n mz hv
  cases mz with
  | none => exact h n none hv
  | some z => exact h n (some z.down) hv

end Bridge

/-- Local updates transport along the lift. -/
theorem LocalUpdate.uLift [CMRA α] {x y : α × α} (h : LocalUpdate x y) :
    LocalUpdate ((⟨x.1⟩, ⟨x.2⟩) : ULift.{v} α × ULift.{v} α) (⟨y.1⟩, ⟨y.2⟩) := by
  intro n mz hv he
  cases mz with
  | none => exact h n none hv he
  | some z => exact h n (some z.down) hv he

/-- Core-identity elements stay core-identity under the lift. -/
instance instCoreIdULift [CMRA α] (a : α) [CMRA.CoreId a] :
    CMRA.CoreId (⟨a⟩ : ULift.{v} α) where
  core_id := by
    have h := CMRA.CoreId.core_id (x := a)
    show (CMRA.pcore a).map ULift.up ≡ _
    rcases hp : CMRA.pcore a with _ | c
    · rw [hp] at h; exact h.elim
    · rw [hp] at h; simpa using h

/-- Units stay units under the lift. -/
instance instIsUnitULift [CMRA α] (e : α) [IsUnit e] :
    IsUnit (⟨e⟩ : ULift.{v} α) where
  unit_valid := IsUnit.unit_valid (ε := e)
  unit_left_id := IsUnit.unit_left_id (ε := e)
  pcore_unit := by
    have h := IsUnit.pcore_unit (ε := e)
    show (CMRA.pcore e).map ULift.up ≡ _
    rcases hp : CMRA.pcore e with _ | c
    · rw [hp] at h; exact h.elim
    · rw [hp] at h; simpa using h

instance instLeibnizULift [OFE α] [OFE.Leibniz α] : OFE.Leibniz (ULift.{v} α) where
  eq_of_eqv h := congrArg ULift.up (OFE.Leibniz.eq_of_eqv (α := α) h)

/-! ## Discreteness transports -/

instance instOFEDiscreteULift [OFE α] [OFE.Discrete α] : OFE.Discrete (ULift.{v} α) where
  discrete_0 h := OFE.Discrete.discrete_0 (α := α) h

instance instCMRADiscreteULift [CMRA α] [CMRA.Discrete α] : CMRA.Discrete (ULift.{v} α) where
  discrete_valid h := CMRA.Discrete.discrete_valid (α := α) h

/-! ## Convenience for porting

The coercion makes the `ULift.up` at introduction points implicit, so client
code can keep writing `iOwn γ a` with `a` at its original type even though the
ghost state now stores `ULift a`. -/

instance instCoeTailULift : CoeTail α (ULift.{v} α) := ⟨ULift.up⟩

end Iris.Algebra
