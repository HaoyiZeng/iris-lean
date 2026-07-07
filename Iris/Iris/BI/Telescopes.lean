module

public import Iris.BI.DerivedLawsLater
public import Iris.Std.Telescopes
public import Init.NotationExtra

@[expose] public section

namespace Iris
open BI OFE Lean

/-- Telescopic existential quantifier over packed telescope arguments. -/
@[rocq_alias bi_texist]
def biTexist [BI PROP] {TT : Tele.{u}} (Ψ : TT → PROP) : PROP :=
  Tele.fold (TT := TT) (X := PROP) (Y := PROP)
    (λ Φ => iprop(∃ x, Φ x)) id (Tele.bind (TT := TT) (U := PROP) Ψ)

/-- Telescopic universal quantifier over packed telescope arguments. -/
@[rocq_alias bi_tforall]
def biTforall [BI PROP] {TT : Tele.{u}} (Ψ : TT → PROP) : PROP :=
  Tele.fold (TT := TT) (X := PROP) (Y := PROP)
    (λ Φ => iprop(∀ x, Φ x)) id (Tele.bind (TT := TT) (U := PROP) Ψ)

syntax "∀.. " ident ", " term : term
macro_rules
  | `(∀.. $x:ident, $P:term) =>
      `(biTforall (fun $x => iprop($P)))

syntax "∃.. " ident ", " term : term
macro_rules
  | `(∃.. $x:ident, $P:term) =>
      `(biTexist (fun $x => iprop($P)))

delab_rule biTforall
  | `($_ fun $x:ident => $Ψ) => do
      ``(iprop(∀.. $x:ident, $(← unpackIprop Ψ)))

delab_rule biTexist
  | `($_ fun $x:ident => $Ψ) => do
      ``(iprop(∃.. $x:ident, $(← unpackIprop Ψ)))

@[rocq_alias bi_tforall_forall]
theorem biTforall_forall [BI PROP] {TT : Tele} (Ψ : TT → PROP) :
    biTforall Ψ ⊣⊢ iprop(∀ x, Ψ x) := by
  induction TT with
  | nil =>
      refine ⟨?_, forall_elim PUnit.unit⟩
      refine forall_intro λ x => ?_
      cases x
      exact .rfl
  | cons b ih =>
      refine ⟨?_, ?_⟩
      · refine forall_intro λ x => ?_
        cases x with
        | mk x xs =>
            exact (forall_elim x).trans <| (ih x (λ xs => Ψ ⟨x, xs⟩)).1.trans <|
              forall_elim xs
      · refine forall_intro λ x => ?_
        refine (forall_intro λ xs => forall_elim ⟨x, xs⟩).trans ?_
        exact (ih x (λ xs => Ψ ⟨x, xs⟩)).2

@[rocq_alias bi_texist_exist]
theorem biTexist_exist [BI PROP] {TT : Tele} (Ψ : TT → PROP) :
    biTexist Ψ ⊣⊢ iprop(∃ x, Ψ x) := by
  induction TT with
  | nil =>
      refine ⟨exists_intro PUnit.unit, ?_⟩
      refine exists_elim λ x => ?_
      cases x
      exact .rfl
  | cons b ih =>
      refine ⟨?_, ?_⟩
      · refine exists_elim λ x => ?_
        refine (ih x (λ xs => Ψ ⟨x, xs⟩)).1.trans ?_
        exact exists_elim λ xs => exists_intro (Ψ := Ψ) ⟨x, xs⟩
      · refine exists_elim λ x => ?_
        cases x with
        | mk x xs =>
            exact ((exists_intro xs).trans (ih x (λ xs => Ψ ⟨x, xs⟩)).2).trans
              (exists_intro (Ψ := λ x => biTexist (λ xs => Ψ ⟨x, xs⟩)) x)

@[rocq_alias bi_tforall_ne]
instance biTforall_ne [BI PROP] {TT : Tele} :
    NonExpansive (biTforall (PROP := PROP) (TT := TT)) where
  ne {n} {Ψ1} {Ψ2} h := by
    calc
      biTforall Ψ1 ≡{n}≡ iprop(∀ x, Ψ1 x) := (equiv_iff.mpr (biTforall_forall Ψ1)).dist
      _ ≡{n}≡ iprop(∀ x, Ψ2 x) := forall_ne h
      _ ≡{n}≡ biTforall Ψ2 := (equiv_iff.mpr (biTforall_forall Ψ2)).dist.symm

@[rocq_alias bi_texist_ne]
instance biTexist_ne [BI PROP] {TT : Tele} :
    NonExpansive (biTexist (PROP := PROP) (TT := TT)) where
  ne {n} {Ψ1} {Ψ2} h := by
    calc
      biTexist Ψ1 ≡{n}≡ iprop(∃ x, Ψ1 x) := (equiv_iff.mpr (biTexist_exist Ψ1)).dist
      _ ≡{n}≡ iprop(∃ x, Ψ2 x) := exists_ne h
      _ ≡{n}≡ biTexist Ψ2 := (equiv_iff.mpr (biTexist_exist Ψ2)).dist.symm

@[rocq_alias bi_tforall_proper]
theorem biTforall_proper [BI PROP] {TT : Tele} {Ψ1 Ψ2 : TT → PROP}
    (h : ∀ x, Ψ1 x ⊣⊢ Ψ2 x) : biTforall Ψ1 ⊣⊢ biTforall Ψ2 := by
  exact (biTforall_forall Ψ1).trans <| (forall_congr h).trans <| (biTforall_forall Ψ2).symm

@[rocq_alias bi_texist_proper]
theorem biTexist_proper [BI PROP] {TT : Tele} {Ψ1 Ψ2 : TT → PROP}
    (h : ∀ x, Ψ1 x ⊣⊢ Ψ2 x) : biTexist Ψ1 ⊣⊢ biTexist Ψ2 := by
  exact (biTexist_exist Ψ1).trans <| (exists_congr h).trans <| (biTexist_exist Ψ2).symm

@[rocq_alias bi_tforall_absorbing]
instance biTforall_absorbing [BI PROP] {TT : Tele} (Ψ : TT → PROP)
    [∀ x, Absorbing (Ψ x)] : Absorbing (biTforall Ψ) where
  absorbing :=
    (absorbingly_mono (biTforall_forall Ψ).1).trans <|
      absorbing.trans (biTforall_forall Ψ).2

@[rocq_alias bi_tforall_persistent]
instance biTforall_persistent [BI PROP] [BIPersistentlyForall PROP] {TT : Tele}
    (Ψ : TT → PROP) [∀ x, Persistent (Ψ x)] : Persistent (biTforall Ψ) where
  persistent :=
    (biTforall_forall Ψ).1.trans <|
      persistent.trans <| persistently_mono (biTforall_forall Ψ).2

@[rocq_alias bi_texist_affine]
instance biTexist_affine [BI PROP] {TT : Tele} (Ψ : TT → PROP)
    [∀ x, Affine (Ψ x)] : Affine (biTexist Ψ) where
  affine := (biTexist_exist Ψ).1.trans affine

@[rocq_alias bi_texist_absorbing]
instance biTexist_absorbing [BI PROP] {TT : Tele} (Ψ : TT → PROP)
    [∀ x, Absorbing (Ψ x)] : Absorbing (biTexist Ψ) where
  absorbing :=
    (absorbingly_mono (biTexist_exist Ψ).1).trans <|
      absorbing.trans (biTexist_exist Ψ).2

@[rocq_alias bi_texist_persistent]
instance biTexist_persistent [BI PROP] {TT : Tele} (Ψ : TT → PROP)
    [∀ x, Persistent (Ψ x)] : Persistent (biTexist Ψ) where
  persistent :=
    (biTexist_exist Ψ).1.trans <|
      persistent.trans <| persistently_mono (biTexist_exist Ψ).2

@[rocq_alias bi_tforall_timeless]
instance biTforall_timeless [BI PROP] {TT : Tele} (Ψ : TT → PROP)
    [∀ x, Timeless (Ψ x)] : Timeless (biTforall Ψ) where
  timeless :=
    (later_mono (biTforall_forall Ψ).1).trans <|
      Timeless.timeless.trans <| except0_mono (biTforall_forall Ψ).2

@[rocq_alias bi_texist_timeless]
instance biTexist_timeless [BI PROP] {TT : Tele} (Ψ : TT → PROP)
    [∀ x, Timeless (Ψ x)] : Timeless (biTexist Ψ) where
  timeless :=
    (later_mono (biTexist_exist Ψ).1).trans <|
      Timeless.timeless.trans <| except0_mono (biTexist_exist Ψ).2

end Iris
