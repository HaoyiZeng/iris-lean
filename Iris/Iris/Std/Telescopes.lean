module

@[expose] public section

namespace Iris

universe u v w

/-- A telescope of dependent binders. -/
inductive Tele : Type (u + 1) where
  | nil : Tele
  | cons {X : Type u} (binder : X → Tele) : Tele

namespace Tele

/-- Packed arguments for a telescope. -/
def Arg : Tele → Type u
  | nil => PUnit
  | cons b => Sigma λ x => Arg (b x)

instance : CoeSort Tele (Type u) where
  coe := Arg

/-- Curried functions over a telescope. -/
abbrev Fun : Tele.{u} → Type v → Type (max u v)
  | nil, U => ULift U
  | cons b, U => ∀ x, Fun (b x) U

/-- Fold over a curried telescope function. -/
def fold {X : Type v} {Y : Type w} {TT : Tele.{u}}
    (step : {A : Type u} → (A → Y) → Y) (base : X → Y) : Fun TT X → Y :=
  match TT with
  | nil => λ x => base x.down
  | cons b => λ f => step (λ x => fold (TT := b x) step base (f x))

/-- Apply a curried telescope function to packed telescope arguments. -/
def app {TT : Tele} {U : Type _} : Fun TT U → TT → U :=
  match TT with
  | nil => λ f _ => f.down
  | cons b => λ f a =>
      match a with
      | ⟨x, xs⟩ => app (TT := b x) (f x) xs

/-- Convert a function on packed telescope arguments into curried form. -/
def bind {TT : Tele} {U : Type _} : (TT → U) → Fun TT U :=
  match TT with
  | nil => λ f => ULift.up (f PUnit.unit)
  | cons b => λ f x => bind (TT := b x) (λ xs => f ⟨x, xs⟩)

theorem app_bind {TT : Tele} {U : Type _} (f : TT → U) (x : TT) :
    app (bind f) x = f x := by
  induction TT with
  | nil =>
      cases x
      rfl
  | cons b ih =>
      cases x with
      | mk x xs =>
          simp [app, bind, ih]

/-- Map below a telescope function. -/
def map {TT : Tele} {T : Type _} {U : Type _} (F : T → U) : Fun TT T → Fun TT U :=
  match TT with
  | nil => λ t => ULift.up (F t.down)
  | cons b => λ t x => map (TT := b x) F (t x)

theorem map_app {TT : Tele} {T : Type _} {U : Type _}
    (F : T → U) (t : Fun TT T) (x : TT) :
    app (map F t) x = F (app t x) := by
  induction TT with
  | nil =>
      cases x
      rfl
  | cons b ih =>
      cases x with
      | mk x xs =>
          exact ih x (t x) xs

/-- Identity telescope function. -/
def funId {TT : Tele} : Fun TT TT :=
  bind id

theorem funId_eq {TT : Tele} (x : TT) :
    app funId x = x := by
  simp [funId, app_bind]

/-- Composition of telescope functions. -/
def funComp {TT1 TT2 TT3 : Tele} :
    Fun TT2 TT3 → Fun TT1 TT2 → Fun TT1 TT3 :=
  match TT1 with
  | nil => λ f g => ULift.up (app f g.down)
  | cons b => λ f g x => funComp (TT1 := b x) f (g x)

theorem funComp_eq {TT1 TT2 TT3 : Tele}
    (f : Fun TT2 TT3) (g : Fun TT1 TT2) (x : TT1) :
    app (funComp f g) x = app f (app g x) := by
  induction TT1 with
  | nil =>
      cases x
      rfl
  | cons b ih =>
      cases x with
      | mk x xs =>
          exact ih x (g x) xs

/-- Telescope universal quantification over `Prop`. -/
def tforall {TT : Tele} (Ψ : TT → Prop) : Prop :=
  fold (λ Φ => ∀ x, Φ x) id (bind Ψ)

/-- Telescope existential quantification over `Prop`. -/
def texist {TT : Tele} (Ψ : TT → Prop) : Prop :=
  fold (λ Φ => ∃ x, Φ x) id (bind Ψ)

theorem tforall_forall {TT : Tele} (Ψ : TT → Prop) :
    tforall Ψ ↔ ∀ x, Ψ x := by
  induction TT with
  | nil =>
      constructor
      · intro h x
        cases x
        exact h
      · intro h
        exact h PUnit.unit
  | cons b ih =>
      constructor
      · intro h x
        cases x with
        | mk x xs =>
            exact (ih x (λ xs => Ψ ⟨x, xs⟩)).mp (h x) xs
      · intro h x
        exact (ih x (λ xs => Ψ ⟨x, xs⟩)).mpr (λ xs => h ⟨x, xs⟩)

theorem texist_exist {TT : Tele} (Ψ : TT → Prop) :
    texist Ψ ↔ ∃ x, Ψ x := by
  induction TT with
  | nil =>
      constructor
      · intro h
        exact ⟨PUnit.unit, h⟩
      · intro h
        rcases h with ⟨x, hx⟩
        cases x
        exact hx
  | cons b ih =>
      constructor
      · intro h
        rcases h with ⟨x, hx⟩
        rcases (ih x (λ xs => Ψ ⟨x, xs⟩)).mp hx with ⟨xs, hxs⟩
        exact ⟨⟨x, xs⟩, hxs⟩
      · intro h
        rcases h with ⟨x, hx⟩
        rcases x with ⟨x, xs⟩
        exact ⟨x, (ih x (λ xs => Ψ ⟨x, xs⟩)).mpr ⟨xs, hx⟩⟩

end Tele
end Iris
