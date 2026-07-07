module

public meta import Lean.PrettyPrinter

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
def Fun : Tele.{u} → Type v → Type (max u v)
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

syntax "[tele]" : term
syntax "[tele " ident+ "]" : term

macro_rules
  | `([tele]) => `(Tele.nil)
  | `([tele $x:ident]) => `(Tele.cons (fun $x => Tele.nil))
  | `([tele $x:ident $y:ident $ys:ident*]) =>
      `(Tele.cons (fun $x => [tele $y $ys*]))

syntax "[tele_arg]" : term
syntax "[tele_arg " term,* "]" : term

macro_rules
  | `([tele_arg]) => `(PUnit.unit)
  | `([tele_arg $x]) => `(⟨$x, PUnit.unit⟩)
  | `([tele_arg $x, $xs,*]) => `(⟨$x, [tele_arg $xs,*]⟩)

syntax "λ.. " ident+ ", " term : term

macro_rules
  | `(λ.. $x:ident, $e:term) =>
      `(Tele.app (Tele.bind (λ $x => $e)))
  | `(λ.. $x:ident $y:ident $ys:ident*, $e:term) =>
      `(Tele.app (Tele.bind (λ $x => λ.. $y $ys*, $e)))

namespace Delab

open Lean

private meta def appHeadName? : Syntax → Option Name
  | .node _ `Lean.Parser.Term.app #[.ident _ _ n _, _] => some n
  | .ident _ _ n _ => some n
  | _ => none

private meta def appArgs? : Syntax → Option (Array Syntax)
  | .node _ `Lean.Parser.Term.app #[_, .node _ `null args] => some args
  | _ => none

private meta def bindFun? (stx : Syntax) : Option ((TSyntax `ident) × Syntax) := do
  guard (appHeadName? stx == some `Tele.bind)
  let some #[funStx] := appArgs? stx | none
  let .node _ `Lean.Parser.Term.fun #[_, .node _ `Lean.Parser.Term.basicFun #[binders, _, _, body]] := funStx | none
  let .node _ `null #[x] := binders | none
  if x.isIdent then
    some (⟨x⟩, body)
  else
    none

meta partial def lambdaDot? (stx : Syntax) : Option (Array (TSyntax `ident) × TSyntax `term) := do
  guard (appHeadName? stx == some `Tele.app)
  let some #[bindStx] := appArgs? stx | none
  let (x, body) ← bindFun? bindStx
  match lambdaDot? body with
  | some (xs, body) => some (#[x] ++ xs, body)
  | none => some (#[x], ⟨body⟩)

end Delab

@[app_unexpander Tele.app]
meta def unexpandTeleApp : Lean.PrettyPrinter.Unexpander
  | stx => do
      let some (xs, body) := Delab.lambdaDot? stx | throw ()
      match body with
      | `(λ.. $y:ident $ys:ident*, $body:term) =>
          let xs := xs ++ #[y] ++ ys
          let some x := xs[0]? | throw ()
          let ys := xs.extract 1 xs.size
          `(λ.. $x:ident $ys:ident*, $body:term)
      | _ =>
          let some x := xs[0]? | throw ()
          let ys := xs.extract 1 xs.size
          `(λ.. $x:ident $ys:ident*, $body:term)

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
