module

public import Lean

/-! # Shared delaboration helpers for `auUncurry` chains

Adapted from Aeneas (`backends/lean/Aeneas/Std/Delab.lean`).  The Aeneas
version walks `Aeneas.Std.uncurry`; this iris-lean copy walks the packed
atomic-update head symbol `Iris.auUncurry`.  Constructor-pattern support from the
Aeneas helper is intentionally omitted: the packed AU notation only emits and
accepts plain identifier binders.
-/

@[expose] public section

namespace Iris

/-- Stable head symbol for packed atomic-update binders.  Kept separate from
`Std.uncurry` so notation and delaboration can recognize AU binder packing. -/
@[reducible] def auUncurry {α β : Type _} {PROP : Type _} (p : α → β → PROP) : α × β → PROP :=
  fun (x, y) => p x y

@[simp] theorem auUncurry_pair {α β : Type _} {PROP : Type _}
    (x : α) (y : β) (p : α → β → PROP) : auUncurry p (x, y) = p x y := rfl

@[defeq] theorem auUncurry_eq {α β : Type _} {PROP : Type _}
    (x : α × β) (p : α → β → PROP) : auUncurry p x = p x.fst x.snd := rfl

end Iris

public meta section

open Lean PrettyPrinter Delaborator SubExpr

namespace Iris.Delab

/-- A binder entry collected while traversing lambda/`auUncurry` layers:
- `FVarId` — the fvar introduced by the lambda
- `Name` — the binder name
- `Pos` — the SubExpr position of the enclosing lambda (for hover annotation) -/
abbrev BinderEntry := FVarId × Name × Pos

/-- Enter leading `fun` binders, collecting a `BinderEntry` for each.

The packed AU empty-binder marker is `fun (_ : Unit) => body`; if the `Unit`
binder is unused we skip it so the delaborator prints the empty binder list back. -/
partial def enterLams (acc : Array BinderEntry)
    (k : Array BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n ty b _ =>
    if ty.isConstOf ``Unit && !b.hasLooseBVars then
      withBindingBody' n pure fun _ => enterLams acc k
    else
      let pos ← getPos
      withBindingBody' n pure fun fv =>
        enterLams (acc.push (fv.fvarId!, n, pos)) k
  | _ => k acc

/-- Enter `fun` binders and chained `Iris.auUncurry`s, flattening all leaves.

Example: on `auUncurry (fun a => auUncurry (fun b c => body))`, collects
`[a, b, c]` and leaves the reader at `body`. -/
partial def enterUncurryChain (acc : Array BinderEntry)
    (k : Array BinderEntry → DelabM α) : DelabM α :=
  enterLams acc fun acc' => do
    if (← getExpr).isAppOfArity ``_root_.Iris.auUncurry 4 then
      withAppArg <| enterUncurryChain acc' k
    else
      k acc'

/-- Build tuple syntax `(p₀, p₁, ...)` from an array of pattern terms. -/
def buildTupleTerm (pats : Array Term) : DelabM Term := do
  let head := pats[0]!
  let tail := pats.extract 1 pats.size
  `(($head, $tail,*))

/-- Build a pattern for each binder.  This simplified iris-lean copy only handles
plain binders; if a future notation emits constructor or tuple patterns, the caller
can fall back to Lean's default delaborator. -/
partial def delabBinders (binders : List BinderEntry) (k : DelabM α) :
    DelabM (Array Term × α) := do
  match binders with
  | [] => return (#[], ← k)
  | (fv, name, binderPos) :: rest =>
    let stx : Term := annotatePos binderPos ⟨Lean.mkIdent name⟩
    addTermInfo binderPos stx.raw (.fvar fv) (isBinder := true)
    let (restPats, a) ← delabBinders rest k
    return (#[stx] ++ restPats, a)

/-- Enter an `auUncurry` chain, collect binder patterns via `delabBinders`, and
wrap them in a single tuple term. Returns `(tupleTerm, k_result)`.

Expects the reader to be positioned at the function argument of `auUncurry`
(i.e. after `withAppArg`). -/
def delabUncurryAsTuple (k : DelabM α) : DelabM (Term × α) :=
  enterUncurryChain #[] fun binders => do
    let (pats, a) ← delabBinders binders.toList k
    return (← buildTupleTerm pats, a)

def prodMk? (e : Expr) : Option (Expr × Expr) := do
  let e := e.consumeMData
  guard (e.isAppOfArity ``Prod.mk 4)
  let args := e.getAppArgs
  some (args[2]!, args[3]!)

/-- Delaborate an applied packed AU family:
`auUncurry f (a, b)` is displayed as `f a b`.

This is separate from the atomic-update delaborators: it also cleans proof-mode
hypotheses whose type contains an already-applied packed family. -/
@[delab app.Iris.auUncurry]
def delabAuUncurryApp : Delab := do
  let e ← getExpr
  /- At least the four arguments of `auUncurry` plus the tuple.  Anything beyond
  that is over-application -- `auUncurry f (a, b) y` -- which happens whenever a
  packed family is a *function*, as the commit side of an update is.  Those
  extra arguments are carried through rather than dropped. -/
  guard (e.isAppOfArity' ``_root_.Iris.auUncurry 5 || e.getAppNumArgs > 5)
  guard (e.isAppOf ``_root_.Iris.auUncurry)
  let args := e.getAppArgs
  let some (a, b) := prodMk? args[4]! | failure
  let extra := args[5:].toArray
  let reduced ← Core.betaReduce (mkAppN (mkAppN args[3]! #[a, b]) extra)
  withTheReader SubExpr (fun ctx => { ctx with expr := reduced }) delab

end Iris.Delab

end
