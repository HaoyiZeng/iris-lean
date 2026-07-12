/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
module

public meta import Iris.BI.Notation
public meta import Iris.ProofMode.Expr

public meta import Lean.PrettyPrinter.Delaborator

public meta section

namespace Iris.ProofMode
open Iris.BI Qq
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

/- This file generates the state display for the Iris Proof Mode. It is implemented as a
delaborator for the function `Entails'`. This function is definitionally equal to the `Entails`
predicate defined in `BI.BIBase`, its purpose is merely to serve as a marker for the delaboration
function. The hypothesis of the entailment are diplayed with a leading `□` or `∗` depending on
whether they are persistent or not.

NOTE: Hypothesis are assumed to have a specific shape so they can be displayed correctly.
In particular, hypothesis must have name annotations so they may be displayed appropiately. -/

declare_syntax_cat irisLine
syntax ident " : " term : irisLine
syntax "────────────────────────────────────────────────────────────□" : irisLine
syntax "────────────────────────────────────────────────────────────∗" : irisLine

syntax irisGoalStx := ppDedent(ppLine irisLine)* ppDedent(ppLine term)

open Lean.PrettyPrinter

@[delab app.Iris.ProofMode.Entails']
def delabIrisGoal : Delab := do
  let expr ← instantiateMVars <| ← getExpr

  -- extract environment
  let some { hyps, goal, .. } := parseIrisGoal? expr | failure

  -- delaborate hypotheses, split into persistent / spatial contexts
  let (_, pers, spat) ← delabHypotheses hyps ({}, #[], #[])
  let goal ← unpackIprop (← delab goal)

  -- persistent context, `────□` (if any), spatial context, `────∗`, goal
  let mut lines := pers.reverse
  if !pers.isEmpty then
    lines := lines.push (← `(irisLine| ────────────────────────────────────────────────────────────□))
  lines := lines ++ spat.reverse
  lines := lines.push (← `(irisLine| ────────────────────────────────────────────────────────────∗))
  return ⟨← `(irisGoalStx| $lines* $goal:term)⟩
where
  delabHypotheses {u prop bi s} (hyps : @Hyps u prop bi s)
      (acc : NameMap Nat × Array (TSyntax `irisLine) × Array (TSyntax `irisLine)) :
      DelabM (NameMap Nat × Array (TSyntax `irisLine) × Array (TSyntax `irisLine)) := do
    match hyps with
    | .emp _ => pure acc
    | .hyp _ name _ p ty _ =>
      let mut (map, pers, spat) := acc
      let (idx, name') ← if let some idx := map.find? name then
        pure (idx + 1, name.appendAfter <| if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
      else
        pure (0, name)
      let nm := mkIdent name'
      let tyStx ← unpackIprop (← delab ty)
      let stx ← `(irisLine| $nm:ident : $tyStx)
      if isTrue p then
        pure (map.insert name idx, pers.push stx, spat)
      else
        pure (map.insert name idx, pers, spat.push stx)
    | .sep _ _ _ _ lhs rhs => delabHypotheses lhs (← delabHypotheses rhs acc)

@[delab app.Iris.ProofMode.HypMarker]
def delabHypMarker : Delab := do unpackIprop (← withAppArg delab)
