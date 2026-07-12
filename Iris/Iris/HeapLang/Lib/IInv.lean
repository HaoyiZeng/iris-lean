module

public import Iris.Instances.Lib.Invariants
public import Iris.BI.Lib.Atomic
public meta import Iris.ProofMode.Tactics

/-!
## A local `iinv` tactic (poor-man's Rocq `iInv`)

`iInv` is not ported to iris-lean (see `Iris/ProofMode/Porting.lean`). This file
provides small *local* tools so that opening a (timeless) invariant reads closer
to the Rocq idiom, without touching any upstream file.

Two flavours:
* `iinv h with ⟨pat, cl⟩` — open an invariant in an ordinary `|={E,E'}=>` goal
  (thin wrapper around `inv_acc_timeless`).
* `aacc_inv` / `iinv_aacc` — the analogue of Rocq's `elim_acc_aacc`: open an
  invariant *inside* an atomic accessor (`atomicAcc`) goal, **keeping it an
  accessor**, so that `iaaccintro` can be used afterwards.
-/

namespace Iris
open Iris.ProofMode BI

@[expose] public section

/-- Open a **timeless** invariant `h : inv N I` in a fupd goal `|={E, E'}=> Q`
(requires `↑N ⊆ E`). `iinv h with ⟨pat, cl⟩` destructures the body via `pat`,
binds the closer `cl`, and moves the goal mask to `E \ ↑N`. -/
macro "iinv " h:ident " with " pat:icasesPat : tactic =>
  `(tactic|
    imod inv_acc_timeless
      (by first
        | assumption
        | exact Iris.Std.LawfulSet.subset_refl
        | (intro x hx; first | exact CoPset.mem_full | simp_all)
        | solve_by_elim
        | simp_all)
      $$ $h:ident with $pat)

section AaccInv
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]
variable {TA TB : Tele}

/-- The core of Rocq's `elim_acc_aacc`: open a **timeless** invariant `inv N I`
*inside* an atomic accessor goal `atomicAcc E1 E2 α Pas β Φ` (needs `↑N ⊆ E1`),
keeping the goal an accessor. You are handed the body `I` (already stripped of
`▷`, since it is timeless) and must prove an accessor at the reduced mask
`E1 \ ↑N` whose abort/commit each hand `I` back (to re-close the invariant). -/
theorem aacc_inv {E1 E2 : CoPset} {N : Namespace} {I : IProp GF} [Timeless I]
    (α : TA → IProp GF) (Pas : IProp GF) (β Φ : TA → TB → IProp GF) (Hsub : ↑N ⊆ E1) :
    inv N I -∗
    (I -∗ atomicAcc (E1 \ ↑N) E2 α iprop(I ∗ Pas) β (fun x y => iprop(I ∗ Φ x y))) -∗
    atomicAcc E1 E2 α Pas β Φ := by
  iintro #Hinv Hcont
  unfold atomicAcc
  -- open the invariant: E1 → E1\N, get `I` (▷ stripped by timelessness) and a closer
  imod inv_acc Hsub $$ Hinv with ⟨>HI, Hcl⟩
  -- feed `I` to the continuation to obtain the reduced accessor, then open it
  ihave Hinner := Hcont $$ HI
  imod Hinner with ⟨%x, Hα, Hclose⟩
  imodintro
  iexists x
  iframe Hα
  isplit
  · -- abort: the reduced accessor hands `I ∗ Pas` back; use `I` to close the inv
    iintro Hα
    icases Hclose with ⟨Habort, -⟩
    imod Habort $$ Hα with ⟨HI, HPas⟩
    imod Hcl $$ HI
    imodintro; iexact HPas
  · -- commit: symmetric, closing the inv with the returned `I`
    iintro %y Hβ
    icases Hclose with ⟨-, Hcommit⟩
    imod Hcommit $$ %y Hβ with ⟨HI, HΦ⟩
    imod Hcl $$ HI
    imodintro; iexact HΦ

/-- Open a timeless invariant `h : inv N I` *inside an atomic accessor goal*
`atomicAcc E1 E2 α P β Φ` (via `aacc_inv`), handing you the body as `body`. The
accessor is preserved, so `iaaccintro'` can finish it — this is the Rocq
`iInv … ; iaaccintro …` idiom. Companion to the fupd-goal `iinv … with …`. -/
macro "iinv " h:ident " as " body:ident : tactic =>
  `(tactic|
    (iapply aacc_inv _ _ _ _
      (by first
        -- Prove `↑N ⊆ E1` *membership-wise* first: for the common `E1 = ⊤` this is
        -- `x ∈ ⊤` (cheap `mem_full`). Trying `subset_refl`/`assumption` first would
        -- unify `↑N =?= E1`, forcing a full namespace/coPset reduction (deep, slow).
        | (intro x hx; exact CoPset.mem_full)
        | (simp only [Iris.Std.LawfulSet.diff_empty]; intro x hx; exact CoPset.mem_full)
        | assumption
        | exact Iris.Std.LawfulSet.subset_refl
        | (intro x hx; simp_all)) $$ $h:ident
     iintro $body:ident))

end AaccInv

section AaccIntroTele
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta Qq Std Iris.ProofMode

/-- Build a telescope-argument value `x : Tele.Arg TA` whose components are fresh
metavariables (for a concrete `nil`/`cons` telescope `TA`). Unifying `α x` against
a *reduced* hypothesis then solves those metavariables — this is what lets us
select a concrete resource like `l ↦ #b` against a telescope-encoded `α`. -/
meta partial def mkTeleArgMVar (TA : Expr) : MetaM Expr := do
  let TA ← whnfD TA
  let fn := TA.getAppFn
  match fn.constName? with
  | some ``Iris.Tele.nil =>
      let u := fn.constLevels![0]!
      return mkConst ``PUnit.unit [Level.succ u]
  | some ``Iris.Tele.cons =>
      let u := fn.constLevels![0]!
      let args := TA.getAppArgs
      let X := args[0]!
      let b := args[1]!
      let xmv ← mkFreshExprMVar X
      let bx ← whnfD (mkApp b xmv)
      let rest ← mkTeleArgMVar bx
      let motive ← withLocalDeclD `x X fun x =>
        mkLambdaFVars #[x] (mkApp (mkConst ``Iris.Tele.Arg [u]) (mkApp b x))
      return mkAppN (mkConst ``Sigma.mk [u, u]) #[X, motive, xmv, rest]
  | _ => throwError "iaaccintro': telescope is not a concrete nil/cons: {TA}"

/-- Like the upstream `iaaccintro`, but it locates the telescope witness `x` by
unifying `α x` with the selected hypothesis *up to telescope reduction* (via
`mkTeleArgMVar`), so it also works when the resource is a concrete `pointsTo`
(e.g. `l ↦ #b`) rather than a syntactic `α x`. -/
elab "iaaccintro' " " with " h:ident : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse (← `(pmTerm| $h:ident))
  ProofModeM.runTactic λ mvar g => do
    let { prop, hyps, goal, .. } := g
    let goal ← instantiateMVars goal
    let_expr atomicAcc _ _ _ TA TB Eo Ei α P β Φ := goal |
      throwError "iaaccintro': goal is not an atomic accessor"
    let uTB := (← inferType TB).getAppFn.constLevels![0]!
    let ⟨_, hyps', p, out, Hsel⟩ ← iHave hyps pmt false
    unless p.isConstOf ``false do
      throwError "iaaccintro': selected hypothesis must be spatial"
    -- find `x : Tele.Arg TA` with `α x` defeq to the selected hypothesis `out`
    let x ← mkTeleArgMVar TA
    unless ← isDefEq (mkApp α x) out do
      throwError "iaaccintro': selected hypothesis does not match the atomic precondition"
    let x ← instantiateMVars x
    let some Eiq ← checkTypeQ Ei q(CoPset) |
      throwError "iaaccintro': malformed atomic accessor inner mask"
    let some Eoq ← checkTypeQ Eo q(CoPset) |
      throwError "iaaccintro': malformed atomic accessor outer mask"
    let Hsub : Q($Eiq ⊆ $Eoq) ← mkFreshExprSyntheticOpaqueMVar q($Eiq ⊆ $Eoq)
    let sideGoals ← evalTacticAt
      (← `(tactic| first | exact LawfulSet.empty_subset | assumption | trivial))
      Hsub.mvarId!
    for sideGoal in sideGoals do
      addMVarGoal sideGoal
    -- Reduce telescope applications (`Tele.app … ⟨b,()⟩ y`) so the abort/commit
    -- subgoals are clean — the user never has to sprinkle `itele_reduce`.
    let αx ← reduceTeleApps (mkApp α x)
    let fupdP ← mkAppM ``FUpd.fupd #[Eo, Eo, P]
    let abortGoal ← mkAppM ``BIBase.wand #[αx, fupdP]
    let yTy := mkApp (mkConst ``Iris.Tele.Arg [uTB]) TB
    let commitGoal ← withLocalDeclD `y yTy fun y => do
      let βxy ← reduceTeleApps (mkApp2 β x y)
      let Φxy ← reduceTeleApps (mkApp2 Φ x y)
      let fupdΦ ← mkAppM ``FUpd.fupd #[Eo, Eo, Φxy]
      let body ← mkAppM ``BIBase.wand #[βxy, fupdΦ]
      let lam ← mkLambdaFVars #[y] body
      mkAppM ``biTforall #[lam]
    let some abortGoal ← checkTypeQ abortGoal prop |
      throwError "iaaccintro': internal error, malformed abort subgoal"
    let some commitGoal ← checkTypeQ commitGoal prop |
      throwError "iaaccintro': internal error, malformed commit subgoal"
    let Habort ← addBIGoal hyps' abortGoal
    let Hcommit ← addBIGoal hyps' commitGoal
    let pf ← mkAppM ``tacAaccIntro #[α, β, Φ, P, Eo, Ei, x, Hsub, Hsel, Habort, Hcommit]
    mvar.assign pf

/-- Cast lemma used by `iunfold`: from a definitional equality `ty = ty'`, produce the
persistent replacement wand needed by `Hyps.replace`. -/
theorem iunfoldCast {PROP : Type _} [BI PROP] {e ty ty' : PROP} (h : ty = ty') :
    e ⊢ <pers> (ty -∗ ty') := by
  subst h
  exact persistently_emp_intro.trans (persistently_mono (wand_intro emp_sep.1))

/-- `iunfold f at h` δ-unfolds the definition `f` inside the **proof-mode** hypothesis `h`.
This is a purely definitional change (the hypothesis' proof term is unchanged; validity is
witnessed by `wand_rfl`), working around the fact that `simp only [f] at h` / `unfold f at h`
do not apply to virtual proof-mode hypotheses.  Only sound for defs whose unfolding is `rfl`
(i.e. not well-founded recursion); do **not** use it on recursive predicates like `contents`. -/
elab "iunfold " f:ident " at " h:ident : tactic => do
  let declName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo f
  ProofModeM.runTactic fun mvar g => do
    let { prop, e, hyps, goal, .. } := g
    let ivar ← hyps.findWithInfo h
    let some ⟨_, hyps', pf⟩ ← hyps.replace ivar (fun _ _ ty => do
        let r ← Lean.Meta.unfold ty declName
        let some ty' ← checkTypeQ r.expr prop
          | throwError "iunfold: unfolded hypothesis is ill-typed"
        let heqE ← match r.proof? with
          | some p => pure p
          | none   => Lean.Meta.mkEqRefl ty
        let some heq ← checkTypeQ heqE q(($ty : $prop) = $ty')
          | throwError "iunfold: could not build the unfolding equality"
        let pf0 : Q($e ⊢ <pers> ($ty -∗ $ty')) := q(iunfoldCast $heq)
        return ⟨ty', pf0⟩)
      | throwError "iunfold: cannot find hypothesis {h}"
    let pf' ← addBIGoal hyps' goal
    mvar.assign q(Entails.trans $pf $pf')

end AaccIntroTele

section Test
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]

/-- Sanity check for `iinv`: open then immediately close a timeless invariant. -/
example (N : Namespace) (P : IProp GF) [BI.Timeless P] :
    ⊢ inv N P ={⊤}=∗ True := by
  iintro #Hinv
  iinv Hinv with ⟨HP, Hcl⟩
  imod Hcl $$ HP
  itrivial

/-- End-to-end demo of the ported `elim_acc_aacc`: `aacc_inv` opens an invariant
*inside* an atomic accessor while keeping it an accessor, so that `iaaccintro`
can finish it — the Rocq `iInv … ; iaaccintro with …` idiom.

Here the invariant holds the atomic resource `α x0`; opening it hands us `α x0`,
which we give to the accessor. On abort we return it unchanged; on commit the
accessor's own `β x0 y = α x0` gives it straight back. Both branches also hand
back the invariant body (added by `aacc_inv`) so it can be re-closed. -/
example {TA TB : Tele} (N : Namespace) (x0 : TA)
    (α : TA → IProp GF) (Pas : IProp GF) (Φ : TA → TB → IProp GF) [BI.Timeless (α x0)] :
    ⊢ inv N (α x0) -∗ Pas -∗
      atomicAcc ⊤ ∅ α Pas (fun x _ => α x) (fun x y => iprop(Φ x y ∨ True)) := by
  iintro #Hinv HPas
  -- open the invariant *inside* the accessor (`aacc_inv` = `elim_acc_aacc`):
  iapply aacc_inv _ _ _ _ (by intro x hx; exact CoPset.mem_full) $$ Hinv
  iintro HI                         -- HI : α x0  (the atomic resource, from the invariant)
  -- now the goal is *still an accessor*; finish it with `iaaccintro`:
  iaaccintro with HI
  · -- abort: hand back `α x0 ∗ Pas` (the invariant body ∗ the kept resource)
    iintro HI; imodintro; isplitl [HI] <;> iassumption
  · -- commit: `β x0 y = α x0`, so give back `α x0 ∗ (Φ x0 y ∨ True)`
    iintro %y Hβ; imodintro; isplitl [Hβ]
    · iexact Hβ
    · iright; itrivial

/-- Sanity check for `iunfold`: unfold a non-recursive definition inside a proof-mode
hypothesis, then use the unfolded form. -/
private def iunfoldTestDef (P Q : IProp GF) : IProp GF := iprop(P ∗ Q)

example (P Q : IProp GF) : iunfoldTestDef P Q ⊢ iprop(Q ∗ P) := by
  iintro H
  iunfold iunfoldTestDef at H
  icases H with ⟨HP, HQ⟩
  isplitl [HQ] <;> iassumption

end Test

end

end Iris
