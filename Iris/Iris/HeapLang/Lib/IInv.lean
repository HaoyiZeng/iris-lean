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
variable {A B : Type _}

/-- The core of Rocq's `elim_acc_aacc`: open a **timeless** invariant `inv N I`
*inside* an atomic accessor goal `atomicAcc E1 E2 α Pas β Φ` (needs `↑N ⊆ E1`),
keeping the goal an accessor. You are handed the body `I` (already stripped of
`▷`, since it is timeless) and must prove an accessor at the reduced mask
`E1 \ ↑N` whose abort/commit each hand `I` back (to re-close the invariant). -/
theorem aacc_inv {E1 E2 : CoPset} {N : Namespace} {I : IProp GF} [Timeless I]
    (α : A → IProp GF) (Pas : IProp GF) (β Φ : A → B → IProp GF) (Hsub : ↑N ⊆ E1) :
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
accessor is preserved, so `iaaccintro` can finish it — this is the Rocq
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

section AaccIntroPacked
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta Qq Std Iris.ProofMode

/- The packed-witness `iaaccintro` that used to live here now *is* `iaaccintro`,
in `Iris/BI/Lib/Atomic.lean`: the version defined there could only match a
hypothesis that was syntactically `α` applied to one argument, which no
multi-binder triple ever produces, so it was unusable and the two have been
merged. -/

/-- Cast lemma used by `iunfold`: from a definitional equality `ty = ty'`, produce the
persistent replacement wand needed by `Hyps.replace`. -/
theorem iunfoldCast {PROP : Type _} [BI PROP] {e ty ty' : PROP} (h : ty = ty') :
    e ⊢ <pers> (ty -∗ ty') := by
  subst h
  exact persistently_emp_intro.trans (persistently_mono (wand_intro emp_sep.1))

/-- `iunfold f at h` δ-unfolds the definition `f` inside the proof-mode hypothesis `h`. -/
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

end AaccIntroPacked

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
example {A B : Type _} (N : Namespace) (x0 : A)
    (α : A → IProp GF) (Pas : IProp GF) (Φ : A → B → IProp GF) [BI.Timeless (α x0)] :
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
