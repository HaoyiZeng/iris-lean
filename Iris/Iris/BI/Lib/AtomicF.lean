module

public import Iris.BI
public import Iris.BI.Updates
public import Iris.BI.Lib.Fixpoint
public meta import Iris.ProofMode.Tactics

@[expose] public section
namespace Iris

open Iris.OFE BI

/-!
# Atomic updates without telescopes

An atomic update is a greatest fixpoint: aborting hands the update back, which is
what makes it re-usable and so what a CAS-retry loop needs.

The usual encoding indexes the pre- and postconditions by a *telescope*, so that
`α` can bind any number of variables. That indexing is what forces `Tele.app`,
`ULift.up`, and the `itele_reduce` family whose only job is to scrub those back
out of goals.

Here the binders never reach the type level. Note where the recursive occurrence
sits:

    |={Eo,Ei}=> ∃ x y z, α ∗ ((α ={Ei,Eo}=∗ ‹abort›) ∧ (∀ w, β ={Ei,Eo}=∗ Φ))

`‹abort›` is the *only* recursive position, and it does not mention `x y z`. So
abstract exactly that slot -- `F : PROP → PROP` -- and let the binders live
inside `F` as ordinary `∃`/`∀`. The fixpoint below runs over `Unit → PROP` and
never learns the arity; `iprop`'s quantifiers already accept any number of
binders, and the proof mode already eliminates them (`imod H with ⟨%x, %y, %z,
Hα, Hclose⟩`).
-/

section Definitions
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

/-- An atomic update, given its accessor as a function of the abort slot.

`F P` should be the accessor whose abort branch yields `P`; `atomicUpdateOf F`
ties the knot so that aborting yields the update itself. -/
def atomicUpdateOf (F : PROP → PROP) : PROP :=
  bi_greatest_fixpoint (fun Ψ (_ : Unit) => F (Ψ ())) ()

/-- The monotonicity `atomicUpdateOf`'s laws need, stated on `F` alone.

This is all the fixpoint asks of an accessor, and it mentions neither the
binders nor their number. -/
class AccMono (F : PROP → PROP) extends NonExpansive F where
  mono : ∀ P Q : PROP, ⊢ iprop(□ (P -∗ Q) -∗ (F P -∗ F Q))

/-- The fixpoint's monotonicity obligation, discharged from `AccMono` alone.
Note that neither the binders nor their number appear anywhere. -/
instance instBIMonoPredOfAccMono (F : PROP → PROP) [A : AccMono F] :
    BIMonoPred (PROP := PROP) (A := Unit) (fun Ψ (_ : Unit) => F (Ψ ())) where
  mono_pred := by
    intro Φ Ψ _ _
    iintro #Hmono %u
    iapply (A.mono _ _)
    iintro
    iapply Hmono
  mono_pred_ne := by infer_instance

/-- Non-expansiveness of the fixpoint functional, likewise. -/
instance instNEFunctionalOfAccMono (F : PROP → PROP) [A : AccMono F] :
    NonExpansive (fun (Ψ : Unit → PROP) (_ : Unit) => F (Ψ ())) where
  ne := by
    intro n Ψ Ψ' h _
    exact A.toNonExpansive.ne (h ())

end Definitions

section Laws
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable (F : PROP → PROP) [AccMono F]

/- `BIFUpdate` is only needed by the accessors these laws are applied to, not by
   the laws themselves. -/
set_option linter.unusedSectionVars false

/-- Unfolding: an atomic update is its own accessor's abort slot.

Everything a proof needs follows from this. Opening is `imod` on the fupd inside
`F`; the binders come out as ordinary variables; aborting and committing are the
two branches of the `∧`, reached with `icases … with ⟨Habort, -⟩` and
`⟨-, Hcommit⟩`. -/
theorem auOf_unfold : atomicUpdateOf F ⊢ F (atomicUpdateOf F) := by
  conv => lhs; unfold atomicUpdateOf
  exact greatest_fixpoint_unfold_mp (F := fun Ψ (_ : Unit) => F (Ψ ())) (x := ())

theorem auOf_fold : F (atomicUpdateOf F) ⊢ atomicUpdateOf F := by
  conv => rhs; unfold atomicUpdateOf
  exact greatest_fixpoint_unfold_mpr (F := fun Ψ (_ : Unit) => F (Ψ ())) (x := ())

theorem auOf_unfold_eqv : atomicUpdateOf F ⊣⊢ F (atomicUpdateOf F) :=
  ⟨auOf_unfold F, auOf_fold F⟩

/-- Introduction by coinduction: to produce an update it is enough to give one
accessor whose abort branch restores what you started from.

The abort slot may be either that resource or an update already in hand -- the
`∨` is what makes this a *co*induction rather than a one-shot accessor. -/
theorem auOf_intro (Q : Unit → PROP) [NonExpansive Q] :
    ⊢ iprop(□ (∀ y, Q y -∗ F iprop(Q () ∨ atomicUpdateOf F)) -∗
            ∀ y, Q y -∗ atomicUpdateOf F) :=
  greatest_fixpoint_coind (F := fun Ψ (_ : Unit) => F (Ψ ())) (Φ := Q)

end Laws

/-! ## Opening an atomic update

`auOf_unfold` is generic: one lemma, any accessor, any number of binders. The
tactic below just saves writing it out, and passes the pattern straight through
to `imod`, so the arity is whatever the caller writes.

Compare the telescoped `iauopen`, which had to follow `imod` with
`itele_reduce` to scrub `Tele.app`/`ULift.up`/`Sigma` witnesses back out of the
goal before `icases` could name the binders. There is nothing to scrub here. -/

open Lean in
macro "iauopen " colGt h:specPat " with " colGt pat:icasesPat : tactic =>
  `(tactic| (ihave __au := auOf_unfold _ $$ $h; imod __au with $pat))

/-! ## Discharging `AccMono`

The fixpoint needs its functional monotone; that is fixpoint theory, not a cost
of this encoding. The telescoped version pays it too, but once and out of sight,
because `atomicAcc` there is a *fixed* shape. Here the accessor is written out,
so the obligation lands at each one.

It is short and uniform -- only the two lines naming the binders vary with their
number, everything else is fixed:

```
mono := by
  intro P Q
  iintro #HPQ H
  imod H with ⟨%x, %y, Hα, Hclose⟩   -- one `%` per binder
  imodintro
  iexists x, y                        -- the same names
  isplitl [Hα]
  · iexact Hα
  · isplit
    · iintro Hα'
      icases Hclose with ⟨Habort, -⟩
      imod Habort $$ Hα' with HP
      imodintro
      iapply HPQ $$ HP
    · iapply and_elim_r $$ Hclose
```

Since only those two lines depend on the arity, and a notation building the
accessor already knows it, emitting this is mechanical -- *except* for one Lean
detail. `icasesPat` declares a literal `$` pattern
(`ProofMode/Patterns/CasesPattern.lean:19`), which shadows antiquotation syntax,
so `⟨%$b, $rest⟩` inside a quotation does not parse: the `$` is read as the
literal pattern. A literal `⟨%x, Hr⟩` parses fine. Generating these patterns
therefore needs the `Syntax.node`s built by hand rather than by quotation.
-/

end Iris
