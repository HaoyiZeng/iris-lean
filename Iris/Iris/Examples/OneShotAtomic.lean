module

public import Iris.BI.Lib.Atomic
public import Iris.ProgramLogic.Atomic

@[expose] public section


namespace Iris.OneShot

open BI ProgramLogic Language.Notation Std

/-! ## Definitions -/

section Definitions
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele}

/-- **One-shot atomic update.**

    Compare `Iris.atomicUpdate`, which is `ν P. |={Eo,Ei}=> ∃.. x, α x ∗
    ((α x ={Ei,Eo}=∗ P) ∧ (∀.. y, β x y ={Ei,Eo}=∗ Φ x y))`.  Deleting the left
    conjunct — the *abort* branch — removes the only negative occurrence of `α`, and
    with it the need for a greatest fixpoint.  The implementation gets one attempt at
    the linearisation point rather than an unbounded retry loop. -/
def oneShotAU (Eo Ei : CoPset) (α : TA → PROP) (β Φ : TA → TB → PROP) : PROP :=
  iprop(|={Eo, Ei}=> ∃.. x, α x ∗ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y))

end Definitions

section WeakestPre
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {TA TB TP : Tele}

/-- **One-shot logically atomic triple.**  The mask convention matches upstream
    `atomicWP`: the argument `E` is the part *removed* from `⊤`, i.e. `Eo = ⊤ \ E`.

    Unlike `atomicWP` the update sits under a `▷`, so a caller that has already taken
    a step can supply it. -/
abbrev oneShotWP
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val) : IProp GF :=
  iprop(∀ (Φ : Val → IProp GF),
    ▷ oneShotAU (⊤ \ E) ∅ α β (λ x y => ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
    WP e {{ Φ }})

end WeakestPre

/-! ## Notation

`⟪{ .. }⟫ e @ E ⟪{ .. }⟫`, deliberately distinct from the coinductive `⟪ .. ⟫`.
Only the 0-, 1- and 2-binder `∀` forms are provided. -/

declare_syntax_cat osPre
declare_syntax_cat osPost

syntax "⟪{" ("∀ " ident ", ")? term "}⟫" : osPre
syntax "⟪{" "∀ " ident ", " "∀ " ident ", " term "}⟫" : osPre

syntax "⟪{" "∃ " ident ", " term " | " ident ", " "RET " term "; " term "}⟫" : osPost
syntax "⟪{" "∃ " ident ", " term " | " "RET " term "}⟫" : osPost
syntax "⟪{" term " | " "RET " term "}⟫" : osPost

syntax (name := oneShotTripleNotation)
  ppRealFill(osPre ppSpace term:arg " @ " term:arg ppSpace osPost) : term

macro_rules
  -- two ∀ binders, no ∃, no RET binders   (the `∀ σ, ∀ M` shape used in Array.lean)
  | `(⟪{ ∀ $x₁:ident, ∀ $x₂:ident, $α:term }⟫ $e:term @ $E:term
      ⟪{ $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x₁ => λ $x₂ => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} iprop($β)))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app
            (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none)))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app
            (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v))))
  -- two ∀ binders, ∃ binder, no RET binders
  | `(⟪{ ∀ $x₁:ident, ∀ $x₂:ident, $α:term }⟫ $e:term @ $E:term
      ⟪{ ∃ $y:ident, $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.cons <| λ _ => Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x₁ => λ $x₂ => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app <| λ $y => ULift.up.{0,0} iprop($β))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app <| λ $y =>
            ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app <| λ $y =>
            ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v)))
  -- one ∀ binder, no ∃, no RET binders
  | `(⟪{ ∀ $x:ident, $α:term }⟫ $e:term @ $E:term ⟪{ $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} iprop($β)))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none)))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v))))
  -- one ∀ binder, ∃ binder, no RET binders
  | `(⟪{ ∀ $x:ident, $α:term }⟫ $e:term @ $E:term
      ⟪{ ∃ $y:ident, $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.cons <| λ _ => Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} iprop($β))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v)))
  -- one ∀ binder, ∃ binder, RET binder + POST
  | `(⟪{ ∀ $x:ident, $α:term }⟫ $e:term @ $E:term
      ⟪{ ∃ $y:ident, $β:term | $z:ident, RET $v:term; $POST:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.cons <| λ _ => Tele.nil.{0})
        (TP := Tele.cons <| λ _ => Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} iprop($β))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} <| Tele.app <| λ $z =>
            ULift.up.{0,0} (some iprop($POST)))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} <| Tele.app <| λ $z => ULift.up.{0,0} $v))
  -- no binders at all
  | `(⟪{ $α:term }⟫ $e:term @ $E:term ⟪{ $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.nil.{0})
        (TB := Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app (ULift.up.{0,0} iprop($α)))
        (Tele.app (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} iprop($β))))
        (Tele.app (ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none))))
        (Tele.app (ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v)))))

/-! ## The bridge to `atomicUpdate`

A one-shot spec *implies* the coinductive one, so an existing `atomicWP` interface can
be re-derived from a one-shot replacement rather than migrated. -/

section Bridge
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele} {α : TA → PROP} {β Φ : TA → TB → PROP}

/-- A coinductive atomic update can always be cashed in for a one-shot one: unfold it
    once and take the *commit* conjunct, throwing away the abort branch.

    The converse fails, which is exactly the sense in which a one-shot **spec** is
    stronger: the implementation is handed strictly less. -/
theorem au_to_oneShotAU (Eo Ei : CoPset) :
    atomicUpdate Eo Ei α β Φ ⊢ oneShotAU Eo Ei α β Φ := by
  refine (aupd_aacc α β Φ Eo Ei).trans ?_
  simp only [atomicAcc, oneShotAU]
  iintro HAU
  imod HAU with ⟨%x, Hα, Hcl⟩
  imodintro
  iexists x
  iframe Hα
  icases Hcl with ⟨-, Hcommit⟩
  iexact Hcommit

/-- Widen the outer mask.  The one-shot analogue of `atomicAcc_maskWeaken`, and the
    only mask surgery the rest of the file needs. -/
theorem oneShotAU_maskWeaken (Eo1 Eo2 Ei : CoPset) (HE : Eo1 ⊆ Eo2) :
    oneShotAU Eo1 Ei α β Φ ⊢ oneShotAU Eo2 Ei α β Φ := by
  unfold oneShotAU
  iintro Hstep
  imod fupd_mask_subseteq HE with Hclose1
  imod Hstep with ⟨%x, Hα, Hcl⟩
  imodintro
  iexists x
  iframe Hα
  iintro %y Hβ
  ihave HΦ := Hcl $$ %y Hβ
  imod HΦ with HΦ
  imod Hclose1
  imodintro
  iexact HΦ

end Bridge

/-! ## Triple-level consequences -/

section TripleLemmas
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {TA TB TP : Tele}

/-- Every one-shot triple is also a coinductive one: the update sits in *negative*
    position, so `au_to_oneShotAU` applies contravariantly.  An existing `atomicWP`
    spec is therefore a one-line corollary of its one-shot replacement. -/
theorem oneShotWP_to_atomicWP
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF) (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF)) (f : TA → TB → TP → Val) :
    oneShotWP e E α β POST f ⊢ atomicWP e E α β POST f := by
  unfold oneShotWP atomicWP
  iintro Hwp %Φ HAU
  ihave Hgoal := Hwp $$ %Φ
  iapply Hgoal
  inext
  iapply au_to_oneShotAU $$ HAU

end TripleLemmas

section Monotonicity
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele}

/-- Covariant in the atomic precondition.  `α` occurs only positively, so a *single*
    entailment suffices; the coinductive update needs both directions because `α` also
    appears to the left of the abort wand. -/
theorem oneShotAU_mono_pre (Eo Ei : CoPset) (α α' : TA → PROP) (β Φ : TA → TB → PROP)
    (H : ∀ x, α x ⊢ α' x) :
    oneShotAU Eo Ei α β Φ ⊢ oneShotAU Eo Ei α' β Φ := by
  unfold oneShotAU
  iintro HAU
  imod HAU with ⟨%x, Hα, Hcl⟩
  imodintro
  iexists x
  isplitl [Hα]
  · iapply H x $$ Hα
  · iexact Hcl

/-- Contravariant in the atomic postcondition: `β` occurs only to the left of a wand. -/
theorem oneShotAU_mono_post (Eo Ei : CoPset) (α : TA → PROP) (β β' Φ : TA → TB → PROP)
    (H : ∀ x y, β' x y ⊢ β x y) :
    oneShotAU Eo Ei α β Φ ⊢ oneShotAU Eo Ei α β' Φ := by
  unfold oneShotAU
  iintro HAU
  imod HAU with ⟨%x, Hα, Hcl⟩
  imodintro
  iexists x
  iframe Hα
  iintro %y Hβ
  iapply Hcl $$ %y
  iapply H x y $$ Hβ

/-- Covariant in the continuation; the analogue of `atomicAcc_wand`'s `Φ` argument. -/
theorem oneShotAU_mono_cont (Eo Ei : CoPset) (α : TA → PROP) (β Φ Φ' : TA → TB → PROP)
    (H : ∀ x y, Φ x y ⊢ Φ' x y) :
    oneShotAU Eo Ei α β Φ ⊢ oneShotAU Eo Ei α β Φ' := by
  unfold oneShotAU
  iintro HAU
  imod HAU with ⟨%x, Hα, Hcl⟩
  imodintro
  iexists x
  iframe Hα
  iintro %y Hβ
  ihave HΦ := Hcl $$ %y Hβ
  imod HΦ with HΦ
  imodintro
  iapply H x y $$ HΦ

/-- Framing.  A resource held across the linearisation point rides along without ever
    entering `α`.  Under `atomicUpdate` this is painful because `R` would have to
    survive every abort round trip. -/
theorem oneShotAU_frame (Eo Ei : CoPset) (R : PROP) (α : TA → PROP) (β Φ : TA → TB → PROP) :
    iprop(R ∗ oneShotAU Eo Ei α β Φ) ⊢
      oneShotAU Eo Ei α β (λ x y => iprop(R ∗ Φ x y)) := by
  unfold oneShotAU
  iintro ⟨HR, HAU⟩
  imod HAU with ⟨%x, Hα, Hcl⟩
  imodintro
  iexists x
  iframe Hα
  iintro %y Hβ
  ihave HΦ := Hcl $$ %y Hβ
  imod HΦ with HΦ
  imodintro
  simp only []
  iframe HR HΦ

end Monotonicity

section Structural
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {TA TB TP : Tele}

/-- Sequential collapse: a client that owns `α` outright uses the atomic spec as an
    ordinary Hoare triple. -/
theorem oneShotWP_seq
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF) (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF)) (f : TA → TB → TP → Val) :
    oneShotWP e E α β POST f ⊢
      iprop(∀ (Φ : Val → IProp GF), ∀.. x,
        α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }}) := by
  iintro Hwp
  iapply atomicWP_seq e E α β POST f
  iapply oneShotWP_to_atomicWP e E α β POST f $$ Hwp

/-- Absorb a client invariant into the atomic precondition: a spec whose `α` demands
    `▷ I` alongside the real precondition is traded for one that does not, at the price
    of the mask `↑N`. -/
theorem oneShotWP_inv
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF) (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF)) (f : TA → TB → TP → Val)
    (N : Namespace) (I : IProp GF) (HN : ↑N ⊆ E) :
    oneShotWP e (E \ ↑N)
      (λ x => iprop(▷ I ∗ α x))
      (λ x y => iprop(▷ I ∗ β x y)) POST f -∗
    inv N I -∗ oneShotWP e E α β POST f := by
  unfold oneShotWP
  iintro Hwp #Hinv %Φ HAU
  have HNmask : ↑N ⊆ (⊤ \ (E \ ↑N) : CoPset) := by
    intro x hxN
    rw [LawfulSet.mem_diff]
    refine ⟨CoPset.mem_full, fun hx => ?_⟩
    rw [LawfulSet.mem_diff] at hx
    exact hx.2 hxN
  have Houter : (⊤ \ E : CoPset) ⊆ ((⊤ \ (E \ ↑N)) \ ↑N : CoPset) := by
    intro x hx
    rw [LawfulSet.mem_diff] at hx ⊢
    refine ⟨?_, fun hxN => hx.2 (HN x hxN)⟩
    rw [LawfulSet.mem_diff]
    refine ⟨hx.1, fun hxEdiff => ?_⟩
    rw [LawfulSet.mem_diff] at hxEdiff
    exact hx.2 hxEdiff.1
  ihave Hgoal := Hwp $$ %Φ
  iapply Hgoal
  inext
  ihave HAU := oneShotAU_maskWeaken (α := α) (β := β) _ _ ∅ Houter $$ HAU
  unfold oneShotAU
  imod inv_acc HNmask $$ Hinv with ⟨HI, HcloseInv⟩
  imod HAU with ⟨%x, Hα, Hcl⟩
  imodintro
  iexists x
  isplitl [HI Hα]
  · simp only []
    iframe HI Hα
  iintro %y HβI
  icases HβI with ⟨HI', Hβ⟩
  ihave HΦ := Hcl $$ %y Hβ
  imod HΦ with HΦ
  imod HcloseInv $$ HI' with _
  imodintro
  iexact HΦ

end Structural

/-! ## Smoke tests for the notation

These only check that each `macro_rule` elaborates; they assert nothing. -/

section Smoke
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

/-- No binders. -/
example (e : Expr) (E : CoPset) (P Q : IProp GF) (v : Val) : IProp GF :=
  ⟪{ P }⟫ e @ E ⟪{ Q | RET v }⟫

/-- One `∀` binder. -/
example (e : Expr) (E : CoPset) (P : Nat → IProp GF) (Q : IProp GF) (v : Val) : IProp GF :=
  ⟪{ ∀ n, P n }⟫ e @ E ⟪{ Q | RET v }⟫

/-- One `∀`, one `∃`. -/
example (e : Expr) (E : CoPset) (P : Nat → IProp GF) (Q : Nat → IProp GF) (v : Val) :
    IProp GF :=
  ⟪{ ∀ n, P n }⟫ e @ E ⟪{ ∃ m, Q m | RET v }⟫

/-- One `∀`, one `∃`, one RET binder with a `POST`. -/
example (e : Expr) (E : CoPset) (P : Nat → IProp GF) (Q R : Nat → IProp GF)
    (g : Nat → Val) : IProp GF :=
  ⟪{ ∀ n, P n }⟫ e @ E ⟪{ ∃ m, Q m | k, RET g k; R k }⟫

/-- Two `∀` binders — the `∀ σ, ∀ M` shape `Array.lean` uses throughout. -/
example (e : Expr) (E : CoPset) (P : Nat → Bool → IProp GF) (Q : IProp GF) (v : Val) :
    IProp GF :=
  ⟪{ ∀ n, ∀ b, P n b }⟫ e @ E ⟪{ Q | RET v }⟫

/-- Two `∀` binders plus an `∃`. -/
example (e : Expr) (E : CoPset) (P : Nat → Bool → IProp GF) (Q : Nat → IProp GF)
    (v : Val) : IProp GF :=
  ⟪{ ∀ n, ∀ b, P n b }⟫ e @ E ⟪{ ∃ m, Q m | RET v }⟫

end Smoke

end Iris.OneShot
