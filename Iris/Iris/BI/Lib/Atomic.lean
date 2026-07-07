module

public import Iris.BI
public import Iris.BI.Updates
public import Iris.BI.Telescopes
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public meta import Iris.ProofMode.Tactics

@[expose] public section
namespace Iris

open Iris.OFE BI

section Definitions
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele}

@[rocq_alias atomic_acc]
def atomicAcc (Eo Ei : CoPset)
  (α : TA → PROP) (P : PROP) (β Φ: TA → TB → PROP) : PROP :=
  iprop(|={Eo, Ei}=> ∃.. x, α x ∗ ((α x ={Ei, Eo}=∗ P) ∧ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y)))

@[rocq_alias atomic_acc_wand]
theorem atomicAcc_wand α (P1 P2 : PROP) β Eo Ei (Φ1 Φ2 : TA → TB → PROP) :
  ((P1 -∗ P2) ∧ (∀ x y, (Φ1 x y -∗ Φ2 x y)) -∗
  (atomicAcc Eo Ei α P1 β Φ1 -∗ atomicAcc Eo Ei α P2 β Φ2)) := by
  iintro Hwand Hatomic
  simp only [atomicAcc]
  imod Hatomic with ⟨%x, ⟨Hα, Hclose⟩⟩
  imodintro
  iexists x
  iframe Hα
  isplit
  · iintro Hα
    icases Hclose with ⟨Hclose, -⟩
    icases Hwand with ⟨Hwand, -⟩
    imod Hclose $$ Hα
    imodintro
    iapply Hwand
    iassumption
  · iintro %y Hβ
    icases Hclose with ⟨-, Hclose⟩
    icases Hwand with ⟨-, Hwand⟩
    imod Hclose $$ %y Hβ
    imodintro
    iapply Hwand
    iassumption

@[rocq_alias atomic_acc_mask]
theorem atomicAcc_mask (Eo Ed : CoPset) α (P : PROP) β (Φ : TA → TB → PROP) :
  atomicAcc Eo (Eo\Ed) α P β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → atomicAcc E (E\Ed) α P β Φ := by
  isplit
  · iintro Hatomic %E %HE
    unfold atomicAcc
    iapply fupd_mask_frame_acc HE $$ Hatomic
    iintro Hstep
    icases Hstep with ⟨%x, Hα, Hclose⟩
    iintro !> Hclose'
    iexists x
    iframe Hα
    isplit
    · iintro Hα
      iapply Hclose'
      icases Hclose with ⟨Hclose, -⟩
      iapply Hclose $$ Hα
    · iintro %y Hβ
      iapply Hclose'
      icases Hclose with ⟨-, Hclose⟩
      iapply Hclose $$ %y Hβ
  · iintro Hatomic
    exact (and_intro (pure_intro (fun _ h => h)) (forall_elim Eo)).trans imp_elim_right

@[rocq_alias atomic_acc_mask_weaken]
theorem atomicAcc_maskWeaken (Eo1 Eo2 Ei : CoPset) α (P : PROP) β (Φ : TA → TB → PROP) :
    Eo1 ⊆ Eo2 →
    atomicAcc Eo1 Ei α P β Φ -∗ atomicAcc Eo2 Ei α P β Φ := by
  intro HE
  iintro Hstep
  unfold atomicAcc
  imod fupd_mask_subseteq HE with Hclose1
  imod Hstep with ⟨%x, Hα, Hclose2⟩
  imodintro
  iexists x
  iframe Hα
  isplit
  · iintro Hα
    icases Hclose2 with ⟨Hclose2, -⟩
    imod Hclose2 $$ Hα with HP
    imod Hclose1
    imodintro
    iexact HP
  · iintro %y Hβ
    icases Hclose2 with ⟨-, Hclose2⟩
    imod Hclose2 $$ %y Hβ with HΦ
    imod Hclose1
    imodintro
    iexact HΦ

variable (Eo Ei : CoPset) (α : TA → PROP) (β Φ : TA → TB → PROP)

def atomicUpdatePre (Ψ : Unit → PROP) (_ : Unit) : PROP :=
  atomicAcc Eo Ei α (Ψ ()) β Φ

@[rocq_alias atomic_update_pre_mono]
instance atomicUpdatePre_mono :
  BIMonoPred (atomicUpdatePre Eo Ei α β Φ) where
  mono_pred := by
    intro Ψ1 Ψ2 _ _
    iintro #Hmono %u Hau
    cases u
    unfold atomicUpdatePre
    ihave Hwand : (Ψ1 () -∗ Ψ2 ()) ∧ (∀ x y, Φ x y -∗ Φ x y) $$ []
    · isplit
      · iapply Hmono $$ %()
      · iintro %_ %_ H
        iexact H
    iapply atomicAcc_wand α (Ψ1 ()) (Ψ2 ()) β Eo Ei Φ Φ $$ Hwand Hau
  mono_pred_ne.ne {n} {u1} {u2} _ := by
    cases u1
    cases u2
    exact .rfl

#rocq_ignore atomic_update_def "`atomicUpdate` is defined directly without Rocq seal/unseal."
#rocq_ignore atomic_update_aux "`atomicUpdate` is defined directly without Rocq seal/unseal."
#rocq_ignore atomic_update_unseal "`atomicUpdate` is defined directly without Rocq seal/unseal."

@[rocq_alias atomic_update]
def atomicUpdate : PROP := bi_greatest_fixpoint (atomicUpdatePre Eo Ei α β Φ) ()

end Definitions

declare_syntax_cat auPre
syntax " ⟪ " ("∃ " ident ", ")? term " ⟫ " : auPre

declare_syntax_cat auPost
syntax " ⟪ " ("∀ " ident ", ")? term (", " "COMM " term)? " ⟫ " : auPost

syntax (name := atomicUpdateNotation)
  "AU " auPre " @ " term ", " term  auPost : term

macro_rules
  | `(AU ⟪ ∃ $x:ident, $α:term ⟫ @ $Eo:term, $Ei:term
        ⟪ ∀ $y:ident, $β:term, COMM $Φ:term ⟫) =>
      `(atomicUpdate (TA := Tele.cons (λ _ : _ => Tele.nil))
          (TB := Tele.cons (λ _ : _ => Tele.nil))
          $Eo $Ei
          (λ a => match a with | ⟨$x, _⟩ => iprop($α))
          (λ a b => match a, b with | ⟨$x, _⟩, ⟨$y, _⟩ => iprop($β))
          (λ a b => match a, b with | ⟨$x, _⟩, ⟨$y, _⟩ => iprop($Φ)))

namespace AtomicDelab

open Lean PrettyPrinter

meta def appArgs? : Syntax → Option (Array Syntax)
  | .node _ `Lean.Parser.Term.app #[_, .node _ `null args] => some args
  | _ => none

meta def funBody? : Syntax → Option Syntax
  | .node _ `Lean.Parser.Term.fun
      #[_, .node _ `Lean.Parser.Term.basicFun #[_, _, _, body]] => some body
  | _ => none

meta def anonCtorHead? : Syntax → Option (TSyntax `ident)
  | .node _ `Lean.Parser.Term.anonymousCtor #[_, .node _ `null args, _] =>
      match args[0]? with
      | some h => if h.isIdent then some ⟨h⟩ else none
      | none => none
  | _ => none

meta partial def collectAnonCtorHeads (stx : Syntax) : Array (TSyntax `ident) :=
  match anonCtorHead? stx with
  | some x => #[x]
  | none => stx.getArgs.foldl (init := #[]) fun acc child => acc ++ collectAnonCtorHeads child

meta def matchAlt? : Syntax → Option (Array (TSyntax `ident) × TSyntax `term) := fun body => do
  let .node _ k xs := body | none
  if k != `Lean.Parser.Term.match then none else
  let some altsStx := xs[5]? | none
  let .node _ altsK alts := altsStx | none
  if altsK != `Lean.Parser.Term.matchAlts then none else
  let some altStx := alts[0]? | none
  let .node _ nullK altWrap := altStx | none
  if nullK != `null then none else
  let some matchAltStx := altWrap[0]? | none
  let .node _ matchAltK alt := matchAltStx | none
  if matchAltK != `Lean.Parser.Term.matchAlt then none else
  let some pat := alt[1]? | none
  let some rhs := alt[3]? | none
  some (collectAnonCtorHeads pat, ⟨rhs⟩)

meta def packedFun? (arity : Nat) (stx : Syntax) : Option (Array (TSyntax `ident) × TSyntax `term) := do
  let body ← funBody? stx
  let (xs, rhs) ← matchAlt? body
  if xs.size == arity then
    some (xs, rhs)
  else
    none

end AtomicDelab

@[app_unexpander atomicUpdate]
meta def unexpandAtomicUpdate : Lean.PrettyPrinter.Unexpander
  | stx => do
      let some #[Eo, Ei, αArg, βArg, ΦArg] := AtomicDelab.appArgs? stx | throw ()
      let some (xs, α) := AtomicDelab.packedFun? 1 αArg | throw ()
      let some (ys, β) := AtomicDelab.packedFun? 2 βArg | throw ()
      let some (_, Φ) := AtomicDelab.packedFun? 2 ΦArg | throw ()
      let some x := xs[0]? | throw ()
      let some y := ys[1]? | throw ()
      `(AU ⟪ ∃ $x:ident, $α:term ⟫ @ $(⟨Eo⟩), $(⟨Ei⟩)
        ⟪ ∀ $y:ident, $β:term, COMM $Φ:term ⟫)


section Lemmas
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele}
variable (α : TA → PROP) (β Φ: TA → TB → PROP) (P : PROP)

@[rocq_alias atomic_acc_ne]
theorem atomicAcc_ne Eo Ei {n}
    {α1 α2 : TA → PROP} {P1 P2 : PROP}
    {β1 β2 Φ1 Φ2 : TA → TB → PROP} :
    (∀ x, α1 x ≡{n}≡ α2 x) →
    P1 ≡{n}≡ P2 →
    (∀ x y, β1 x y ≡{n}≡ β2 x y) →
    (∀ x y, Φ1 x y ≡{n}≡ Φ2 x y) →
    atomicAcc Eo Ei α1 P1 β1 Φ1 ≡{n}≡
      atomicAcc Eo Ei α2 P2 β2 Φ2 := by
  intro Hα HP Hβ HΦ
  unfold atomicAcc
  refine BIFUpdate.ne.ne ?_
  refine biTexist_ne.ne ?_
  intro x
  refine sep_ne.ne (Hα x) ?_
  refine and_ne.ne ?_ ?_
  · refine wand_ne.ne (Hα x) ?_
    exact BIFUpdate.ne.ne HP
  · refine biTforall_ne.ne ?_
    intro y
    refine wand_ne.ne (Hβ x y) ?_
    exact BIFUpdate.ne.ne (HΦ x y)

instance atomicAcc_ne_inst Eo Ei : NonExpansive (atomicAcc Eo Ei α P β) where
  ne {_ _ _} HΦ := atomicAcc_ne Eo Ei (fun _ => .rfl) .rfl (fun _ _ => .rfl) HΦ

@[rocq_alias atomic_update_ne]
theorem atomicUpdate_ne Eo Ei {n}
    {α1 α2 : TA → PROP} {β1 β2 Φ1 Φ2 : TA → TB → PROP} :
    (∀ x, α1 x ≡{n}≡ α2 x) →
    (∀ x y, β1 x y ≡{n}≡ β2 x y) →
    (∀ x y, Φ1 x y ≡{n}≡ Φ2 x y) →
    atomicUpdate Eo Ei α1 β1 Φ1 ≡{n}≡
      atomicUpdate Eo Ei α2 β2 Φ2 := by
  intro Hα Hβ HΦ
  unfold atomicUpdate
  refine exists_ne fun Ψ => ?_
  refine sep_ne.ne ?_ .rfl
  refine intuitionistically_ne.ne ?_
  refine forall_ne fun u => ?_
  refine wand_ne.ne .rfl ?_
  unfold atomicUpdatePre
  exact atomicAcc_ne Eo Ei Hα .rfl Hβ HΦ

instance atomicUpdate_ne_inst Eo Ei : NonExpansive (atomicUpdate Eo Ei α β) where
  ne {_ _ _} HΦ := atomicUpdate_ne Eo Ei (fun _ => .rfl) (fun _ _ => .rfl) HΦ

@[rocq_alias atomic_update_mask_weaken]
theorem atomicUpdate_maskWeaken (Eo1 Eo2 Ei : CoPset) :
    Eo1 ⊆ Eo2 →
    atomicUpdate Eo1 Ei α β Φ -∗ atomicUpdate Eo2 Ei α β Φ := by
  intro HE
  unfold atomicUpdate
  iintro HAU
  iapply greatest_fixpoint_coiter
    (Φ := fun _ : Unit => bi_greatest_fixpoint (atomicUpdatePre Eo1 Ei α β Φ) ())
  · iintro !> %u H
    cases u
    ihave H2 : atomicUpdatePre Eo1 Ei α β Φ
        (bi_greatest_fixpoint (atomicUpdatePre Eo1 Ei α β Φ)) () $$ [H]
    · iapply greatest_fixpoint_unfold_mp (F := atomicUpdatePre Eo1 Ei α β Φ) $$ H
    simp only [atomicUpdatePre]
    iapply atomicAcc_maskWeaken _ _ _ _ _ _ _ HE $$ H2
  · iexact HAU

@[rocq_alias aupd_unfold]
theorem aupd_unfold Eo Ei :
    atomicUpdate Eo Ei α β Φ ⊣⊢
    atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ := by
  unfold atomicUpdate atomicUpdatePre
  exact BI.equiv_iff.mp <| greatest_fixpoint_unfold (F := atomicUpdatePre Eo Ei α β Φ) (x := ())

@[rocq_alias aupd_aacc]
theorem aupd_aacc Eo Ei :
    atomicUpdate Eo Ei α β Φ ⊢
    atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ := by
  exact (aupd_unfold α β Φ Eo Ei).1

theorem aupd_acc Eo Ei E :
    Eo ⊆ E →
    atomicUpdate Eo Ei α β Φ -∗
    |={E,Ei}=> ∃.. x, α x ∗
      ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
       (∀.. y, β x y ={Ei,E}=∗ Φ x y)) := by
  intro HE
  iintro HAU
  ihave HAC : atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ $$ [HAU]
  · iapply aupd_aacc $$ HAU
  ihave HAC2 : atomicAcc E Ei α (atomicUpdate Eo Ei α β Φ) β Φ $$ [HAC]
  · iapply atomicAcc_maskWeaken Eo E Ei α (atomicUpdate Eo Ei α β Φ) β Φ HE $$ HAC
  unfold atomicAcc
  iexact HAC2

set_option synthInstance.checkSynthOrder false in
@[rocq_alias elim_mod_aupd]
instance elimModAupd φ Eo Ei E Q Q'
    [h : ∀ R, ProofMode.ElimModal φ false false iprop(|={E,Ei}=> R) R Q Q'] :
    ProofMode.ElimModal (φ ∧ Eo ⊆ E) false false
      (atomicUpdate Eo Ei α β Φ)
      iprop(∃.. x, α x ∗
        ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀.. y, β x y ={Ei,E}=∗ Φ x y)))
      Q Q' where
  elim_modal := by
    intro hc
    iintro ⟨HAU, Hcont⟩
    ihave HAC : atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ $$ [HAU]
    · iapply aupd_aacc $$ HAU
    ihave HAC2 : atomicAcc E Ei α (atomicUpdate Eo Ei α β Φ) β Φ $$ [HAC]
    ·
      iapply atomicAcc_maskWeaken Eo E Ei α (atomicUpdate Eo Ei α β Φ) β Φ hc.2 $$ HAC
    ihave Hfupd : |={E,Ei}=> ∃.. x, α x ∗
        ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀.. y, β x y ={Ei,E}=∗ Φ x y)) $$ [HAC2]
    · unfold atomicAcc
      iexact HAC2
    iapply ProofMode.ElimModal.elim_modal
      (φ := φ) (p := false) (p' := false)
      (P := iprop(|={E,Ei}=> ∃.. x, α x ∗
        ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀.. y, β x y ={Ei,E}=∗ Φ x y))))
      (P' := iprop(∃.. x, α x ∗
        ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀.. y, β x y ={Ei,E}=∗ Φ x y))))
      (Q := Q) (Q' := Q') hc.1
    isplitl [Hfupd]
    · iexact Hfupd
    · iexact Hcont

@[rocq_alias aupd_intro]
theorem aupd_intro (Q : PROP) Eo Ei :
    Absorbing P → Persistent P →
    (P ∧ Q ⊢ atomicAcc Eo Ei α Q β Φ) →
    P ∧ Q ⊢ atomicUpdate Eo Ei α β Φ := by
  intro _ _
  intro HAU
  unfold atomicUpdate atomicUpdatePre
  iintro Hpq
  icases Hpq with ⟨#HP, HQ⟩
  iapply greatest_fixpoint_coiter (Φ := fun _ : Unit => Q)
  · iintro !> %u HQ
    cases u
    iapply HAU
    isplit
    · iexact HP
    · iexact HQ
  · iexact HQ

@[rocq_alias aacc_intro]
theorem aacc_intro Eo Ei :
    Ei ⊆ Eo → ⊢@{PROP} ∀.. x, α x -∗
    ((α x ={Eo}=∗ P) ∧ (∀.. y, β x y ={Eo}=∗ Φ x y)) -∗
    atomicAcc Eo Ei α P β Φ := by
  intro hsub
  unfold atomicAcc
  iintro %x Hα Hclose
  iapply fupd_mask_intro hsub
  iintro Hmask
  iexists x
  iframe Hα
  isplit
  · iintro Hα
    imod Hmask
    icases Hclose with ⟨Hclose, -⟩
    iapply Hclose $$ Hα
  · iintro %y Hβ
    imod Hmask
    icases Hclose with ⟨-, Hclose⟩
    iapply Hclose $$ %y Hβ

#rocq_ignore elim_acc_aacc "ElimAcc and maybe-wand (`-∗?`) are not ported in Lean ProofMode yet."

set_option synthInstance.checkSynthOrder false in
@[rocq_alias elim_modal_acc]
instance elimModalAcc p q φ Eo Ei Pas Q Q'
    [h : ∀ R, ProofMode.ElimModal φ p q Q Q' iprop(|={Eo,Ei}=> R) iprop(|={Eo,Ei}=> R)] :
    ProofMode.ElimModal φ p q Q Q'
      (atomicAcc Eo Ei α Pas β Φ)
      (atomicAcc Eo Ei α Pas β Φ) where
  elim_modal := by
    intro hφ
    unfold atomicAcc
    exact ProofMode.ElimModal.elim_modal
      (φ := φ) (p := p) (p' := q) (P := Q) (P' := Q')
      (Q := iprop(|={Eo,Ei}=> ∃.. x, α x ∗ ((α x ={Ei, Eo}=∗ Pas) ∧ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y))))
      (Q' := iprop(|={Eo,Ei}=> ∃.. x, α x ∗ ((α x ={Ei, Eo}=∗ Pas) ∧ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y)))) hφ

@[rocq_alias aacc_aacc]
theorem aacc_aacc (E1 E1' E2 E3 : CoPset)
    (α' : TA → PROP) (P' : PROP) (β' Φ' : TA → TB → PROP) :
    E1' ⊆ E1 →
    atomicAcc E1' E2 α P β Φ -∗
    (∀ x, α x -∗ atomicAcc E2 E3 α' (iprop(α x ∗ (P ={E1}=∗ P'))) β'
      (fun x' y' => iprop((α x ∗ (P ={E1}=∗ Φ' x' y')) ∨
        ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
    atomicAcc E1 E3 α' P' β' Φ' := by
  intro HE
  iintro Hupd Hstep
  ihave Hupd2 : atomicAcc E1 E2 α P β Φ $$ [Hupd]
  · iapply atomicAcc_maskWeaken _ _ _ _ _ _ _ HE $$ Hupd
  simp only [atomicAcc]
  imod Hupd2 with ⟨%x, Hα, Hclose⟩
  imod Hstep $$ %x Hα with ⟨%x', Hα', Hclose'⟩
  imodintro
  iexists x'
  iframe Hα'
  isplit
  · iintro Hα'2
    icases Hclose' with ⟨Hclose', -⟩
    imod Hclose' $$ Hα'2 with ⟨Hα2, Hupd3⟩
    icases Hclose with ⟨Hclose, -⟩
    imod Hclose $$ Hα2 with HP
    iapply Hupd3 $$ HP
  · iintro %y' Hβ'
    icases Hclose' with ⟨-, Hclose'⟩
    imod Hclose' $$ %y' Hβ' with Hres
    icases Hres with ⟨⟨Hα2, HΦ'⟩ | ⟨%y, Hβ, HΦ'⟩⟩
    · icases Hclose with ⟨Hclose, -⟩
      imod Hclose $$ Hα2 with HP
      iapply HΦ' $$ HP
    · icases Hclose with ⟨-, Hclose⟩
      imod Hclose $$ %y Hβ with HΦ
      iapply HΦ' $$ HΦ
@[rocq_alias aacc_aupd]
theorem aacc_aupd (E1 E1' E2 E3 : CoPset)
    (α' : TA → PROP) (P' : PROP) (β' Φ' : TA → TB → PROP) :
    E1' ⊆ E1 →
    atomicUpdate E1' E2 α β Φ -∗
    (∀ x, α x -∗ atomicAcc E2 E3 α' (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P'))) β'
      (fun x' y' => iprop((α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ Φ' x' y')) ∨
        ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
    atomicAcc E1 E3 α' P' β' Φ' := by
  intro HE
  iintro Hupd Hstep
  ihave Haacc : atomicAcc E1' E2 α (atomicUpdate E1' E2 α β Φ) β Φ $$ [Hupd]
  · iapply aupd_aacc
    iassumption
  iapply aacc_aacc α β Φ (atomicUpdate E1' E2 α β Φ) E1 E1' E2 E3 α' P' β' Φ' HE $$ Haacc Hstep

@[rocq_alias aacc_aupd_commit]
theorem aacc_aupd_commit (E1 E1' E2 E3 : CoPset)
    (α' : TA → PROP) (P' : PROP) (β' Φ' : TA → TB → PROP) :
    E1' ⊆ E1 →
    atomicUpdate E1' E2 α β Φ -∗
    (∀ x, α x -∗ atomicAcc E2 E3 α' (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P'))) β'
      (fun x' y' => iprop(∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
    atomicAcc E1 E3 α' P' β' Φ' := by
  intro HE
  iintro Hupd Hstep
  iapply aacc_aupd α β Φ E1 E1' E2 E3 α' P' β' Φ' HE $$ Hupd
  iintro %x Hα
  iapply atomicAcc_wand α'
      (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P')))
      (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P')))
      β' E2 E3
      (fun x' y' => iprop(∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))
      (fun x' y' => iprop((α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ Φ' x' y')) ∨
        ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))
  · isplit
    · iintro H
      iexact H
    · iintro %x' %y' H
      iright
      iexact H
  · iapply Hstep $$ %x Hα

@[rocq_alias aacc_aupd_abort]
theorem aacc_aupd_abort (E1 E1' E2 E3 : CoPset)
    (α' : TA → PROP) (P' : PROP) (β' Φ' : TA → TB → PROP) :
    E1' ⊆ E1 →
    atomicUpdate E1' E2 α β Φ -∗
    (∀ x, α x -∗ atomicAcc E2 E3 α' (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P'))) β'
      (fun x' y' => iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ Φ' x' y')))) -∗
    atomicAcc E1 E3 α' P' β' Φ' := by
  intro HE
  iintro Hupd Hstep
  iapply aacc_aupd α β Φ E1 E1' E2 E3 α' P' β' Φ' HE $$ Hupd
  iintro %x Hα
  iapply atomicAcc_wand α'
      (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P')))
      (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P')))
      β' E2 E3
      (fun x' y' => iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ Φ' x' y')))
      (fun x' y' => iprop((α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ Φ' x' y')) ∨
        ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))
  · isplit
    · iintro H
      iexact H
    · iintro %x' %y' H
      ileft
      iexact H
  · iapply Hstep $$ %x Hα






end Lemmas

section ProofMode
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele}
variable (α : TA → PROP) (β Φ: TA → TB → PROP)

@[rocq_alias tac_aupd_intro]
theorem tacAupdIntro {Δ : PROP} Eo Ei :
    (Δ ⊢ atomicAcc Eo Ei α Δ β Φ) →
    Δ ⊢ atomicUpdate Eo Ei α β Φ := by
  intro Hacc
  iintro HΔ
  iapply aupd_intro (α := α) (β := β) (Φ := Φ)
    (P := iprop(True)) (Q := Δ)
  · infer_instance
  · infer_instance
  · exact and_elim_r.trans Hacc
  · isplit
    · itrivial
    · iexact HΔ

theorem tacAupdIntroExplicit (Δ : PROP) Eo Ei :
    (Δ ⊢ atomicAcc Eo Ei α Δ β Φ) →
    Δ ⊢ atomicUpdate Eo Ei α β Φ :=
  tacAupdIntro α β Φ Eo Ei

theorem tacAaccIntro {Δ Δ' : PROP} (P : PROP) Eo Ei x :
    Ei ⊆ Eo →
    (Δ ⊢ Δ' ∗ α x) →
    (Δ' ⊢ α x ={Eo}=∗ P) →
    (Δ' ⊢ ∀.. y, β x y ={Eo}=∗ Φ x y) →
    Δ ⊢ atomicAcc Eo Ei α P β Φ := by
  intro HE Hα Habort Hcommit
  iintro HΔ
  icases Hα $$ HΔ with ⟨HΔ', Hα⟩
  iapply aacc_intro α β Φ P Eo Ei HE $$ %x Hα
  isplit
  · iapply Habort $$ HΔ'
  · iapply Hcommit $$ HΔ'

open Lean Elab Tactic Meta Qq Std ProofMode

elab "iAuIntro" : tactic => do
  ProofModeM.runTactic λ mvar g => do
    let { prop, bi, hyps, goal, .. } := g
    let goal ← instantiateMVars goal
    let_expr atomicUpdate _ _ instFUpd TA TB Eo Ei α β Φ := goal |
      throwError "iAuIntro: goal is not an atomic update"
    let uTA := (← inferType TA).getAppFn.constLevels![0]!
    let uTB := (← inferType TB).getAppFn.constLevels![0]!
    let Δctx : Q($prop) := hyps.tm
    let accGoalExpr := mkAppN (mkConst ``atomicAcc [g.u, uTA, uTB])
      #[prop, bi, instFUpd, TA, TB, Eo, Ei, α, Δctx, β, Φ]
    let some accGoal ← checkTypeQ accGoalExpr prop |
      throwError "iAuIntro: internal error, malformed atomic accessor goal"
    let Hacc : Q($Δctx ⊢ $accGoal) ←
      mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr { g with goal := accGoal })
    modify fun s => { s with goals := s.goals.push Hacc.mvarId! }
    let HaccTy ← instantiateMVars (← inferType Hacc)
    let fn := HaccTy.getAppFn
    let args := HaccTy.getAppArgs
    let Δactual ←
      if (fn.isConstOf ``Entails') || (fn.isConstOf ``BIBase.Entails) then
        if h : 2 < args.size then
          pure args[2]
        else
          throwError "iAuIntro: internal error, malformed entailment"
      else
        throwError "iAuIntro: internal error, accessor subgoal is not an entailment"
    let pf ← mkAppM ``tacAupdIntroExplicit #[α, β, Φ, Δactual, Eo, Ei, Hacc]
    mvar.assign pf

elab "iAaccIntro" " with " h:ident : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse (← `(pmTerm| $h:ident))
  ProofModeM.runTactic λ mvar g => do
    let { prop, hyps, goal, .. } := g
    let goal ← instantiateMVars goal
    let_expr atomicAcc _ _ _ _ TB Eo Ei α P β Φ := goal |
      throwError "iAaccIntro: goal is not an atomic accessor"
    let uTB := (← inferType TB).getAppFn.constLevels![0]!
    let ⟨_, hyps', p, out, Hsel⟩ ← iHave hyps pmt false
    unless p.isConstOf ``false do
      throwError "iAaccIntro: selected hypothesis must be spatial"
    let outFn := out.getAppFn
    let outArgs := out.getAppArgs
    unless outArgs.size == 1 do
      throwError "iAaccIntro: selected hypothesis does not match the atomic precondition"
    unless ← isDefEq outFn α do
      throwError "iAaccIntro: selected hypothesis does not match the atomic precondition"
    let x := outArgs[0]!
    let some Eiq ← checkTypeQ Ei q(CoPset) |
      throwError "iAaccIntro: malformed atomic accessor inner mask"
    let some Eoq ← checkTypeQ Eo q(CoPset) |
      throwError "iAaccIntro: malformed atomic accessor outer mask"
    let Hsub : Q($Eiq ⊆ $Eoq) ← mkFreshExprSyntheticOpaqueMVar q($Eiq ⊆ $Eoq)
    let sideGoals ← evalTacticAt
      (← `(tactic| first | exact LawfulSet.empty_subset | assumption | trivial))
      Hsub.mvarId!
    for sideGoal in sideGoals do
      addMVarGoal sideGoal
    let αx := mkApp α x
    let fupdP ← mkAppM ``FUpd.fupd #[Eo, Eo, P]
    let abortGoal ← mkAppM ``BIBase.wand #[αx, fupdP]
    let yTy := mkApp (mkConst ``Tele.Arg [uTB]) TB
    let commitGoal ← withLocalDeclD `y yTy fun y => do
      let βxy := mkApp2 β x y
      let Φxy := mkApp2 Φ x y
      let fupdΦ ← mkAppM ``FUpd.fupd #[Eo, Eo, Φxy]
      let body ← mkAppM ``BIBase.wand #[βxy, fupdΦ]
      let lam ← mkLambdaFVars #[y] body
      mkAppM ``biTforall #[lam]
    let some abortGoal ← checkTypeQ abortGoal prop |
      throwError "iAaccIntro: internal error, malformed abort subgoal"
    let some commitGoal ← checkTypeQ commitGoal prop |
      throwError "iAaccIntro: internal error, malformed commit subgoal"
    let Habort ← addBIGoal hyps' abortGoal
    let Hcommit ← addBIGoal hyps' commitGoal
    let pf ← mkAppM ``tacAaccIntro #[α, β, Φ, P, Eo, Ei, x, Hsub, Hsel, Habort, Hcommit]
    mvar.assign pf
end ProofMode

end Iris
