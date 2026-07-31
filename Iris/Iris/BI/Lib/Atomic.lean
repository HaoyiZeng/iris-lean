module

public import Iris.BI
public import Iris.BI.Updates
public import Iris.BI.Telescopes
public import Iris.BI.Lib.Fixpoint
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
syntax "⟪ " ("∃ " ident ", ")? term " ⟫" : auPre

declare_syntax_cat auPost
syntax "⟪ " ("∀ " ident ", ")? term (", " "COMM " term)? " ⟫" : auPost

syntax (name := atomicUpdateNotation)
  "AU " ppRealFill(auPre ppSpace "@ " term ", " term ppSpace auPost) : term

macro_rules
  | `(AU ⟪ ∃ $x:ident, $α:term ⟫ @ $Eo:term, $Ei:term
        ⟪ ∀ $y:ident, $β:term, COMM $Φ:term ⟫) =>
      `(atomicUpdate (TA := Tele.cons (λ _ : _ => Tele.nil))
          (TB := Tele.cons (λ _ : _ => Tele.nil))
          $Eo $Ei
          (Tele.app <| λ $x => ULift.up iprop($α))
          (Tele.app <| λ $x => ULift.up <| Tele.app <| λ $y => ULift.up iprop($β))
          (Tele.app <| λ $x => ULift.up <| Tele.app <| λ $y => ULift.up iprop($Φ)))
  | `(AU ⟪ ∃ $x:ident, $α:term ⟫ @ $Eo:term, $Ei:term
        ⟪ $β:term, COMM $Φ:term ⟫) =>
      `(atomicUpdate (TA := Tele.cons (λ _ : _ => Tele.nil))
          (TB := Tele.nil)
          $Eo $Ei
          (Tele.app <| λ $x => ULift.up iprop($α))
          (Tele.app <| λ $x => ULift.up <| Tele.app (ULift.up iprop($β)))
          (Tele.app <| λ $x => ULift.up <| Tele.app (ULift.up iprop($Φ))))
  | `(AU ⟪ $α:term ⟫ @ $Eo:term, $Ei:term
        ⟪ ∀ $y:ident, $β:term, COMM $Φ:term ⟫) =>
      `(atomicUpdate (TA := Tele.nil)
          (TB := Tele.cons (λ _ : _ => Tele.nil))
          $Eo $Ei
          (Tele.app (ULift.up iprop($α)))
          (Tele.app <| ULift.up <| Tele.app <| λ $y => ULift.up iprop($β))
          (Tele.app <| ULift.up <| Tele.app <| λ $y => ULift.up iprop($Φ)))
  | `(AU ⟪ $α:term ⟫ @ $Eo:term, $Ei:term
        ⟪ $β:term, COMM $Φ:term ⟫) =>
      `(atomicUpdate (TA := Tele.nil)
          (TB := Tele.nil)
          $Eo $Ei
          (Tele.app (ULift.up iprop($α)))
          (Tele.app (ULift.up <| Tele.app (ULift.up iprop($β))))
          (Tele.app (ULift.up <| Tele.app (ULift.up iprop($Φ)))))

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

@[rocq_alias elim_mod_aupd]
instance elimModAupd (Eo Ei E E3 : CoPset) (Q0 : PROP) :
    ProofMode.ElimModal (Eo ⊆ E) false false
      (atomicUpdate Eo Ei α β Φ)
      iprop(∃.. x, α x ∗
        ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀.. y, β x y ={Ei,E}=∗ Φ x y)))
      iprop(|={E,E3}=> Q0)
      iprop(|={Ei,E3}=> Q0) where
  elim_modal := by
    intro hEo
    iintro ⟨HAU, Hcont⟩
    ihave Hfupd : |={E,Ei}=> ∃.. x, α x ∗
        ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀.. y, β x y ={Ei,E}=∗ Φ x y)) $$ [HAU]
    · iapply aupd_acc α β Φ Eo Ei E hEo $$ HAU
    imod Hfupd with Hacc
    iapply Hcont $$ Hacc

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

/-- Weakening the *commit* condition of an atomic accessor.  Handing the holder a
    harder obligation `β'` is sound as long as discharging it also discharges the
    obligation `β` we owe ourselves. -/
theorem atomicAcc_mono_commit (β' : TA → TB → PROP) Eo Ei
    (h : ∀ x y, β' x y ⊢ β x y) :
    atomicAcc Eo Ei α P β Φ ⊢ atomicAcc Eo Ei α P β' Φ := by
  simp only [atomicAcc]
  iintro Hacc
  imod Hacc with ⟨%x, Hα, Hclose⟩
  imodintro
  iexists x
  iframe Hα
  isplit
  · icases Hclose with ⟨Habort, -⟩
    iexact Habort
  · icases Hclose with ⟨-, Hcommit⟩
    iintro %y Hβ'
    ihave Hβ := h x y $$ Hβ'
    iapply Hcommit $$ %y Hβ

/-- Same, one level up: an atomic *update* whose commit condition is `β` can be used
    wherever one with the harder commit condition `β'` is expected. -/
theorem aupd_mono_commit (β' : TA → TB → PROP) Eo Ei
    (h : ∀ x y, β' x y ⊢ β x y) :
    atomicUpdate Eo Ei α β Φ ⊢ atomicUpdate Eo Ei α β' Φ := by
  iintro HAU
  iapply aupd_intro (α := α) (β := β') (Φ := Φ) (P := iprop(True))
    (atomicUpdate Eo Ei α β Φ) Eo Ei inferInstance inferInstance ?_
  · iintro HQ
    icases HQ with ⟨-, HQ⟩
    iapply atomicAcc_mono_commit (α := α) (β := β) (Φ := Φ)
      (P := atomicUpdate Eo Ei α β Φ) β' Eo Ei h
    iapply aupd_aacc $$ HQ
  · isplit
    · itrivial
    · iexact HAU

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
theorem aacc_aacc {TA' TB' : Tele} (E1 E1' E2 E3 : CoPset)
    (α' : TA' → PROP) (P' : PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomicAcc E1' E2 α P β Φ -∗
    (∀.. x, α x -∗ atomicAcc E2 E3 α' (iprop(α x ∗ (P ={E1}=∗ P'))) β'
      (fun x' y' => iprop((α x ∗ (P ={E1}=∗ Φ' x' y')) ∨
        ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y')))) -∗
    atomicAcc E1 E3 α' P' β' Φ' := by
  intro HE
  iintro Hupd Hstep
  ihave Hstep := (biTforall_forall _).mp $$ Hstep
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
theorem aacc_aupd {TA' TB' : Tele} (E1 E1' E2 E3 : CoPset)
    (α' : TA' → PROP) (P' : PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomicUpdate E1' E2 α β Φ -∗
    (∀.. x, α x -∗ atomicAcc E2 E3 α' (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P'))) β'
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
theorem aacc_aupd_commit {TA' TB' : Tele} (E1 E1' E2 E3 : CoPset)
    (α' : TA' → PROP) (P' : PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomicUpdate E1' E2 α β Φ -∗
    (∀.. x, α x -∗ atomicAcc E2 E3 α' (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P'))) β'
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
theorem aacc_aupd_abort {TA' TB' : Tele} (E1 E1' E2 E3 : CoPset)
    (α' : TA' → PROP) (P' : PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomicUpdate E1' E2 α β Φ -∗
    (∀.. x, α x -∗ atomicAcc E2 E3 α' (iprop(α x ∗ (atomicUpdate E1' E2 α β Φ ={E1}=∗ P'))) β'
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

elab "iauintro" : tactic => do
  ProofModeM.runTactic λ mvar g => do
    let { prop, bi, hyps, goal, .. } := g
    let goal ← instantiateMVars goal
    let_expr atomicUpdate _ _ instFUpd TA TB Eo Ei α β Φ := goal |
      throwError "iauintro: goal is not an atomic update"
    let uTA := (← inferType TA).getAppFn.constLevels![0]!
    let uTB := (← inferType TB).getAppFn.constLevels![0]!
    let Δctx : Q($prop) := hyps.tm
    let accGoalExpr := mkAppN (mkConst ``atomicAcc [g.u, uTA, uTB])
      #[prop, bi, instFUpd, TA, TB, Eo, Ei, α, Δctx, β, Φ]
    let some accGoal ← checkTypeQ accGoalExpr prop |
      throwError "iauintro: internal error, malformed atomic accessor goal"
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
          throwError "iauintro: internal error, malformed entailment"
      else
        throwError "iauintro: internal error, accessor subgoal is not an entailment"
    let pf ← mkAppM ``tacAupdIntroExplicit #[α, β, Φ, Δactual, Eo, Ei, Hacc]
    mvar.assign pf

elab "iaaccintro" " with " h:ident : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse (← `(pmTerm| $h:ident))
  ProofModeM.runTactic λ mvar g => do
    let { prop, hyps, goal, .. } := g
    let goal ← instantiateMVars goal
    let_expr atomicAcc _ _ _ _ TB Eo Ei α P β Φ := goal |
      throwError "iaaccintro: goal is not an atomic accessor"
    let uTB := (← inferType TB).getAppFn.constLevels![0]!
    let ⟨_, hyps', p, out, Hsel⟩ ← iHave hyps pmt false
    unless p.isConstOf ``false do
      throwError "iaaccintro: selected hypothesis must be spatial"
    let outFn := out.getAppFn
    let outArgs := out.getAppArgs
    unless outArgs.size == 1 do
      throwError "iaaccintro: selected hypothesis does not match the atomic precondition"
    unless ← isDefEq outFn α do
      throwError "iaaccintro: selected hypothesis does not match the atomic precondition"
    let x := outArgs[0]!
    let some Eiq ← checkTypeQ Ei q(CoPset) |
      throwError "iaaccintro: malformed atomic accessor inner mask"
    let some Eoq ← checkTypeQ Eo q(CoPset) |
      throwError "iaaccintro: malformed atomic accessor outer mask"
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
      throwError "iaaccintro: internal error, malformed abort subgoal"
    let some commitGoal ← checkTypeQ commitGoal prop |
      throwError "iaaccintro: internal error, malformed commit subgoal"
    let Habort ← addBIGoal hyps' abortGoal
    let Hcommit ← addBIGoal hyps' commitGoal
    let pf ← mkAppM ``tacAaccIntro #[α, β, Φ, P, Eo, Ei, x, Hsub, Hsel, Habort, Hcommit]
    mvar.assign pf
end ProofMode

section Delab
public meta section
open Lean PrettyPrinter Delaborator SubExpr

/-- Reduce `Tele.app`-applications that can make progress, faithfully to Rocq's
`Arguments tele_app … !_ /`. This fires when either the telescope argument is a
*constructor* (`⟨_, _⟩` / `PUnit.unit`), **or** the telescope itself is `Tele.nil`
— because `Tele.app` over `nil` ignores its argument (`nil => λ f _ => f.down`),
so `Tele.app { down := X } s` reduces to `X` even when `s` is a bare variable
(e.g. a spuriously-introduced `Tele.nil.Arg` witness). Unapplied components
(`Tele.app (fun x => ..)` over a `cons`) and variable `cons`-arguments are left
untouched — so notations still print and, once a telescope binder is destructed
(`⟨n, _⟩`), applications like `α ⟨n, _⟩` reduce straight to their body. Reduction
stops at the first user-level head (via `whnfHeadPred`), so predicates like `↦`
are not unfolded; residual `⟨n, _⟩.fst` / `.snd` projections (produced by the
matcher) are reduced too. -/
public partial def reduceTeleApps (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun n => do
    if n.isAppOf ``Tele.app && n.getAppNumArgs ≥ 4 &&
        (let a := n.getAppArgs[3]!
         let tt := n.getAppArgs[0]!
         tt.isConstOf ``Tele.nil || a.isAppOf ``Sigma.mk || a.isConstOf ``PUnit.unit) then
      return .visit <| ← Meta.whnfHeadPred n fun h => do
        match h.getAppFn with
        | .const c _ => return c == ``Tele.app || c == ``ULift.up || c == ``ULift.down
        | _ => return true
    else if n.isProj then
      -- reduce residual `⟨_, _⟩.fst` structure projections
      return .visit (← Meta.whnfCore n)
    else if n.isAppOf ``ULift.down && n.getAppNumArgs ≥ 1 && n.appArg!.isAppOf ``ULift.up then
      -- `ULift.down (ULift.up x)` ↦ `x`
      return .visit n.appArg!.appArg!
    else if (n.isAppOf ``Sigma.fst || n.isAppOf ``Sigma.snd) && n.isApp &&
        n.appArg!.isAppOf ``Sigma.mk && n.appArg!.getAppNumArgs == 4 then
      return .done n.appArg!.getAppArgs[if n.isAppOf ``Sigma.fst then 2 else 3]!
    else if n.getAppFn.constName? == some `Iris.wandM && n.getAppNumArgs == 4 &&
        n.getAppArgs[2]!.isAppOf ``Option.none then
      -- `none -∗? Q` (the Lean analogue of Rocq's `maybe_wand None`, reduced by
      -- `cbn [maybe_wand]`) reduces to `Q`.
      return .visit n.getAppArgs[3]!
    else
      return .continue)

/-- Peel the binder names of a *single* telescope `T` off the component `g`,
returning one name per `Tele.cons` level together with the residual body.
Telescopes deeper than one level (e.g. `⟪ ∀ x, ∀ y, … ⟫`) consume one lambda
binder per level, so a flat `one name per telescope` walk would mis-align the
names of the following component. -/
public partial def teleNamesOne (g T : Expr) : List Name × Expr :=
  let g := if g.isAppOf ``Tele.app then g.getAppArgs[2]! else g
  if T.isAppOf ``Tele.cons then
    match g with
    | .lam nm _ body _ =>
      let body := if body.isAppOf ``ULift.up then body.appArg! else body
      -- descend into the tail telescope `β x`; we only inspect its head symbol,
      -- so the loose bvar left by opening the lambda is harmless
      let tail := match T.getAppArgs[1]! with | .lam _ _ tb _ => tb | β => β
      let (nms, rest) := teleNamesOne body tail
      (nm :: nms, rest)
    | _ => ([], g)
  else
    let inner := if g.isAppOf ``ULift.up then g.appArg! else g
    ([], inner)

/-- Extract the ordinary binder names of a telescope-function component from its
*original* (un-reduced) structure, one per `Tele.cons` level of `Ts` (nil levels
contribute none). Used to keep binder names stable and consistent across
`α`/`β`/`Φ`, unaffected by later reduction/α-renaming. -/
public partial def teleNames : Expr → List Expr → List Name
  | _, [] => []
  | comp, T :: Ts =>
    let (nms, rest) := teleNamesOne comp T
    nms ++ teleNames rest Ts

-- A single proof-mode reduction tactic (Lean analogue of Rocq's `pm_prettify`):
-- reduce the constructor-applied telescope functions in the goal so tactics like
-- `iapply` can use them, while keeping unapplied components (so `AU`/`atomicWP`
-- notations still print). This changes the goal to a definitionally-equal form.
open Lean.Elab.Tactic in
elab "itele_reduce_apps" : tactic =>
  liftMetaTactic1 fun mvar => do
    return some (← mvar.change (← reduceTeleApps (← instantiateMVars (← mvar.getType))))

/-- Proof-mode normalisation tactic, the Lean analogue of Rocq's `pm_prettify`
(`cbn [tele_app bi_texist bi_tforall …]`). It (a) peels telescopic quantifiers
`∃..`/`∀..` over *concrete* telescopes into plain `∃`/`∀` with the packed `PUnit`
tail substituted (via `biTexist_cons/nil`, `biTforall_cons/nil`), so no
`Sigma`/`PUnit` witness leaks into `icases`/`ispecialize`; and (b) reduces the
constructor-applied telescope functions in the goal so tactics like `iapply` can
use them, while keeping unapplied components (so `AU`/`atomicWP` notations still
print). Both steps preserve definitional equality; the peeling `simp only` is
wrapped in `try` so the tactic is a no-op when nothing matches. -/
macro "itele_reduce" : tactic =>
  `(tactic|
    (try simp only [biTexist_cons, biTexist_nil, biTforall_cons, biTforall_nil]
     itele_reduce_apps))

/-- `iauopen h with pat` opens a client *atomic update* `h`: it eliminates the
update's outer fupd (`imod`) and destructs the result with `pat`, then immediately
normalizes the telescope-encoded `α` (`itele_reduce`) so the exposed `α x` carries
no `Tele.app`. This mirrors Rocq's `iMod "AU" as (x) "[Hα Hclose]"`, whose
telescope smart-intro yields a clean `∃ x, α x ∗ (abort ∧ commit)`.

Opening an atomic update is the *only* place a proof needs `itele_reduce`, so this
is the idiomatic way to do it; use plain `imod` for ordinary modalities. -/
macro "iauopen" colGt pmt:pmTerm " with " colGt pat:icasesPat : tactic =>
  `(tactic| (imod $pmt with $pat; itele_reduce))

macro "iauopen" colGt pmt:pmTerm : tactic =>
  `(tactic| (imod $pmt; itele_reduce))

/-- Peel a telescope-function component (`α`, `β`, `Φ`, ...) along the telescope
list `Ts`, by *applying* it to constructor arguments built from fresh ordinary
binders (Rocq's `λ..`: packed binder → ordinary binder). The result is reduced,
so an inlined `POST x y z` / `f x y z` collapses to its clean body with ordinary
binder names — no `Tele.app`/`{down}` leaks. `Tele.nil` levels contribute no
binder. Handles both the notation form `Tele.app (fun x => ULift.up _)` and the
plain `fun x => _` form (from `atomicWP`). Telescopes of *any* depth are handled;
each `Tele.cons` level contributes one ordinary binder. -/
public partial def buildTeleArg {α : Type} (argTy g : Expr) (names : List Name)
    (k : Array Name → List Name → Expr → MetaM α) : MetaM α := do
  let argTy ← Meta.whnf argTy
  if argTy.isAppOf ``Sigma then
    -- `Tele.Arg (cons X β) = Σ x : X, Tele.Arg (β x)`: introduce a binder for `x`
    -- and recurse into the tail, which for a multi-level telescope is another
    -- `Sigma` rather than `PUnit`.
    let X := argTy.getAppArgs[0]!
    let β := argTy.getAppArgs[1]!
    let g := if g.isAppOf ``Tele.app then g.getAppArgs[2]! else g
    let nm := names.head?.getD <| match g with | .lam n .. => n | _ => `x
    Meta.withLocalDeclD nm X fun fv => do
      let gBody :=
        let b := g.beta #[fv]
        if b.isAppOf ``ULift.up then b.appArg! else b
      buildTeleArg (β.beta #[fv]) gBody names.tail fun nms rest tail => do
        let arg ← Meta.mkAppOptM ``Sigma.mk #[X, β, fv, tail]
        k (#[← fv.fvarId!.getUserName] ++ nms) rest arg
  else
    match argTy.getAppFn with
    | .const ``PUnit us => k #[] names (mkConst ``PUnit.unit us)
    | _ => throwError "peelComp: expected `PUnit` at the end of a telescope, got {argTy}"

public partial def peelComp {α : Type} (comp : Expr) (Ts : List Expr) (names : List Name)
    (k : Array Name → Expr → MetaM α) : MetaM α := do
  let comp ← reduceTeleApps comp
  match Ts with
  | [] => k #[] comp
  | T :: Ts =>
    let dom ← Meta.whnf (← Meta.inferType comp)
    let argTy ← Meta.whnf dom.bindingDomain!
    if (← Meta.whnf T).isConstOf ``Tele.nil then
      -- `argTy` is `PUnit.{v}`; apply `comp` to `PUnit.unit` (nil consumes no binder name)
      match argTy.getAppFn with
      | .const ``PUnit us => peelComp (comp.beta #[mkConst ``PUnit.unit us]) Ts names k
      | _ => throwError "peelComp: expected `PUnit` for a nil telescope, got {argTy}"
    else
      let g := if comp.isAppOf ``Tele.app then comp.getAppArgs[2]! else comp
      buildTeleArg argTy g names fun nms rest arg =>
        peelComp (comp.beta #[arg]) Ts rest fun nms' body =>
          k (nms ++ nms') body

/-- Peel a component and delaborate its reduced body, returning the ordinary
binder names and the body syntax. `names` overrides the derived binder names at
`cons` levels (used to keep binder names consistent across `α`/`β`/`Φ`). -/
public def peelDelab (comp : Expr) (Ts : List Expr) (names : List Name := []) :
    MetaM (Array Name × Term) :=
  peelComp comp Ts names fun nms body => do
    return (nms, ← unpackIprop (← Lean.PrettyPrinter.delab body))
/-- Shared peeling for `delabAtomicUpdate`/`delabAtomicAcc`. From the argument
array of an `atomicUpdate`/`atomicAcc` application, peel the telescope-encoded
`α`/`β`/`Φ` at the given indices and build the display fragments `∃ x, α` / `∀ y, β`
(or bare `α`/`β` for `nil` telescopes), returning `(Eo, Ei, pre, comm, Φ)`. Fails
(→ default printer) on abstract telescopes, where `peelDelab` cannot peel. -/
def peelAtomicParts (args : Array Expr) (αIdx βIdx ΦIdx : Nat) :
    DelabM (Term × Term × Term × Term × Term) := do
  let TA := args[3]!
  let TB := args[4]!
  unless (TA.isConstOf ``Tele.nil || TA.isAppOf ``Tele.cons) &&
         (TB.isConstOf ``Tele.nil || TB.isAppOf ``Tele.cons) do failure
  let Eo ← withNaryArg 5 delab
  let Ei ← withNaryArg 6 delab
  let αNames := teleNames args[αIdx]! [TA]
  -- reuse the pre binder names for the COMM component (`Φ`), which comes from the
  -- `atomicWP` definition and would otherwise use its own binder names.
  let βNames := teleNames args[βIdx]! [TA, TB]
  let (αn, α) ← peelDelab args[αIdx]! [TA] αNames
  let (βn, β) ← peelDelab args[βIdx]! [TA, TB] βNames
  let (_, Φ) ← peelDelab args[ΦIdx]! [TA, TB] βNames
  let taCons := !(TA.isConstOf ``Tele.nil)
  let tbCons := !(TB.isConstOf ``Tele.nil)
  -- `αn` holds one name per `cons` level of `TA`, `βn` the names of `TA` followed by
  -- those of `TB`; emit one binder each so multi-level telescopes print in full.
  let mut pre := α
  if taCons then
    for nm in αn.reverse do
      pre ← `(∃ $(mkIdent nm):ident, $pre)
  let mut comm := β
  if tbCons then
    for nm in (βn.extract αn.size βn.size).reverse do
      comm ← `(∀ $(mkIdent nm):ident, $comm)
  return (Eo, Ei, pre, comm, Φ)

@[delab app.Iris.atomicUpdate]
def delabAtomicUpdate : Delab := do
  let e ← getExpr
  unless e.getAppFn.isConstOf ``atomicUpdate do failure
  let args := e.getAppArgs
  unless args.size == 10 do failure
  let (Eo, Ei, pre, comm, Φ) ← peelAtomicParts args 7 8 9
  `(AU ⟪ $pre ⟫ @ $Eo, $Ei ⟪ $comm, COMM $Φ ⟫)

/-- Display syntax for an atomic accessor (analogue of the `AU⟪…⟫` notation for
atomic updates). Emitted only by `delabAtomicAcc` for readable proof states. -/
syntax "AACC " "⟪ " term " ⟫" ppSpace "@ " term ", " term ppSpace "⟪ " term ", " "COMM " term ppSpace "ABORT " term " ⟫" : term

/-- Pretty-print `atomicAcc Eo Ei α P β Φ` as
`AACC⟪ α ⟫ @ Eo, Ei ⟪ β, COMM Φ ABORT P ⟫`, peeling the telescope encoding (via
`peelAtomicParts`) and stripping the `iprop(…)` wrapper on the abort target `P`,
so no `Tele.app` / `{down := …}` / `iprop(…)` clutter appears in accessor goals.
Companion to `delabAtomicUpdate`; falls back to the default printer on abstract
telescopes. -/
@[delab app.Iris.atomicAcc]
def delabAtomicAcc : Delab := do
  let e ← getExpr
  unless e.getAppFn.isConstOf ``atomicAcc do failure
  let args := e.getAppArgs
  unless args.size == 11 do failure
  let P ← unpackIprop (← withNaryArg 8 delab)
  let (Eo, Ei, pre, comm, Φ) ← peelAtomicParts args 7 9 10
  `(AACC ⟪ $pre ⟫ @ $Eo, $Ei ⟪ $comm, COMM $Φ ABORT $P ⟫)
end
end Delab

end Iris
