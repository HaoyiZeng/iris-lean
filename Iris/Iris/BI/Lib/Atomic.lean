module

public import Iris.BI
public import Iris.Std.Delab
public import Iris.BI.Updates
public import Iris.BI.Lib.Fixpoint
public meta import Iris.ProofMode.Tactics

@[expose] public section
namespace Iris

open Iris.OFE BI ProofMode

/-! Packed atomic updates. The core is ported from the working packed implementation.
    Shared delaboration helpers live in `Iris.Std.Delab`, adapted from Aeneas. -/

section Definitions
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

@[rocq_alias atomic_acc]
def atomicAcc {A B : Type _} (Eo Ei : CoPset)
    (α : A → PROP) (P : PROP) (β Φ : A → B → PROP) : PROP :=
  iprop(|={Eo,Ei}=> ∃ x, α x ∗ ((α x ={Ei,Eo}=∗ P) ∧ (∀ y, β x y ={Ei,Eo}=∗ Φ x y)))

@[rocq_alias atomic_update_pre_mono]
instance atomicAccMono {A B : Type _} (Eo Ei : CoPset)
    (α : A → PROP) (β Φ : A → B → PROP) :
    BIMonoPred (PROP := PROP) (A := Unit)
      (fun Ψ (_ : Unit) => atomicAcc Eo Ei α (Ψ ()) β Φ) where
  mono_pred := by
    intro Ψ Ψ' _ _
    iintro #Hmono %u H
    simp only [atomicAcc] at *
    imod H with ⟨%x, Hα, Hclose⟩
    imodintro
    iexists x
    isplitl [Hα]
    · iexact Hα
    · isplit
      · iintro Hα'
        icases Hclose with ⟨Habort, -⟩
        imod Habort $$ Hα' with HP
        imodintro
        iapply Hmono $$ HP
      · iapply and_elim_r $$ Hclose
  mono_pred_ne := by infer_instance

@[rocq_alias atomic_update]
def atomicUpdate {A B : Type _} (Eo Ei : CoPset)
    (α : A → PROP) (β Φ : A → B → PROP) : PROP :=
  bi_greatest_fixpoint (fun Ψ (_ : Unit) => atomicAcc Eo Ei α (Ψ ()) β Φ) ()

end Definitions

section Notation
open Lean

meta partial def buildAuLam (xs : List Ident) (body : Term) : MacroM Term := do
  let u := mkIdent ``auUncurry
  match xs with
  | []        => `(fun (_ : Unit) => $body)
  | [x]       => `(fun $x => $body)
  | [a, b]    => `($u (fun $a $b => $body))
  | a :: rest => do `($u (fun $a => $(← buildAuLam rest body)))

declare_syntax_cat auPre
declare_syntax_cat auPost
syntax "⟪ " ("∃ " ident+ ", ")? term " ⟫" : auPre
syntax "⟪ " ("∀ " ident+ ", ")? term ", " "COMM " term " ⟫" : auPost

syntax (name := atomicUpdateNotation)
  "AU " ppRealFill(auPre ppSpace "@ " term ", " term ppSpace auPost) : term

macro_rules
  | `(AU ⟪ $[∃ $xs* , ]? $α:term ⟫ @ $Eo:term, $Ei:term
        ⟪ $[∀ $ys* , ]? $β:term, COMM $Φ:term ⟫) => do
      let xs : List Ident := (xs.map (·.toList)).getD []
      let ys : List Ident := (ys.map (·.toList)).getD []
      let mkOuter (inner : Term) : MacroM Term := buildAuLam xs inner
      let mkInner (b : Term) : MacroM Term := do buildAuLam xs (← buildAuLam ys b)
      `(atomicUpdate $Eo $Ei
          $(← mkOuter (← `(iprop($α))))
          $(← mkInner (← `(iprop($β))))
          $(← mkInner (← `(iprop($Φ)))))

end Notation


section Delab
public meta section
open Lean PrettyPrinter Delaborator SubExpr

def delabAuFamily : DelabM (Array Term × Term) :=
  Iris.Delab.enterUncurryChain #[] fun entries =>
    Iris.Delab.delabBinders entries.toList delab

def toIdents (ts : Array Term) : DelabM (Array Ident) :=
  ts.mapM fun t => if t.raw.isIdent then pure ⟨t.raw⟩ else failure

@[delab app.Iris.atomicUpdate]
def delabAtomicUpdate : Delab := do
  guard <| (← getExpr).isAppOfArity ``atomicUpdate 10
  let Eo ← withNaryArg 5 delab
  let Ei ← withNaryArg 6 delab
  let (preT, aBody) ← withNaryArg 7 delabAuFamily
  let (allT, bBody) ← withNaryArg 8 delabAuFamily
  let (_, fBody) ← withNaryArg 9 delabAuFamily
  let pre ← toIdents preT
  let post ← toIdents (allT.extract preT.size allT.size)
  let preStx ← if pre.isEmpty then `(auPre| ⟪ $aBody ⟫)
                              else `(auPre| ⟪ ∃ $pre*, $aBody ⟫)
  let postStx ← if post.isEmpty then `(auPost| ⟪ $bBody, COMM $fBody ⟫)
                                else `(auPost| ⟪ ∀ $post*, $bBody, COMM $fBody ⟫)
  `(AU $preStx:auPre @ $Eo, $Ei $postStx:auPost)

end
end Delab

section Lemmas
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {A B : Type _}
variable (α : A → PROP) (β Φ : A → B → PROP) (P : PROP)


@[rocq_alias atomic_acc_wand]
theorem atomicAcc_wand {A B : Type _} α (P1 P2 : PROP) β Eo Ei (Φ1 Φ2 : A → B → PROP) :
  ((P1 -∗ P2) ∧ (∀ x y, (Φ1 x y -∗ Φ2 x y)) -∗
  (atomicAcc Eo Ei α P1 β Φ1 -∗ atomicAcc Eo Ei α P2 β Φ2)) := by
  iintro Hwand Hatomic
  simp only [atomicAcc]
  imod Hatomic with ⟨%x, Hα, Hclose⟩
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
theorem atomicAcc_mask {A B : Type _} (Eo Ed : CoPset) α (P : PROP) β (Φ : A → B → PROP) :
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
theorem atomicAcc_maskWeaken {A B : Type _} (Eo1 Eo2 Ei : CoPset) α (P : PROP) β (Φ : A → B → PROP) :
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

@[rocq_alias atomic_acc_ne]
theorem atomicAcc_ne Eo Ei {n}
    {α1 α2 : A → PROP} {P1 P2 : PROP}
    {β1 β2 Φ1 Φ2 : A → B → PROP} :
    (∀ x, α1 x ≡{n}≡ α2 x) →
    P1 ≡{n}≡ P2 →
    (∀ x y, β1 x y ≡{n}≡ β2 x y) →
    (∀ x y, Φ1 x y ≡{n}≡ Φ2 x y) →
    atomicAcc Eo Ei α1 P1 β1 Φ1 ≡{n}≡
      atomicAcc Eo Ei α2 P2 β2 Φ2 := by
  intro Hα HP Hβ HΦ
  unfold atomicAcc
  refine BIFUpdate.ne.ne ?_
  refine exists_ne fun x => ?_
  refine sep_ne.ne (Hα x) ?_
  refine and_ne.ne ?_ ?_
  · refine wand_ne.ne (Hα x) ?_
    exact BIFUpdate.ne.ne HP
  · refine forall_ne fun y => ?_
    refine wand_ne.ne (Hβ x y) ?_
    exact BIFUpdate.ne.ne (HΦ x y)

instance atomicAcc_ne_inst Eo Ei : NonExpansive (atomicAcc Eo Ei α P β) where
  ne {_ _ _} HΦ := atomicAcc_ne Eo Ei (fun _ => .rfl) .rfl (fun _ _ => .rfl) HΦ

@[rocq_alias atomic_update_ne]
theorem atomicUpdate_ne Eo Ei {n}
    {α1 α2 : A → PROP} {β1 β2 Φ1 Φ2 : A → B → PROP} :
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
    (Φ := fun _ : Unit => bi_greatest_fixpoint
      (fun Ψ (_ : Unit) => atomicAcc Eo1 Ei α (Ψ ()) β Φ) ())
  · iintro !> %u H
    cases u
    ihave H2 : atomicAcc Eo1 Ei α
        (bi_greatest_fixpoint (fun Ψ (_ : Unit) => atomicAcc Eo1 Ei α (Ψ ()) β Φ) ()) β Φ $$ [H]
    · iapply greatest_fixpoint_unfold_mp
        (F := fun Ψ (_ : Unit) => atomicAcc Eo1 Ei α (Ψ ()) β Φ) $$ H
    iapply atomicAcc_maskWeaken _ _ _ _ _ _ _ HE $$ H2
  · iexact HAU

@[rocq_alias aupd_unfold]
theorem aupd_unfold Eo Ei :
    atomicUpdate Eo Ei α β Φ ⊣⊢
    atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ := by
  unfold atomicUpdate
  exact BI.equiv_iff.mp <| greatest_fixpoint_unfold (F := fun Ψ (_ : Unit) => atomicAcc Eo Ei α (Ψ ()) β Φ) (x := ())

@[rocq_alias aupd_aacc]
theorem aupd_aacc Eo Ei :
    atomicUpdate Eo Ei α β Φ ⊢
    atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ := by
  exact (aupd_unfold α β Φ Eo Ei).1

theorem aupd_acc Eo Ei E :
    Eo ⊆ E →
    atomicUpdate Eo Ei α β Φ -∗
    |={E,Ei}=> ∃ x, α x ∗
      ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
       (∀ y, β x y ={Ei,E}=∗ Φ x y)) := by
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
      iprop(∃ x, α x ∗
        ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀ y, β x y ={Ei,E}=∗ Φ x y)))
      iprop(|={E,E3}=> Q0)
      iprop(|={Ei,E3}=> Q0) where
  elim_modal := by
    intro hEo
    iintro ⟨HAU, Hcont⟩
    ihave Hfupd : |={E,Ei}=> ∃ x, α x ∗
        ((α x ={Ei,E}=∗ atomicUpdate Eo Ei α β Φ) ∧
        (∀ y, β x y ={Ei,E}=∗ Φ x y)) $$ [HAU]
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
  unfold atomicUpdate
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
theorem atomicAcc_mono_commit (β' : A → B → PROP) Eo Ei
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
theorem aupd_mono_commit (β' : A → B → PROP) Eo Ei
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
    Ei ⊆ Eo → ⊢@{PROP} ∀ x, α x -∗
    ((α x ={Eo}=∗ P) ∧ (∀ y, β x y ={Eo}=∗ Φ x y)) -∗
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
      (Q := iprop(|={Eo,Ei}=> ∃ x, α x ∗ ((α x ={Ei, Eo}=∗ Pas) ∧ (∀ y, β x y ={Ei, Eo}=∗ Φ x y))))
      (Q' := iprop(|={Eo,Ei}=> ∃ x, α x ∗ ((α x ={Ei, Eo}=∗ Pas) ∧ (∀ y, β x y ={Ei, Eo}=∗ Φ x y)))) hφ

@[rocq_alias aacc_aacc]
theorem aacc_aacc {A' B' : Type _} (E1 E1' E2 E3 : CoPset)
    (α' : A' → PROP) (P' : PROP) (β' Φ' : A' → B' → PROP) :
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
theorem aacc_aupd {A' B' : Type _} (E1 E1' E2 E3 : CoPset)
    (α' : A' → PROP) (P' : PROP) (β' Φ' : A' → B' → PROP) :
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
theorem aacc_aupd_commit {A' B' : Type _} (E1 E1' E2 E3 : CoPset)
    (α' : A' → PROP) (P' : PROP) (β' Φ' : A' → B' → PROP) :
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
theorem aacc_aupd_abort {A' B' : Type _} (E1 E1' E2 E3 : CoPset)
    (α' : A' → PROP) (P' : PROP) (β' Φ' : A' → B' → PROP) :
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
variable {A B : Type _}
variable (α : A → PROP) (β Φ : A → B → PROP)

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

theorem tacAupdIntroExplicitPM (Δ : PROP) Eo Ei :
    ProofMode.Entails' Δ (atomicAcc Eo Ei α Δ β Φ) →
    ProofMode.Entails' Δ (atomicUpdate Eo Ei α β Φ) :=
  tacAupdIntro α β Φ Eo Ei

theorem tacAaccIntro {Δ Δ' : PROP} (P : PROP) Eo Ei x :
    Ei ⊆ Eo →
    (Δ ⊢ Δ' ∗ α x) →
    (Δ' ⊢ α x ={Eo}=∗ P) →
    (Δ' ⊢ ∀ y, β x y ={Eo}=∗ Φ x y) →
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
    let_expr atomicUpdate _ _ instFUpd A B Eo Ei α β Φ := goal |
      throwError "iauintro: goal is not an atomic update"
    let Δctx : Q($prop) := hyps.tm
    let accGoalExpr ← mkAppM ``atomicAcc #[Eo, Ei, α, Δctx, β, Φ]
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
    let pf ← mkAppM ``tacAupdIntroExplicitPM #[α, β, Φ, Δactual, Eo, Ei, Hacc]
    mvar.assign pf

elab "iaaccintro" " with " h:ident : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse (← `(pmTerm| $h:ident))
  ProofModeM.runTactic λ mvar g => do
    let { prop, hyps, goal, .. } := g
    let goal ← instantiateMVars goal
    let_expr atomicAcc _ _ _ _ B Eo Ei α P β Φ := goal |
      throwError "iaaccintro: goal is not an atomic accessor"
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
    let yTy := B
    let commitGoal ← withLocalDeclD `y yTy fun y => do
      let βxy := mkApp2 β x y
      let Φxy := mkApp2 Φ x y
      let fupdΦ ← mkAppM ``FUpd.fupd #[Eo, Eo, Φxy]
      let body ← mkAppM ``BIBase.wand #[βxy, fupdΦ]
      let lam ← mkLambdaFVars #[y] body
      mkAppM ``BIBase.forall #[lam]
    let some abortGoal ← checkTypeQ abortGoal prop |
      throwError "iaaccintro: internal error, malformed abort subgoal"
    let some commitGoal ← checkTypeQ commitGoal prop |
      throwError "iaaccintro: internal error, malformed commit subgoal"
    let Habort ← addBIGoal hyps' abortGoal
    let Hcommit ← addBIGoal hyps' commitGoal
    let pf ← mkAppM ``tacAaccIntro #[α, β, Φ, P, Eo, Ei, x, Hsub, Hsel, Habort, Hcommit]
    mvar.assign pf
end ProofMode


/- Opening a packed atomic update no longer needs telescope reduction. -/
macro "iauopen" colGt pmt:pmTerm " with " colGt pat:icasesPat : tactic =>
  `(tactic| imod $pmt with $pat)

macro "iauopen" colGt pmt:pmTerm : tactic =>
  `(tactic| imod $pmt)

end Iris
