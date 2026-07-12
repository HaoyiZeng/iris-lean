module

public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.Invariants
public import Iris.ProgramLogic.WeakestPre

@[expose] public section

namespace Iris

open BI ProgramLogic Language.Notation Std

-- TODO : move this
def wandM [BI PROP] : Option PROP → PROP → PROP
  | some P, Q => iprop(P -∗ Q)
  | none, Q => Q
syntax:25 term:26 " -∗? " term:25 : term
macro_rules
  | `(iprop($P -∗? $Q)) => ``(wandM $P iprop($Q))
delab_rule wandM
  | `($_ $P $Q) => do ``(iprop($P -∗? $Q))

theorem wandM_fupd_wand [BI PROP] [BIFUpdate PROP]
    (P : Option PROP) (R Q : PROP) (E : CoPset) :
    (R -∗ wandM P Q) -∗ wandM P iprop(R ={E}=∗ Q) := by
  cases P with
  | none =>
      simp [wandM]
      iintro H HR
      imodintro
      iapply H $$ HR
  | some P =>
      simp [wandM]
      iintro H HP HR
      imodintro
      iapply H $$ HR HP

theorem wandM_fupd [BI PROP] [BIFUpdate PROP]
    (P : Option PROP) (Q : PROP) (E1 E2 : CoPset) :
    (|={E1,E2}=> wandM P Q) -∗ wandM P iprop(|={E1,E2}=> Q) := by
  cases P with
  | none =>
      simp [wandM]
      iintro H
      iexact H
  | some P =>
      simp [wandM]
      iintro H HP
      imod H with HPQ
      imodintro
      iapply HPQ $$ HP

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {TA TB TP : Tele}

@[rocq_alias atomic_wp]
abbrev atomicWP
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val) : IProp GF :=
  iprop(∀ (Φ : Val → IProp GF),
    atomicUpdate (⊤ \ E) ∅ α β
      (λ x y => ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
    WP e {{ Φ }})


declare_syntax_cat atomicWpPre
syntax "⟪" ("∀ " ident ", ")? term "⟫" : atomicWpPre

declare_syntax_cat atomicWpPost
syntax "⟪" "∃ " ident ", " term " | " ident ", " "RET " term "; " term "⟫" : atomicWpPost
syntax "⟪" term " | " "RET " term "⟫" : atomicWpPost

syntax (name := atomicTripleNotation)
  ppRealFill(atomicWpPre ppSpace term:arg " @ " term:arg ppSpace atomicWpPost) : term

macro_rules
  | `(⟪ ∀ $x:ident, $α:term ⟫ $e:term @ $E:term
      ⟪ ∃ $y:ident, $β:term | $z:ident, RET $v:term; $POST:term ⟫) =>
      `(atomicWP
        (TA := Tele.cons <| λ xn => Tele.nil)
        (TB := Tele.cons <| λ yn => Tele.nil)
        (TP := Tele.cons <| λ zn => Tele.nil)
        $e $E
        (Tele.app <| λ $x => ULift.up iprop($α))
        (Tele.app <| λ $x => ULift.up <| Tele.app <| λ $y => ULift.up iprop($β))
        (Tele.app <| λ $x => ULift.up <| Tele.app <| λ $y => ULift.up <| Tele.app <| λ $z => ULift.up (some iprop($POST)))
        (Tele.app <| λ $x => ULift.up <| Tele.app <| λ $y => ULift.up <| Tele.app <| λ $z => ULift.up $v))
  | `(⟪ ∀ $x:ident, $α:term ⟫ $e:term @ $E:term
      ⟪ $β:term | RET $v:term ⟫) =>
      `(atomicWP
        (TA := Tele.cons <| λ xn => Tele.nil)
        (TB := Tele.nil)
        (TP := Tele.nil)
        $e $E
        (Tele.app <| λ $x => ULift.up iprop($α))
        (Tele.app <| λ $x => ULift.up <| Tele.app (ULift.up iprop($β)))
        (Tele.app <| λ $x => ULift.up <| Tele.app (ULift.up <| Tele.app (ULift.up none)))
        (Tele.app <| λ $x => ULift.up <| Tele.app (ULift.up <| Tele.app (ULift.up $v))))
  | `(⟪ $α:term ⟫ $e:term @ $E:term
      ⟪ $β:term | RET $v:term ⟫) =>
      `(atomicWP
        (TA := Tele.nil)
        (TB := Tele.nil)
        (TP := Tele.nil)
        $e $E
        (Tele.app (ULift.up iprop($α)))
        (Tele.app (ULift.up <| Tele.app (ULift.up iprop($β))))
        (Tele.app (ULift.up <| Tele.app (ULift.up <| Tele.app (ULift.up none))))
        (Tele.app (ULift.up <| Tele.app (ULift.up <| Tele.app (ULift.up $v)))))


section Lemmas

@[rocq_alias atomic_wp_seq]
theorem atomicWP_seq (e : Expr) (E : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val) :
  atomicWP e E α β POST f -∗
  ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ (∀.. z, POST x y z -∗? Φ (f x y z))) -∗
    WP e {{ Φ }} := by
  unfold atomicWP
  iintro Hwp %Φ %x Hα HΦ
  let AUΦ : TA → TB → IProp GF := λ x y => iprop(∀.. z, POST x y z -∗? Φ (f x y z))
  iapply Hwp $$ %Φ
  iauintro
  iaaccintro with Hα
  · iintro Hα
    imodintro
    isplitl [Hα]
    · iexact Hα
    · iexact HΦ
  · iintro %y Hβ
    imodintro
    dsimp only []
    iapply HΦ $$ %y Hβ

@[rocq_alias atomic_wp_seq_step]
theorem atomicWP_seq_step (e : Expr) (E : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val) :
  toVal e = none →
  atomicWP e E α β POST f -∗
  ∀ Φ, ∀.. x, α x -∗
    ▷ (∀.. y, β x y -∗ (∀.. z, POST x y z -∗? Φ (f x y z))) -∗
    WP e {{ Φ }} := by
  intro Hnone
  iintro Hwp %Φ %x Hα HΦ
  let R : IProp GF := iprop(∀.. y, β x y -∗ (∀.. z, POST x y z -∗? Φ (f x y z)))
  ihave Hstep : (|={⊤}[⊤]▷=> R) $$ [HΦ]
  · iapply step_fupd_intro LawfulSet.subset_refl
    iassumption
  iapply wp_step_fupd (s := Stuckness.NotStuck) (E₁ := ⊤) (E₂ := ⊤)
      (P := R) (e := e) (Φ := Φ) Hnone LawfulSet.subset_refl $$ Hstep
  · iapply atomicWP_seq (e := e) (E := E) (α := α) (β := β) (POST := POST) (f := f) $$ Hwp
        %(fun v => iprop(R ={⊤}=∗ Φ v)) %x Hα
    iintro %y Hβ %z
    iapply wandM_fupd_wand (POST x y z) R (Φ (f x y z)) ⊤
    iintro HR
    iapply HR $$ %y Hβ %z

@[rocq_alias atomic_seq_wp_atomic]
theorem atomicSeqWP_atomic (e : Expr) (E : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val)
    [Language.Atomic .WeaklyAtomic e] :
  (∀ Φ, ∀.. x, α x -∗
    (∀.. y, β x y -∗ (∀.. z, POST x y z -∗? Φ (f x y z))) -∗
    WP e @ ∅ {{ Φ }}) -∗
  atomicWP e E α β POST f := by
  unfold atomicWP
  iintro Hwp %Φ HAU
  let AUΦ : TA → TB → IProp GF := λ x y => iprop(∀.. z, POST x y z -∗? Φ (f x y z))
  iapply wp_atomic (s := Stuckness.NotStuck) (E1 := ⊤) (E2 := ∅)
  ihave HAC0 : atomicAcc (⊤ \ E) ∅ α (atomicUpdate (⊤ \ E) ∅ α β AUΦ) β AUΦ $$ [HAU]
  · iapply aupd_aacc
    iassumption
  ihave HAC : atomicAcc ⊤ ∅ α (atomicUpdate (⊤ \ E) ∅ α β AUΦ) β AUΦ $$ [HAC0]
  · iapply atomicAcc_maskWeaken (⊤ \ E) ⊤ ∅ α
        (atomicUpdate (⊤ \ E) ∅ α β AUΦ) β AUΦ LawfulSet.diff_subset_left $$ HAC0
  ihave Hfupd : iprop(|={⊤,∅}=> ∃.. x, α x ∗
      ((α x ={∅,⊤}=∗ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ∧
      (∀.. y, β x y ={∅,⊤}=∗ AUΦ x y))) $$ [HAC]
  · unfold atomicAcc
    iexact HAC
  imod Hfupd with ⟨%x, Hα, Hclose⟩
  imodintro
  iapply Hwp $$ %(fun v => iprop(|={∅,⊤}=> Φ v)) %x Hα
  iintro %y Hβ %z
  iapply wandM_fupd (POST x y z) (Φ (f x y z)) ∅ ⊤
  icases Hclose with ⟨-, Hcommit⟩
  imod Hcommit $$ %y Hβ with HΦ
  imodintro
  ihave HΦ' : iprop(∀.. z, POST x y z -∗? Φ (f x y z)) $$ [HΦ]
  · dsimp only [AUΦ]
    exact .rfl
  iapply HΦ' $$ %z

@[rocq_alias persistent_seq_wp_atomic]
theorem persistentSeqWP_atomic (e : Expr) (E : CoPset)
    (α : Tele.Arg Tele.nil → IProp GF)
    (β : Tele.Arg Tele.nil → TB → IProp GF)
    (POST : Tele.Arg Tele.nil → TB → TP → Option (IProp GF))
    (f : Tele.Arg Tele.nil → TB → TP → Val)
    [Persistent (α PUnit.unit)] :
  (∀ Φ, α PUnit.unit -∗
    (∀.. y, β PUnit.unit y -∗
      (∀.. z, POST PUnit.unit y z -∗? Φ (f PUnit.unit y z))) -∗
    WP e {{ Φ }}) -∗
  atomicWP e E α β POST f := by
  unfold atomicWP
  iintro Hwp %Φ HAU
  let AUΦ : Tele.Arg Tele.nil → TB → IProp GF :=
    λ x y => iprop(∀.. z, POST x y z -∗? Φ (f x y z))
  iapply fupd_wp
  ihave Hfupd : iprop(|={⊤,∅}=> ∃.. x, α x ∗
      ((α x ={∅,⊤}=∗ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ∧
      (∀.. y, β x y ={∅,⊤}=∗ AUΦ x y))) $$ [HAU]
  · iapply aupd_acc α β AUΦ (⊤ \ E) ∅ ⊤ LawfulSet.diff_subset_left $$ HAU
  imod Hfupd with ⟨%x, Hα, Hclose⟩
  cases x
  icases Hα with #Hα
  icases Hclose with ⟨Habort, -⟩
  imod Habort $$ Hα with HAU'
  imodintro
  iapply wp_fupd
  iapply Hwp $$ %(fun v => iprop(|={⊤}=> Φ v)) Hα
  iintro %y Hβ %z
  iapply wandM_fupd (POST PUnit.unit y z) (Φ (f PUnit.unit y z)) ⊤ ⊤
  ihave Hfupd2 : iprop(|={⊤,∅}=> ∃.. x, α x ∗
      ((α x ={∅,⊤}=∗ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ∧
      (∀.. y, β x y ={∅,⊤}=∗ AUΦ x y))) $$ [HAU']
  · iapply aupd_acc α β AUΦ (⊤ \ E) ∅ ⊤ LawfulSet.diff_subset_left $$ HAU'
  imod Hfupd2 with ⟨%x', Hα', Hclose'⟩
  cases x'
  icases Hα' with #Hα'
  icases Hclose' with ⟨-, Hcommit⟩
  imod Hcommit $$ %y Hβ with HΦ
  imodintro
  ihave HΦ' : iprop(∀.. z, POST PUnit.unit y z -∗? Φ (f PUnit.unit y z)) $$ [HΦ]
  · dsimp only [AUΦ]
    exact sep_elim_right
  iapply HΦ' $$ %z

@[rocq_alias atomic_wp_mask_weaken]
theorem atomicWP_maskWeaken (e : Expr) (E1 E2 : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val) :
  E1 ⊆ E2 →
  atomicWP e E1 α β POST f -∗ atomicWP e E2 α β POST f := by
  intro HE
  unfold atomicWP
  iintro Hwp %Φ HAU
  let AUΦ : TA → TB → IProp GF := λ x y => iprop(∀.. z, POST x y z -∗? Φ (f x y z))
  have Hdiff : (⊤ \ E2 : CoPset) ⊆ (⊤ \ E1 : CoPset) := by
    intro x hx
    rw [LawfulSet.mem_diff] at hx ⊢
    exact ⟨hx.1, fun hxE1 => hx.2 (HE x hxE1)⟩
  iapply Hwp $$ %Φ
  iapply atomicUpdate_maskWeaken α β AUΦ (⊤ \ E2) (⊤ \ E1) ∅ Hdiff $$ HAU

@[rocq_alias atomic_wp_inv]
theorem atomicWP_inv (e : Expr) (E : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val)
    (N : Namespace) (I : IProp GF) :
  ↑N ⊆ E →
  atomicWP e (E \ ↑N)
    (λ x => iprop(▷ I ∗ α x))
    (λ x y => iprop(▷ I ∗ β x y)) POST f -∗
  inv N I -∗ atomicWP e E α β POST f := by
  intro HN
  unfold atomicWP
  iintro Hwp #Hinv %Φ HAU
  let αI : TA → IProp GF := λ x => iprop(▷ I ∗ α x)
  let βI : TA → TB → IProp GF := λ x y => iprop(▷ I ∗ β x y)
  let AUΦ : TA → TB → IProp GF := λ x y => iprop(∀.. z, POST x y z -∗? Φ (f x y z))
  have Hacc : iprop(inv N I ∧ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ⊢
      atomicAcc (⊤ \ (E \ ↑N)) ∅ αI (atomicUpdate (⊤ \ E) ∅ α β AUΦ) βI AUΦ := by
    iintro ⟨#Hinv, HAU⟩
    unfold atomicAcc
    have HNmask : ↑N ⊆ (⊤ \ (E \ ↑N) : CoPset) := by
      intro x hxN
      rw [LawfulSet.mem_diff]
      constructor
      · exact CoPset.mem_full
      · intro hx
        rw [LawfulSet.mem_diff] at hx
        exact hx.2 hxN
    have Houter : (⊤ \ E : CoPset) ⊆ ((⊤ \ (E \ ↑N)) \ ↑N : CoPset) := by
      intro x hx
      rw [LawfulSet.mem_diff] at hx ⊢
      constructor
      · rw [LawfulSet.mem_diff]
        constructor
        · exact hx.1
        · intro hxEdiff
          rw [LawfulSet.mem_diff] at hxEdiff
          exact hx.2 hxEdiff.1
      · intro hxN
        exact hx.2 (HN x hxN)
    imod inv_acc HNmask $$ Hinv with ⟨HI, HcloseInv⟩
    ihave HAUacc : iprop(|={(⊤ \ (E \ ↑N)) \ ↑N, ∅}=> ∃.. x, α x ∗
        ((α x ={∅,(⊤ \ (E \ ↑N)) \ ↑N}=∗ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ∧
        (∀.. y, β x y ={∅,(⊤ \ (E \ ↑N)) \ ↑N}=∗ AUΦ x y))) $$ [HAU]
    · iapply aupd_acc α β AUΦ (⊤ \ E) ∅ ((⊤ \ (E \ ↑N)) \ ↑N) Houter $$ HAU
    imod HAUacc with ⟨%x, Hα, HcloseAU⟩
    imodintro
    iexists x
    isplitl [HI Hα]
    · dsimp only [αI]
      iframe
    isplit
    · iintro HαI
      ihave Hαpair : iprop(▷ I ∗ α x) $$ [HαI]
      · dsimp only [αI]
        exact sep_elim_right
      icases Hαpair with ⟨HI', Hα'⟩
      icases HcloseAU with ⟨HabortAU, -⟩
      imod HabortAU $$ Hα' with HAU'
      imod HcloseInv $$ HI' with _
      imodintro
      iexact HAU'
    · iintro %y HβI
      ihave Hβpair : iprop(▷ I ∗ β x y) $$ [HβI]
      · dsimp only [βI]
        exact sep_elim_right
      icases Hβpair with ⟨HI', Hβ'⟩
      icases HcloseAU with ⟨-, HcommitAU⟩
      imod HcommitAU $$ %y Hβ' with HΦ
      imod HcloseInv $$ HI' with _
      imodintro
      ihave HΦ' : AUΦ x y $$ [HΦ]
      · exact sep_elim_right
      iexact HΦ'
  iapply Hwp $$ %Φ
  iapply aupd_intro (α := αI) (β := βI) (Φ := AUΦ)
      (P := inv N I) (Q := atomicUpdate (⊤ \ E) ∅ α β AUΦ)
  · infer_instance
  · infer_instance
  · exact Hacc
  · isplit
    · iexact Hinv
    · iexact HAU

end Lemmas

section Delab
public meta section
open Lean PrettyPrinter Delaborator SubExpr

@[delab app.Iris.atomicWP]
def delabAtomicWP : Delab := do
  let e ← getExpr
  unless e.getAppFn.isConstOf ``atomicWP do failure
  let args := e.getAppArgs
  let n := args.size
  unless n ≥ 9 do failure
  let TA := args[n-9]!
  let TB := args[n-8]!
  let TP := args[n-7]!
  let prog ← withNaryArg (n-6) delab
  let E ← withNaryArg (n-5) delab
  let αNames := teleNames args[n-4]! [TA]
  let βNames := teleNames args[n-3]! [TA, TB]
  let pNames := teleNames args[n-2]! [TA, TB, TP]
  let (αn, α) ← peelDelab args[n-4]! [TA] αNames
  let taCons := !(TA.isConstOf ``Tele.nil)
  let tbCons := !(TB.isConstOf ``Tele.nil)
  if tbCons then
    let (βn, β) ← peelDelab args[n-3]! [TA, TB] βNames
    let (postn, POST) ← peelComp args[n-2]! [TA, TB, TP] pNames fun nms body => do
      let body := if body.isAppOf ``Option.some then body.appArg! else body
      return (nms, ← unpackIprop (← Lean.PrettyPrinter.delab body))
    let (_, v) ← peelDelab args[n-1]! [TA, TB, TP] pNames
    let y := mkIdent (βn[if taCons then 1 else 0]?.getD `y)
    let z := mkIdent (postn[(if taCons then 1 else 0) + 1]?.getD `z)
    if taCons then
      let x := mkIdent (αn[0]?.getD `x)
      `(⟪ ∀ $x, $α ⟫ $prog @ $E ⟪ ∃ $y, $β | $z, RET $v; $POST ⟫)
    else
      `(⟪ $α ⟫ $prog @ $E ⟪ ∃ $y, $β | $z, RET $v; $POST ⟫)
  else
    let (_, β) ← peelDelab args[n-3]! [TA, TB] βNames
    let (_, v) ← peelDelab args[n-1]! [TA, TB, TP] pNames
    if taCons then
      let x := mkIdent (αn[0]?.getD `x)
      `(⟪ ∀ $x, $α ⟫ $prog @ $E ⟪ $β | RET $v ⟫)
    else
      `(⟪ $α ⟫ $prog @ $E ⟪ $β | RET $v ⟫)
end
end Delab

end Iris
