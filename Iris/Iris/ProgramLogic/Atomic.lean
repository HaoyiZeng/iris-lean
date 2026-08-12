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
variable {A B P : Type _}

@[rocq_alias atomic_wp]
abbrev atomicWP
    (e : Expr) (E : CoPset)
    (α : A → IProp GF)
    (β : A → B → IProp GF)
    (POST : A → B → P → Option (IProp GF))
    (f : A → B → P → Val) : IProp GF :=
  iprop(∀ (Φ : Val → IProp GF),
    atomicUpdate (⊤ \ E) ∅ α β
      (fun x y => iprop(∀ z, wandM (POST x y z) (Φ (f x y z)))) -∗
    WP e {{ Φ }})

declare_syntax_cat atomicWpPre
declare_syntax_cat atomicWpPost
syntax "⟪" ("∀ " ident+ ", ")? term "⟫" : atomicWpPre
syntax "⟪" ("∃ " ident+ ", ")? term " | " (ident+ ", ")? "RET " term ("; " term)? "⟫" : atomicWpPost
syntax "⟪" term " | " ident " : " term ", " "RET " term "; " term "⟫" : atomicWpPost

syntax (name := atomicTripleNotation)
  ppRealFill(atomicWpPre ppSpace term:arg " @ " term:arg ppSpace atomicWpPost) : term

open Lean in
macro_rules
  | `(⟪ $[∀ $xs* , ]? $α:term ⟫ $e:term @ $E:term
      ⟪ $[∃ $ys* , ]? $β:term | $[$zs* , ]? RET $v:term $[; $post:term]? ⟫) => do
      let xs : List Ident := (xs.map (·.toList)).getD []
      let ys : List Ident := (ys.map (·.toList)).getD []
      let zs : List Ident := (zs.map (·.toList)).getD []
      let postTerm ← match post with
        | some p => `(some iprop($p))
        | none   => `((none : Option (IProp _)))
      let pre  (b : Term) : MacroM Term := buildAuLam xs b
      let mid  (b : Term) : MacroM Term := do buildAuLam xs (← buildAuLam ys b)
      let full (b : Term) : MacroM Term := do
        buildAuLam xs (← buildAuLam ys (← buildAuLam zs b))
      `(atomicWP $e $E
          $(← pre  (← `(iprop($α))))
          $(← mid  (← `(iprop($β))))
          $(← full postTerm)
          $(← full v))
  | `(⟪ $[∀ $xs* , ]? $α:term ⟫ $e:term @ $E:term
      ⟪ $β:term | $z:ident : $_zty:term, RET $v:term; $post:term ⟫) => do
      let xs : List Ident := (xs.map (·.toList)).getD []
      let zs : List Ident := [z]
      let pre  (b : Term) : MacroM Term := buildAuLam xs b
      let mid  (b : Term) : MacroM Term := do buildAuLam xs (← buildAuLam [] b)
      let full (b : Term) : MacroM Term := do
        buildAuLam xs (← buildAuLam [] (← buildAuLam zs b))
      `(atomicWP $e $E
          $(← pre  (← `(iprop($α))))
          $(← mid  (← `(iprop($β))))
          $(← full (← `(some iprop($post))))
          $(← full v))

section Delab
public meta section
open Lean PrettyPrinter Delaborator SubExpr

/-- Peel a packed family whose leaf is an `Option`, returning the leaf only when
it is `some`. Used for optional `POST` clauses. -/
def delabAuOptLeaf : DelabM (Option Term) :=
  Iris.Delab.enterUncurryChain #[] fun entries => do
    match_expr (← getExpr) with
    | Option.some _ _ => do
        let (_, body) ← Iris.Delab.delabBinders entries.toList (withNaryArg 1 delab)
        return some body
    | _ => return none

@[delab app.Iris.atomicWP]
def delabAtomicWP : Delab := do
  let expr ← getExpr
  guard <| expr.getAppFn.isConstOf ``atomicWP
  let n := expr.getAppNumArgs
  guard <| 6 ≤ n
  let e ← withNaryArg (n - 6) delab
  let E ← withNaryArg (n - 5) delab
  let (preT, aBody) ← withNaryArg (n - 4) delabAuFamily
  let (midT, bBody) ← withNaryArg (n - 3) delabAuFamily
  let post          ← withNaryArg (n - 2) delabAuOptLeaf
  let (allT, vBody) ← withNaryArg (n - 1) delabAuFamily
  guard <| preT.size ≤ midT.size && midT.size ≤ allT.size
  let xs ← toIdents preT
  let ys ← toIdents (midT.extract preT.size midT.size)
  let zs ← toIdents (allT.extract midT.size allT.size)
  let preStx ← if xs.isEmpty then `(atomicWpPre| ⟪$aBody⟫)
                             else `(atomicWpPre| ⟪∀ $xs*, $aBody⟫)
  let postStx ← match ys.isEmpty, zs.isEmpty, post with
    | true,  true,  none   => `(atomicWpPost| ⟪$bBody | RET $vBody⟫)
    | true,  true,  some p => `(atomicWpPost| ⟪$bBody | RET $vBody; $p⟫)
    | true,  false, none   => `(atomicWpPost| ⟪$bBody | $zs*, RET $vBody⟫)
    | true,  false, some p => `(atomicWpPost| ⟪$bBody | $zs*, RET $vBody; $p⟫)
    | false, true,  none   => `(atomicWpPost| ⟪∃ $ys*, $bBody | RET $vBody⟫)
    | false, true,  some p => `(atomicWpPost| ⟪∃ $ys*, $bBody | RET $vBody; $p⟫)
    | false, false, none   => `(atomicWpPost| ⟪∃ $ys*, $bBody | $zs*, RET $vBody⟫)
    | false, false, some p => `(atomicWpPost| ⟪∃ $ys*, $bBody | $zs*, RET $vBody; $p⟫)
  `($preStx:atomicWpPre $e @ $E $postStx:atomicWpPost)

end
end Delab

section Lemmas

@[rocq_alias atomic_wp_seq]
theorem atomicWP_seq (e : Expr) (E : CoPset)
    (α : A → IProp GF)
    (β : A → B → IProp GF)
    (POST : A → B → P → Option (IProp GF))
    (f : A → B → P → Val) :
  atomicWP e E α β POST f -∗
  ∀ Φ, ∀ x, α x -∗ (∀ y, β x y -∗ (∀ z, POST x y z -∗? Φ (f x y z))) -∗
    WP e {{ Φ }} := by
  unfold atomicWP
  iintro Hwp %Φ %x Hα HΦ
  let AUΦ : A → B → IProp GF := λ x y => iprop(∀ z, POST x y z -∗? Φ (f x y z))
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
    (α : A → IProp GF)
    (β : A → B → IProp GF)
    (POST : A → B → P → Option (IProp GF))
    (f : A → B → P → Val) :
  toVal e = none →
  atomicWP e E α β POST f -∗
  ∀ Φ, ∀ x, α x -∗
    ▷ (∀ y, β x y -∗ (∀ z, POST x y z -∗? Φ (f x y z))) -∗
    WP e {{ Φ }} := by
  intro Hnone
  iintro Hwp %Φ %x Hα HΦ
  let R : IProp GF := iprop(∀ y, β x y -∗ (∀ z, POST x y z -∗? Φ (f x y z)))
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
    (α : A → IProp GF)
    (β : A → B → IProp GF)
    (POST : A → B → P → Option (IProp GF))
    (f : A → B → P → Val)
    [Language.Atomic .WeaklyAtomic e] :
  (∀ Φ, ∀ x, α x -∗
    (∀ y, β x y -∗ (∀ z, POST x y z -∗? Φ (f x y z))) -∗
    WP e @ ∅ {{ Φ }}) -∗
  atomicWP e E α β POST f := by
  unfold atomicWP
  iintro Hwp %Φ HAU
  let AUΦ : A → B → IProp GF := λ x y => iprop(∀ z, POST x y z -∗? Φ (f x y z))
  iapply wp_atomic (s := Stuckness.NotStuck) (E1 := ⊤) (E2 := ∅)
  ihave HAC0 : atomicAcc (⊤ \ E) ∅ α (atomicUpdate (⊤ \ E) ∅ α β AUΦ) β AUΦ $$ [HAU]
  · iapply aupd_aacc
    iassumption
  ihave HAC : atomicAcc ⊤ ∅ α (atomicUpdate (⊤ \ E) ∅ α β AUΦ) β AUΦ $$ [HAC0]
  · iapply atomicAcc_maskWeaken (⊤ \ E) ⊤ ∅ α
        (atomicUpdate (⊤ \ E) ∅ α β AUΦ) β AUΦ LawfulSet.diff_subset_left $$ HAC0
  ihave Hfupd : iprop(|={⊤,∅}=> ∃ x, α x ∗
      ((α x ={∅,⊤}=∗ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ∧
      (∀ y, β x y ={∅,⊤}=∗ AUΦ x y))) $$ [HAC]
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
  ihave HΦ' : iprop(∀ z, POST x y z -∗? Φ (f x y z)) $$ [HΦ]
  · dsimp only [AUΦ]
    exact .rfl
  iapply HΦ' $$ %z

@[rocq_alias persistent_seq_wp_atomic]
theorem persistentSeqWP_atomic (e : Expr) (E : CoPset)
    (α : Unit → IProp GF)
    (β : Unit → TB → IProp GF)
    (POST : Unit → TB → TP → Option (IProp GF))
    (f : Unit → TB → TP → Val)
    [Persistent (α ())] :
  (∀ Φ, α () -∗
    (∀ y, β () y -∗
      (∀ z, POST () y z -∗? Φ (f () y z))) -∗
    WP e {{ Φ }}) -∗
  atomicWP e E α β POST f := by
  unfold atomicWP
  iintro Hwp %Φ HAU
  let AUΦ : Unit → TB → IProp GF :=
    λ x y => iprop(∀ z, POST x y z -∗? Φ (f x y z))
  iapply fupd_wp
  ihave Hfupd : iprop(|={⊤,∅}=> ∃ x, α x ∗
      ((α x ={∅,⊤}=∗ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ∧
      (∀ y, β x y ={∅,⊤}=∗ AUΦ x y))) $$ [HAU]
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
  iapply wandM_fupd (POST () y z) (Φ (f () y z)) ⊤ ⊤
  ihave Hfupd2 : iprop(|={⊤,∅}=> ∃ x, α x ∗
      ((α x ={∅,⊤}=∗ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ∧
      (∀ y, β x y ={∅,⊤}=∗ AUΦ x y))) $$ [HAU']
  · iapply aupd_acc α β AUΦ (⊤ \ E) ∅ ⊤ LawfulSet.diff_subset_left $$ HAU'
  imod Hfupd2 with ⟨%x', Hα', Hclose'⟩
  cases x'
  icases Hα' with #Hα'
  icases Hclose' with ⟨-, Hcommit⟩
  imod Hcommit $$ %y Hβ with HΦ
  imodintro
  ihave HΦ' : iprop(∀ z, POST () y z -∗? Φ (f () y z)) $$ [HΦ]
  · dsimp only [AUΦ]
    exact sep_elim_right
  iapply HΦ' $$ %z

@[rocq_alias atomic_wp_mask_weaken]
theorem atomicWP_maskWeaken (e : Expr) (E1 E2 : CoPset)
    (α : A → IProp GF)
    (β : A → B → IProp GF)
    (POST : A → B → P → Option (IProp GF))
    (f : A → B → P → Val) :
  E1 ⊆ E2 →
  atomicWP e E1 α β POST f -∗ atomicWP e E2 α β POST f := by
  intro HE
  unfold atomicWP
  iintro Hwp %Φ HAU
  let AUΦ : A → B → IProp GF := λ x y => iprop(∀ z, POST x y z -∗? Φ (f x y z))
  have Hdiff : (⊤ \ E2 : CoPset) ⊆ (⊤ \ E1 : CoPset) := by
    intro x hx
    rw [LawfulSet.mem_diff] at hx ⊢
    exact ⟨hx.1, fun hxE1 => hx.2 (HE x hxE1)⟩
  iapply Hwp $$ %Φ
  iapply atomicUpdate_maskWeaken α β AUΦ (⊤ \ E2) (⊤ \ E1) ∅ Hdiff $$ HAU

@[rocq_alias atomic_wp_inv]
theorem atomicWP_inv (e : Expr) (E : CoPset)
    (α : A → IProp GF)
    (β : A → B → IProp GF)
    (POST : A → B → P → Option (IProp GF))
    (f : A → B → P → Val)
    (N : Namespace) (I : IProp GF) :
  ↑N ⊆ E →
  atomicWP e (E \ ↑N)
    (λ x => iprop(▷ I ∗ α x))
    (λ x y => iprop(▷ I ∗ β x y)) POST f -∗
  inv N I -∗ atomicWP e E α β POST f := by
  intro HN
  unfold atomicWP
  iintro Hwp #Hinv %Φ HAU
  let αI : A → IProp GF := λ x => iprop(▷ I ∗ α x)
  let βI : A → B → IProp GF := λ x y => iprop(▷ I ∗ β x y)
  let AUΦ : A → B → IProp GF := λ x y => iprop(∀ z, POST x y z -∗? Φ (f x y z))
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
    ihave HAUacc : iprop(|={(⊤ \ (E \ ↑N)) \ ↑N, ∅}=> ∃ x, α x ∗
        ((α x ={∅,(⊤ \ (E \ ↑N)) \ ↑N}=∗ atomicUpdate (⊤ \ E) ∅ α β AUΦ) ∧
        (∀ y, β x y ={∅,(⊤ \ (E \ ↑N)) \ ↑N}=∗ AUΦ x y))) $$ [HAU]
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


end Iris
