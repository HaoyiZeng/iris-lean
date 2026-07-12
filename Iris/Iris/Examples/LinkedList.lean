/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Lib.SpinLock
public import Iris.Algebra.Lib.ExclAuth
public import Iris.ProgramLogic.Atomic

@[expose] public section
namespace Iris.Examples.HeapLang

open Iris.HeapLang BI Iris ProgramLogic List

namespace LinkedList

def new : Val := hl_val% λ _, ref(none())

def add : Val := hl_val%
  λ hd x,
    let v := !hd;
    hd ← some(ref((x, v)))

def removeAux : Val := hl_val%
  rec go x v :=
    match v with
    | none() => none()
    | some(l) =>
      let p := !l;
      let head := fst(p);
      let tail := snd(p);
      if head = x then
        tail
      else
        let newtail := go x tail;
        l ← (head, newtail);
        some(l)

def remove : Val := hl_val%
  λ hd x,
    let v := !hd;
    let v' := &removeAux x v;
    hd ← v'

section Predicates

variable [HeapLangGS hlc GF]

/-- `isList v xs` : the head value `v` represents the mathematical list `xs`. -/
def isList (v : Val) : List Int → IProp GF
  | [] => iprop% ⌜v = hl_val(none())⌝
  | x :: xs => iprop% ∃ l tl, ⌜v = hl_val(some(#(.loc l)))⌝ ∗
    l ↦ some hl_val((#x, &tl)) ∗ isList tl xs

theorem isList_nil {v} :
  isList (GF:=GF) v [] ⊣⊢ iprop(⌜v = hl_val(none())⌝) := .rfl

theorem isList_cons {v x xs} :
  isList (GF:=GF) v (x :: xs) ⊣⊢ iprop(∃ l tl, ⌜v = hl_val(some(#(.loc l)))⌝ ∗
    l ↦ some hl_val((#x, &tl)) ∗ isList tl xs) := .rfl

/-- `isMList h xs` : the handle `h` is a pointer to a head value representing `xs`. -/
def isMList (h : Val) (xs : List Int) : IProp GF := iprop%
  ∃ (l : Loc) (v : Val), ⌜h = Val.lit (.loc l)⌝ ∗ l ↦ some v ∗ isList v xs

end Predicates

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

/-- `new` returns a handle to a fresh empty list. -/
theorem new_spec :
    ⊢ ⦃ True ⦄ hl(&new #()) ⦃ h, RET h; isMList (GF := GF) h [] ⦄ := by
  iintro %Φ - HI
  unfold new
  wp_pures
  iapply wp_alloc
  iintro !> %l Halloc
  iapply HI
  unfold isMList isList
  iexists l, hl_val(none())
  iframe
  itrivial

/-- `add hd x` prepends `x`, turning the represented list `xs` into `x :: xs`. -/
theorem add_spec h x xs :
    ⊢ ⦃ isMList (GF := GF) h xs ⦄ hl(&add &h #x) ⦃ RET hl_val(#()); isMList h (x :: xs) ⦄ := by
  iintro %Φ H1 H
  unfold add
  wp_pures
  unfold isMList
  icases H1 with ⟨%l, %v, %Hh, Hl, Hlist⟩
  rw [Hh]
  wp_bind !_
  iapply wp_load $$ Hl
  iintro !> Hl
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %l' Halloc
  wp_pures
  iapply wp_store $$ Hl
  iintro !> Hl
  iapply H
  iexists l, hl_val(some(#(.loc l')))
  isplit
  · itrivial
  · iframe Hl; rw [isList]; iexists l', v; iframe; itrivial


/-- Helper spec for `removeAux`, in continuation-passing (wand) form so it can be
applied recursively while retaining the current node's resources. -/
theorem removeAux_wp x v xs (Φ : Val → IProp GF) :
    isList v xs -∗
    (∀ v', isList v' (xs.erase x) -∗ Φ v') -∗
    WP hl(&removeAux #x &v) {{ Φ }} := by
  iintro Hl H
  iloeb as IH generalizing %v %xs %Φ
  wp_rec; wp_pures
  cases xs with
  | nil =>
    icases isList_nil $$ Hl with %heq; subst heq
    wp_pures
    imodintro
    iapply H
    rw [List.erase_nil]
    iapply Hl
  | cons hd tl =>
    icases isList_cons $$ Hl with ⟨%l, %tlv, %heq, Hpt, Hl⟩
    subst heq
    wp_pures
    wp_bind !_
    iapply wp_load $$ Hpt
    iintro !> Hpt
    wp_pures
    by_cases hcmp : hd = x
    · subst hcmp
      simp only [beq_self_eq_true]
      wp_pures
      imodintro
      iapply H
      rw [List.erase_cons_head]; iexact Hl
    · have hb : (hl_val(#hd) == hl_val(#x)) = false := by simp [hcmp]
      simp only [hb]
      wp_pures
      wp_bind &removeAux _ _
      iapply IH $$ Hl
      iintro %v' Hl'
      wp_pures
      wp_bind (_ ← _)
      iapply wp_store $$ Hpt
      iintro !> Hpt
      wp_pures
      imodintro
      iapply H
      rw [List.erase_cons_tail (by simpa using hcmp), isList]
      iexists l, v'
      iframe
      itrivial


/-- `remove hd x` deletes the first occurrence of `x` from the represented list. -/
theorem remove_spec h x xs :
    ⊢ ⦃ isMList (GF := GF) h xs ⦄ hl(&remove &h #x) ⦃ RET hl_val(#()); isMList h (xs.erase x) ⦄ := by
  iintro %Φ H1 H
  unfold remove
  wp_pures
  unfold isMList
  icases H1 with ⟨%l, %v, %Hh, Hl, Hlist⟩
  rw [Hh]
  wp_bind !_
  iapply wp_load $$ Hl
  iintro !> Hl
  wp_pures
  wp_bind &removeAux _ _
  iapply removeAux_wp $$ Hlist
  iintro %v' Hlist'
  wp_pures
  iapply wp_store $$ Hl
  iintro !> Hl
  iapply H
  iexists l, v'
  iframe
  itrivial

end Specs

end LinkedList

namespace LockList

open SpinLock

def Node.new : Val := hl_val%
  λ x next,
    let lk := &newlock #();
    let c  := ref((x, next));
    (lk, c)

def Node.insert : Val := hl_val%
  λ node x,
    &acquire (fst(node));
    let c := snd(node);
    let p := !c;
    let new := &Node.new x (snd(p));
    c ← (fst(p), new);
    &release (fst(node))

def Node.setValue : Val := hl_val%
  λ node x,
    &acquire (fst(node));
    let c := snd(node);
    let p := !c;
    c ← (x, snd(p));
    &release (fst(node))

/-- Remove the node *after* `node` (assumes `node` has a successor node, i.e. its
`next` is not `none()`).  Two-lock: lock `node`, read its successor `s`, lock `s`,
splice `node.next := s.next`, unlock both. -/
def Node.removeAfter : Val := hl_val%
  λ node,
    &acquire (fst(node));
    let c := snd(node);
    let p := !c;
    let s := snd(p);
    &acquire (fst(s));
    let cs := snd(s);
    let ps := !cs;
    c ← (fst(p), snd(ps));
    &release (fst(s));
    &release (fst(node))

section Predicates

variable [HeapLangGS hlc GF] [SpinLockG GF]

def isNode (node : Val) (x : Int) : List Int → IProp GF
  | [] => iprop%
    ∃ (lk : Val) (γ : GName) (c : Loc), ⌜node = hl_val((&lk, #c))⌝ ∗
    SpinLock.isLock γ lk (c ↦ hl_val((#x, none())))
  | x' :: xs => iprop%
    ∃ (lk : Val) (γ : GName) (c : Loc) (p : Val), ⌜node = hl_val((&lk, #c))⌝ ∗
    SpinLock.isLock γ lk iprop(c ↦ hl_val((#x, &p)) ∗ isNode p x' xs)

theorem isNode_nil {node x} :
  isNode (GF:=GF) node x [] ⊣⊢
    iprop(∃ (lk : Val) (γ : GName) (c : Loc), ⌜node = hl_val((&lk, #c))⌝ ∗
      SpinLock.isLock γ lk (c ↦ hl_val((#x, none())))) := .rfl

theorem isNode_cons {node x x' xs} :
  isNode (GF:=GF) node x (x'::xs) ⊣⊢
    iprop(
      ∃ (lk : Val) (γ : GName) (c : Loc) (p : Val), ⌜node = hl_val((&lk, #c))⌝ ∗
      SpinLock.isLock γ lk iprop(c ↦ hl_val((#x, &p)) ∗ isNode p x' xs)) := .rfl

instance isNode_persistent (node : Val) (x : Int) (xs : List Int) :
    Persistent (isNode (GF := GF) node x xs) := by
  unfold isNode
  cases xs <;> infer_instance


end Predicates

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF]

theorem Node.new_spec x xs :
    ⊢ ⦃ isNode (GF := GF) next x' xs ⦄ hl(&Node.new #x &next)
        ⦃ node, RET node; isNode node x (x'::xs) ⦄ := by
  iintro %Φ H1 H
  unfold Node.new
  wp_pures
  wp_bind &newlock _
  iapply newlock_spec
  iintro %v %γ2 Hγ2
  wp_pures
  wp_bind ref(_)
  iapply wp_fupd
  iapply wp_alloc
  iintro !> %l Halloc
  imod Hγ2 $$ %(iprop(l ↦ some (hl_val((#x, &next))) ∗ isNode next x' xs)) %⊤ [Halloc H1] with Hlock
  · iframe
  imodintro
  wp_pures
  imodintro
  iapply H
  -- simp [isNode]
  simp only [isNode]
  iexists v, γ2, l, next
  isplit
  itrivial
  iframe

theorem Node.insert_spec x' :
    ⊢ ⦃ ∃ x xs, isNode (GF := GF) hd x xs ⦄
        hl(&Node.insert &hd #x')
      ⦃ RET hl_val(#()); ∃ x xs, isNode node x xs ⦄ := by
  iintro %Φ H1 H
  unfold Node.insert
  wp_pures
  icases H1 with ⟨%x, %xs, H1⟩
  rcases xs with ⟨l | l2⟩
  · simp only [isNode_nil.to_eq]
    icases H1 with ⟨%lk, %γ2, %c, %heq, Hlock⟩
    rw [heq]
    wp_pures
    wp_bind &acquire _
    iapply acquire_spec $$ Hlock
    iintro ⟨Hlocked, Hpt⟩
    wp_pures
    wp_bind !_
    iapply wp_load $$ Hpt
    iintro !> Hpt
    wp_pures
    wp_bind &Node.new _ _
    sorry
  · sorry

end Specs

/-! ## V2: existential lock invariant (mutation unblocked, contents untracked) -/
section PredicateINV

variable [HeapLangGS hlc GF] [SpinLockG GF]

/-- One unfolding of the **recursive** node predicate. `Φ` is the recursive
occurrence (applied to the successor).  A node is a locked cell holding `(x, nx)`
where `nx` is either `none()` (last node) or **another node** (`Φ nx`). -/
def isNodeE.pre (Φ : Val → IProp GF) (node : Val) : IProp GF := iprop%
  ∃ (lk : Val) (γ : GName) (c : Loc), ⌜node = hl_val((&lk, #c))⌝ ∗
    SpinLock.isLock γ lk iprop(∃ (x : Int) (nx : Val), c ↦ hl_val((#x, &nx)) ∗
      (⌜nx = hl_val(none())⌝ ∨ Φ nx))

/-- `SpinLock.isLock γ lk` is contractive in its invariant: the invariant is stored
under `inv`, which is contractive (it guards with `▷`). -/
theorem isLock_contractive (γ : GName) (lk : Val) :
    OFE.Contractive (SpinLock.isLock (GF := GF) γ lk) where
  distLater_dist := by
    intro n R R' H
    unfold SpinLock.isLock
    refine BI.exists_ne fun l => ?_
    refine BI.and_ne.ne .rfl ?_
    refine OFE.Contractive.distLater_dist (f := inv spinlockN) fun m hm => ?_
    unfold SpinLock.lockInv
    refine BI.exists_ne fun b => ?_
    refine BI.sep_ne.ne .rfl ?_
    cases b
    · exact BI.sep_ne.ne .rfl (H m hm)
    · exact .rfl

/-- The functor is **contractive**: the recursive occurrence `Φ nx` sits under
`isLock`, and `inv` stores `▷`, so `isLock` is contractive in its invariant. -/
instance isNodeE.pre.contractive : OFE.Contractive (isNodeE.pre (GF := GF)) where
  distLater_dist := by
    intro n Φ Φ' H node
    unfold isNodeE.pre
    refine BI.exists_ne fun lk => ?_
    refine BI.exists_ne fun γ => ?_
    refine BI.exists_ne fun c => ?_
    refine BI.sep_ne.ne .rfl ?_
    refine (isLock_contractive γ lk).distLater_dist fun m hm => ?_
    refine BI.exists_ne fun x => ?_
    refine BI.exists_ne fun nx => ?_
    refine BI.sep_ne.ne .rfl ?_
    exact BI.or_ne.ne .rfl (H m hm nx)

/-- `isNodeE node` : `node` is the head of a well-formed, per-node-locked chain
(each node's lock guards its cell and, recursively, its successor). Defined as the
**guarded (Banach) fixpoint** of `isNodeE.pre`. -/
def isNodeE : Val → IProp GF := fixpoint isNodeE.pre

theorem isNodeE_unfold (node : Val) :
    isNodeE (GF := GF) node ⊣⊢ isNodeE.pre isNodeE node :=
  BI.equiv_iff.1 <| fixpoint_unfold (f := isNodeE.pre.toContractiveHom) node

/-- Same as `isNodeE_unfold` but with the body of `isNodeE.pre` spelled out (it is
definitionally equal), so `icases`/`rw` can act on the `∃`. -/
theorem isNodeE_unfold' (node : Val) :
    isNodeE (GF := GF) node ⊣⊢
      iprop(∃ (lk : Val) (γ : GName) (c : Loc), ⌜node = hl_val((&lk, #c))⌝ ∗
        SpinLock.isLock γ lk iprop(∃ (x : Int) (nx : Val), c ↦ hl_val((#x, &nx)) ∗
          (⌜nx = hl_val(none())⌝ ∨ isNodeE nx))) :=
  isNodeE_unfold node

instance isNodeE_persistent (node : Val) : Persistent (isNodeE (GF := GF) node) := by
  rw [(isNodeE_unfold' node).to_eq]
  infer_instance

/-- `isList list` : `list = (hlk, h)` where the header lock `hlk` guards a head cell
`h` holding either `none()` (empty list) or a node handle that starts a valid
`isNodeE` chain.  Non-recursive: it reuses the already-defined `isNodeE`. -/
def isList (list : Val) : IProp GF := iprop%
  ∃ (hlk : Val) (γ : GName) (h : Loc), ⌜list = hl_val((&hlk, #h))⌝ ∗
    SpinLock.isLock γ hlk
      iprop(∃ (hv : Val), h ↦ hv ∗ (⌜hv = hl_val(none())⌝ ∨ isNodeE hv))

/-- Definitional unfold of `isList`, as a `⊣⊢` so `icases`/`iapply _.mpr` can act on
the leading `∃`. -/
theorem isList_unfold (list : Val) :
    isList (GF := GF) list ⊣⊢
      iprop(∃ (hlk : Val) (γ : GName) (h : Loc), ⌜list = hl_val((&hlk, #h))⌝ ∗
        SpinLock.isLock γ hlk
          iprop(∃ (hv : Val), h ↦ hv ∗ (⌜hv = hl_val(none())⌝ ∨ isNodeE hv))) :=
  .rfl

instance isList_persistent (list : Val) : Persistent (isList (GF := GF) list) := by
  rw [(isList_unfold list).to_eq]
  infer_instance

end PredicateINV

section SpecsINV

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF]

/-- `Node.new x next` builds a fresh locked node whose successor is `next`.  The
caller must supply proof that `next` is a valid successor (`none()` or a node). -/
theorem Node.newE_spec (x : Int) (next : Val) (Φ : Val → IProp GF) :
    (⌜next = hl_val(none())⌝ ∨ isNodeE next) -∗
    (∀ node, isNodeE node -∗ Φ node) -∗
    WP hl(&Node.new #x &next) {{ Φ }} := by
  iintro Hnext Hcont
  unfold Node.new
  wp_pures
  wp_bind &newlock _
  iapply newlock_spec
  iintro %v %γ Hγ
  wp_pures
  wp_bind ref(_)
  iapply wp_fupd
  iapply wp_alloc
  iintro !> %c Halloc
  imod Hγ $$ %(iprop(∃ (x0 : Int) (nx : Val), c ↦ hl_val((#x0, &nx)) ∗
      (⌜nx = hl_val(none())⌝ ∨ isNodeE nx))) %⊤ [Halloc Hnext] with Hlock
  · iexists x, next
    iframe Halloc
    iexact Hnext
  imodintro
  wp_pures
  imodintro
  iapply Hcont
  rw [(isNodeE_unfold' _).to_eq]
  iexists v, γ, c
  isplit
  · itrivial
  · iexact Hlock

/-- `Node.insert hd x'` inserts a fresh node right after `hd`; `hd` remains a valid
node.  This is the proof your original `insert_spec` could not reach: the recursive
lock invariant is **existential over the successor**, so `release` can re-establish
it with the newly-inserted node (which is itself a node). -/
theorem Node.insertE_spec (x' : Int) :
    ⊢ ⦃ isNodeE (GF := GF) hd ⦄ hl(&Node.insert &hd #x')
        ⦃ RET hl_val(#()); isNodeE hd ⦄ := by
  iintro %Φ H1 H
  unfold Node.insert
  wp_pures
  icases (isNodeE_unfold' hd) $$ H1 with ⟨%lk, %γ, %c, %heq, #Hlock⟩
  rw [heq]
  wp_pures
  wp_bind &acquire _
  iapply acquire_spec $$ Hlock
  iintro ⟨Hlocked, Hinv⟩
  icases Hinv with ⟨%x, %nx, Hpt, Hnx⟩
  wp_pures
  wp_bind !_
  iapply wp_load $$ Hpt
  iintro !> Hpt
  wp_pures
  wp_bind &Node.new _ _
  iapply Node.newE_spec $$ Hnx
  iintro %new #Hnew
  wp_pures
  wp_bind (_ ← _)
  iapply wp_store $$ Hpt
  iintro !> Hpt
  wp_pures
  ihave HR : iprop(∃ (x0 : Int) (nx0 : Val), c ↦ hl_val((#x0, &nx0)) ∗
      (⌜nx0 = hl_val(none())⌝ ∨ isNodeE nx0)) $$ [Hpt Hnew]
  · iexists x, new
    isplit
    · iexact Hpt
    · iright
      iexact Hnew
  ihave Hres : iprop(SpinLock.isLock γ lk
        iprop(∃ (x0 : Int) (nx0 : Val), c ↦ hl_val((#x0, &nx0)) ∗ (⌜nx0 = hl_val(none())⌝ ∨ isNodeE nx0)) ∗
      (SpinLock.locked γ ∗
        ∃ (x0 : Int) (nx0 : Val), c ↦ hl_val((#x0, &nx0)) ∗ (⌜nx0 = hl_val(none())⌝ ∨ isNodeE nx0)))
      $$ [Hlock Hlocked HR]
  · iframe Hlock Hlocked HR
  iapply release_spec $$ Hres
  iintro -
  iapply H
  iapply (isNodeE_unfold' _).mpr
  iexists lk, γ, c
  isplit
  · itrivial
  · iexact Hlock

end SpecsINV

/-! ## V3 — per-node value ghost (`ExclAuth`), logically-atomic `setValue`

Inv-based SpinLock (Style-1, as V2); the ExclAuth ghost synchronizes the atomic
update: `nodeAuth γ x` (= `●E x`) lives inside the lock invariant pinned to the
stored value; the client trades `nodeContent γ v` (= `◯E v`) through the atomic
update; the linearization point is the frame-preserving update while holding the
lock. -/
section PredicateV3

open OFE COFE CMRA UPred IProp Auth Excl ExclAuth

/-- Discrete OFE of node values. -/
abbrev IntO := LeibnizO Int

/-- Ghost functor: a single `ExclAuth` "ghost variable" over the node value. -/
abbrev NodeValF : COFE.OFunctorPre := AuthURF (OptionOF (ExclOF (constOF IntO)))

/-- Ghost context providing the per-node value resource. -/
class NodeValG (GF : BundledGFunctors) where
  [elemG : ElemG GF NodeValF]

attribute [reducible, instance] NodeValG.elemG

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF] [NodeValG GF]

/-- Server view: authority over the node's current value (sits in the lock inv). -/
def nodeAuth (γ : GName) (v : Int) : IProp GF := iOwn (F := NodeValF) γ (●E (⟨v⟩ : IntO))

/-- Client view (exchangeable): the fragment traded through the atomic update. -/
def nodeContent (γ : GName) (v : Int) : IProp GF := iOwn (F := NodeValF) γ (◯E (⟨v⟩ : IntO))

omit [SpinLockG GF] in
/-- Authority and fragment always agree on the value. -/
theorem nodeVal_agree {γ : GName} {a b : Int} :
    nodeAuth (GF := GF) γ a ∗ nodeContent γ b ⊢ ⌜a = b⌝ := by
  simp only [nodeAuth, nodeContent, ← iOwn_op.to_eq]
  iintro H
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete (A := ExclAuthR (A := IntO)) $$ H with %H
  ipureintro
  exact LeibnizO.eqv_inj (Iris.ExclAuth.agree_L H)

omit [SpinLockG GF] in
/-- Holding both views, atomically update the tracked value: this is the
frame-preserving update at the linearization point. -/
theorem nodeVal_update {γ : GName} {a b : Int} (c : Int) :
    nodeAuth (GF := GF) γ a ∗ nodeContent γ b ==∗ nodeAuth γ c ∗ nodeContent γ c := by
  simp only [nodeAuth, nodeContent, ← iOwn_op.to_eq]
  iapply iOwn_update ExclAuth.update

omit [SpinLockG GF] in
/-- Allocate a fresh value ghost initialized to `v`, handing out both views. -/
theorem nodeVal_alloc (v : Int) :
    ⊢@{IProp GF} |==> ∃ γ, nodeAuth γ v ∗ nodeContent γ v := by
  imod (iOwn_alloc (F := NodeValF) ((●E (⟨v⟩ : IntO)) • (◯E (⟨v⟩ : IntO))) ExclAuth.valid)
    with ⟨%γ, Hown⟩
  imodintro
  iexists γ
  simp only [nodeAuth, nodeContent]
  icases iOwn_op $$ Hown with ⟨Hauth, Hfrag⟩
  iframe

/-- One unfolding of the **value-tracking** recursive node predicate. -/
def isNodeV.pre (Ψ : GName → Val → IProp GF) (γ : GName) (node : Val) : IProp GF := iprop%
  ∃ (lk : Val) (γl : GName) (c : Loc), ⌜node = hl_val((&lk, #c))⌝ ∗
    SpinLock.isLock γl lk iprop(∃ (x : Int) (nx : Val), c ↦ hl_val((#x, &nx)) ∗
      nodeAuth γ x ∗ (⌜nx = hl_val(none())⌝ ∨ ∃ (γ' : GName), Ψ γ' nx))

instance isNodeV.pre.contractive : OFE.Contractive (isNodeV.pre (GF := GF)) where
  distLater_dist := by
    intro n Φ Φ' H γ node
    unfold isNodeV.pre
    refine BI.exists_ne fun lk => ?_
    refine BI.exists_ne fun γl => ?_
    refine BI.exists_ne fun c => ?_
    refine BI.sep_ne.ne .rfl ?_
    refine (isLock_contractive γl lk).distLater_dist fun m hm => ?_
    refine BI.exists_ne fun x => ?_
    refine BI.exists_ne fun nx => ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.or_ne.ne .rfl ?_
    refine BI.exists_ne fun γ' => ?_
    exact H m hm γ' nx

/-- `isNodeV γ node` : `node` heads a value-tracked, per-node-locked chain, with `γ`
the value ghost of *this* node. Guarded (Banach) fixpoint of `isNodeV.pre`. -/
def isNodeV : GName → Val → IProp GF := fixpoint isNodeV.pre

theorem isNodeV_unfold (γ : GName) (node : Val) :
    isNodeV (GF := GF) γ node ⊣⊢ isNodeV.pre isNodeV γ node :=
  BI.equiv_iff.1 <| fixpoint_unfold (f := isNodeV.pre.toContractiveHom) γ node

theorem isNodeV_unfold' (γ : GName) (node : Val) :
    isNodeV (GF := GF) γ node ⊣⊢
      iprop(∃ (lk : Val) (γl : GName) (c : Loc), ⌜node = hl_val((&lk, #c))⌝ ∗
        SpinLock.isLock γl lk iprop(∃ (x : Int) (nx : Val), c ↦ hl_val((#x, &nx)) ∗
          nodeAuth γ x ∗ (⌜nx = hl_val(none())⌝ ∨ ∃ (γ' : GName), isNodeV γ' nx))) :=
  isNodeV_unfold γ node

instance isNodeV_persistent (γ : GName) (node : Val) :
    Persistent (isNodeV (GF := GF) γ node) := by
  rw [(isNodeV_unfold' γ node).to_eq]
  infer_instance

end PredicateV3

section SpecsV3

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF] [NodeValG GF]

/-- `setValue node x` is *logically atomic*: to any client it appears to update the
node's abstract value in a single step.  The linearization point is the physical
store `c ← (x, nx)`, at which we open the client's atomic update to obtain
`nodeContent γ v` (= `◯E v`), combine it with the lock invariant's `nodeAuth γ x'`
(= `●E x'`) to run the frame-preserving update to `x`, and commit `nodeContent γ x`.
Mask `∅`: the store happens after `acquire`, when `spinlockN` is closed, so the
client's atomic update may use the full mask (as in `AtomicLock`). -/
theorem Node.setValue_atomic_spec (γ : GName) (node : Val) (x : Int) :
    isNodeV (GF := GF) γ node ⊢
      ⟪ ∀ v, nodeContent γ v ⟫
        hl(&Node.setValue &node #x) @ ∅
      ⟪ nodeContent γ x | RET hl_val(#()) ⟫ := by
  iintro #Hnode %Φ HAU
  icases (isNodeV_unfold' γ node) $$ Hnode with ⟨%lk, %γl, %c, %heq, #Hlock⟩
  rw [heq]
  unfold Node.setValue
  wp_pures
  wp_bind &acquire _
  iapply acquire_spec $$ Hlock
  iintro ⟨Hlocked, HR⟩
  icases HR with ⟨%x', %nx, Hpt, Hauth, Hdisj⟩
  -- Holding the lock freezes the node, so we commit the abstract update now (a valid
  -- deferred linearization point): open the AU, run the ghost update, commit.
  iapply fupd_wp
  iauopen HAU with ⟨%v, Hcontent, Hclose⟩
  icases Hclose with ⟨-, Hcommit⟩
  ihave Hboth : iprop(nodeAuth γ x' ∗ nodeContent γ v) $$ [Hauth Hcontent]
  · iframe Hauth Hcontent
  imod (nodeVal_update x) $$ Hboth with ⟨Hauth, Hcontent⟩
  imod Hcommit $$ [Hcontent] with HΦ
  · iexact Hcontent
  imodintro
  -- physical: load the cell, store the new value, release
  wp_pures
  wp_bind !_
  iapply wp_load $$ Hpt
  iintro !> Hpt
  wp_pures
  wp_bind (_ ← _)
  iapply wp_store $$ Hpt
  iintro !> Hpt
  wp_pures
  ihave HR : iprop(∃ (x0 : Int) (nx0 : Val), c ↦ hl_val((#x0, &nx0)) ∗
      nodeAuth γ x0 ∗ (⌜nx0 = hl_val(none())⌝ ∨ ∃ (γ' : GName), isNodeV γ' nx0))
      $$ [Hpt Hauth Hdisj]
  · iexists x, nx
    iframe Hpt Hauth Hdisj
  ihave Hres : iprop(SpinLock.isLock γl lk
        iprop(∃ (x0 : Int) (nx0 : Val), c ↦ hl_val((#x0, &nx0)) ∗ nodeAuth γ x0 ∗
          (⌜nx0 = hl_val(none())⌝ ∨ ∃ (γ' : GName), isNodeV γ' nx0)) ∗
      (SpinLock.locked γl ∗ ∃ (x0 : Int) (nx0 : Val), c ↦ hl_val((#x0, &nx0)) ∗ nodeAuth γ x0 ∗
        (⌜nx0 = hl_val(none())⌝ ∨ ∃ (γ' : GName), isNodeV γ' nx0)))
      $$ [Hlock Hlocked HR]
  · iframe Hlock Hlocked HR
  iapply release_spec $$ Hres
  iintro -
  iexact HΦ

end SpecsV3

/-! ## V4 — per-node SUFFIX content, with a logically-atomic `insert`

Each node `hd` carries a ghost `γ` tracking the abstract content of its **whole
suffix** `vs = [hd.val, next.val, …]`.  `Node.insert hd x` inserts `x` right after
`hd`'s value, so the suffix goes `v0 :: rest ⇝ v0 :: x :: rest` — with a
**logically-atomic** spec over `suffixContent γ`.

RA (same ExclAuth as V3, but the payload is a whole `List Int`):
* `suffixAuth γ vs` (= `●E vs`) — authority, lives in `hd`'s lock invariant, pinned to
  the suffix the physical chain currently realizes;
* `suffixContent γ vs` (= `◯E vs`) — the client-facing exchangeable fragment.

Local↔global bridge: `hd`'s lock invariant additionally **owns its successor's
fragment** `suffixContent γ' ws`, so it knows `nx`'s suffix is `ws` and can define its
own `vs = v :: ws`.  Insert transfers that fragment-ownership to the new node. -/
section PredicateV4

open OFE COFE CMRA UPred IProp Auth Excl ExclAuth

/-- Discrete OFE of (suffix) list contents. -/
abbrev ListO := LeibnizO (List Int)

/-- Ghost functor: one `ExclAuth` "ghost variable" over a `List Int`. -/
abbrev SuffixF : COFE.OFunctorPre := AuthURF (OptionOF (ExclOF (constOF ListO)))

/-- Ghost context providing the per-node suffix-content resource. -/
class SuffixG (GF : BundledGFunctors) where
  [elemG : ElemG GF SuffixF]

attribute [reducible, instance] SuffixG.elemG

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF] [SuffixG GF]

/-- Server view: authority over a node's current suffix content (sits in its lock inv). -/
def suffixAuth (γ : GName) (vs : List Int) : IProp GF :=
  iOwn (F := SuffixF) γ (●E (⟨vs⟩ : ListO))

/-- Client view (exchangeable): the fragment traded through the atomic update. -/
def suffixContent (γ : GName) (vs : List Int) : IProp GF :=
  iOwn (F := SuffixF) γ (◯E (⟨vs⟩ : ListO))

omit [SpinLockG GF] in
/-- Authority and fragment always agree on the suffix content. -/
theorem suffixContent_agree {γ : GName} {vs ws : List Int} :
    suffixAuth (GF := GF) γ vs ∗ suffixContent γ ws ⊢ ⌜vs = ws⌝ := by
  simp only [suffixAuth, suffixContent, ← iOwn_op.to_eq]
  iintro H
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete (A := ExclAuthR (A := ListO)) $$ H with %H
  ipureintro
  exact LeibnizO.eqv_inj (Iris.ExclAuth.agree_L H)

omit [SpinLockG GF] in
/-- `icombine`-friendly agreement: keeps both resources while yielding the equality. -/
instance suffixContent_combineGives {γ : GName} {vs ws : List Int} :
    ProofMode.CombineSepGives (suffixAuth (GF := GF) γ vs) (suffixContent γ ws) iprop(⌜vs = ws⌝) where
  combine_sep_gives := suffixContent_agree.trans persistently_pure.2

omit [SpinLockG GF] in
/-- Holding both views, atomically update the suffix content (the LP of insert). -/
theorem suffixContent_update {γ : GName} {vs ws : List Int} (us : List Int) :
    suffixAuth (GF := GF) γ vs ∗ suffixContent γ ws ==∗ suffixAuth γ us ∗ suffixContent γ us := by
  simp only [suffixAuth, suffixContent, ← iOwn_op.to_eq]
  iapply iOwn_update ExclAuth.update

omit [SpinLockG GF] in
/-- Allocate a fresh suffix ghost initialized to `vs`, handing out both views. -/
theorem suffixContent_alloc (vs : List Int) :
    ⊢@{IProp GF} |==> ∃ γ, suffixAuth γ vs ∗ suffixContent γ vs := by
  imod (iOwn_alloc (F := SuffixF) ((●E (⟨vs⟩ : ListO)) • (◯E (⟨vs⟩ : ListO)))
      ExclAuth.valid) with ⟨%γ, Hown⟩
  imodintro
  iexists γ
  simp only [suffixAuth, suffixContent]
  icases iOwn_op $$ Hown with ⟨Hauth, Hfrag⟩
  iframe

/-- Insert `x` right after the head of a suffix: `v0 :: rest ↦ v0 :: x :: rest`. -/
def insAfterHead : List Int → Int → List Int
  | [], x => [x]
  | v0 :: rest, x => v0 :: x :: rest

/-- One unfolding of the recursive **suffix** predicate.  `hd`'s lock invariant holds
its cell, its own authority `suffixAuth γ (v :: ws)`, and — to know its successor's
content `ws` — it **owns the successor's fragment** `suffixContent γ' ws` together with
`Ψ γ' nx` (persistent).  Last node: `nx = none()`, suffix `[v]`. -/
def isNodeSuffix.pre (Ψ : GName → Val → IProp GF) (γ : GName) (hd : Val) : IProp GF := iprop%
  ∃ (lk : Val) (γl : GName) (c : Loc), ⌜hd = hl_val((&lk, #c))⌝ ∗
    SpinLock.isLock γl lk iprop(∃ (v : Int) (nx : Val), c ↦ hl_val((#v, &nx)) ∗
      ( (⌜nx = hl_val(none())⌝ ∗ suffixAuth γ [v])
        ∨ ∃ (γ' : GName) (ws : List Int),
            Ψ γ' nx ∗ suffixContent γ' ws ∗ suffixAuth γ (v :: ws) ))

instance isNodeSuffix.pre.contractive : OFE.Contractive (isNodeSuffix.pre (GF := GF)) where
  distLater_dist := by
    intro n Φ Φ' H γ hd
    unfold isNodeSuffix.pre
    refine BI.exists_ne fun lk => ?_
    refine BI.exists_ne fun γl => ?_
    refine BI.exists_ne fun c => ?_
    refine BI.sep_ne.ne .rfl ?_
    refine (isLock_contractive γl lk).distLater_dist fun m hm => ?_
    refine BI.exists_ne fun v => ?_
    refine BI.exists_ne fun nx => ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.or_ne.ne .rfl ?_
    refine BI.exists_ne fun γ' => ?_
    refine BI.exists_ne fun ws => ?_
    exact BI.sep_ne.ne (H m hm γ' nx) .rfl

/-- `isNodeSuffix γ hd` : `hd` heads a per-node-locked chain whose suffix content is
tracked by ghost `γ`.  Guarded (Banach) fixpoint of `isNodeSuffix.pre`. -/
def isNodeSuffix : GName → Val → IProp GF := fixpoint isNodeSuffix.pre

theorem isNodeSuffix_unfold (γ : GName) (hd : Val) :
    isNodeSuffix (GF := GF) γ hd ⊣⊢ isNodeSuffix.pre isNodeSuffix γ hd :=
  BI.equiv_iff.1 <| fixpoint_unfold (f := isNodeSuffix.pre.toContractiveHom) γ hd

theorem isNodeSuffix_unfold' (γ : GName) (hd : Val) :
    isNodeSuffix (GF := GF) γ hd ⊣⊢
      iprop(∃ (lk : Val) (γl : GName) (c : Loc), ⌜hd = hl_val((&lk, #c))⌝ ∗
        SpinLock.isLock γl lk iprop(∃ (v : Int) (nx : Val), c ↦ hl_val((#v, &nx)) ∗
          ( (⌜nx = hl_val(none())⌝ ∗ suffixAuth γ [v])
            ∨ ∃ (γ' : GName) (ws : List Int),
                isNodeSuffix γ' nx ∗ suffixContent γ' ws ∗ suffixAuth γ (v :: ws) ))) :=
  isNodeSuffix_unfold γ hd

instance isNodeSuffix_persistent (γ : GName) (hd : Val) :
    Persistent (isNodeSuffix (GF := GF) γ hd) := by
  rw [(isNodeSuffix_unfold' γ hd).to_eq]
  infer_instance

end PredicateV4

section SpecsV4

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF] [SuffixG GF]

/-- Build a fresh suffix-tracked node `new = Node.new x next`.  You supply the
successor's suffix info — either it is `none()` (empty suffix `sc = []`), or it is a
node `γn` whose fragment `suffixContent γn sc` you hand over.  The helper allocates a
fresh ghost `γ''`, installs `new`'s lock invariant (owning the successor's fragment),
and returns the persistent `isNodeSuffix γ'' new` plus the fresh fragment
`suffixContent γ'' (x :: sc)`. -/
theorem Node.newSuffix_spec (x : Int) (next : Val) (sc : List Int) (Φ : Val → IProp GF) :
    ((⌜next = hl_val(none())⌝ ∗ ⌜sc = []⌝) ∨
      (∃ γn, isNodeSuffix γn next ∗ suffixContent γn sc)) -∗
    (∀ new γ'', isNodeSuffix γ'' new -∗ suffixContent γ'' (x :: sc) -∗ Φ new) -∗
    WP hl(&Node.new #x &next) {{ Φ }} := by
  iintro Hsucc Hcont
  unfold Node.new
  wp_pures
  wp_bind &newlock _
  iapply newlock_spec
  iintro %lkv %γl Hγl
  wp_pures
  wp_bind ref(_)
  iapply wp_fupd
  iapply wp_alloc
  iintro !> %cnew Halloc
  imod (suffixContent_alloc (x :: sc)) with ⟨%γ'', Hauth'', Hfrag''⟩
  imod Hγl $$ %(iprop(∃ (v0 : Int) (nx0 : Val), cnew ↦ hl_val((#v0, &nx0)) ∗
      ((⌜nx0 = hl_val(none())⌝ ∗ suffixAuth γ'' [v0])
        ∨ ∃ (γ0 : GName) (ws0 : List Int),
            isNodeSuffix γ0 nx0 ∗ suffixContent γ0 ws0 ∗ suffixAuth γ'' (v0 :: ws0))))
      %⊤ [Halloc Hauth'' Hsucc] with Hlock
  · iexists x, next
    iframe Halloc
    icases Hsucc with (⟨%hnone, %hsc⟩ | ⟨%γn, Hnext, Hsc⟩)
    · subst hsc
      ileft
      isplit
      · ipureintro; exact hnone
      · iexact Hauth''
    · iright
      iexists γn, sc
      iframe Hnext Hsc
      iexact Hauth''
  imodintro
  wp_pures
  imodintro
  ihave Hns : isNodeSuffix γ'' hl_val((&lkv, #cnew)) $$ [Hlock]
  · iapply (isNodeSuffix_unfold' _ _).mpr
    iexists lkv, γl, cnew
    isplit
    · itrivial
    · iexact Hlock
  iapply Hcont $$ Hns Hfrag''

/-- Logically-atomic insert-after: to any client, `Node.insert hd x` appears to update
`hd`'s suffix `vs = v0 :: rest` to `v0 :: x :: rest` in one atomic step. -/
theorem Node.insert_suffix_spec (γ : GName) (hd : Val) (x : Int) :
    isNodeSuffix (GF := GF) γ hd ⊢
      ⟪ ∀ vs, suffixContent γ vs ⟫
        hl(&Node.insert &hd #x) @ ∅
      ⟪ suffixContent γ (insAfterHead vs x) | RET hl_val(#()) ⟫ := by
  iintro #Hnode %Φ HAU
  icases (isNodeSuffix_unfold' γ hd) $$ Hnode with ⟨%lk, %γl, %c, %heq, #Hlock⟩
  rw [heq]
  unfold Node.insert
  wp_pures
  wp_bind &acquire _
  iapply acquire_spec $$ Hlock
  iintro ⟨Hlocked, HR⟩
  icases HR with ⟨%x', %nx, Hpt, Heq⟩
  wp_pures
  wp_bind !_
  iapply wp_load $$ Hpt
  iintro !> Hpt
  wp_pures
  wp_bind &Node.new _ _
  icases Heq with (⟨%hnone, Hauth⟩ | ⟨%γn, %ws, Hnext, Hfrag_n, Hauth⟩)
  · -- CASE 1: `hd` is the last node (`nx = none()`), suffix `[x']`.
    subst hnone
    ihave Hs : iprop((⌜hl_val(none()) = hl_val(none())⌝ ∗ ⌜([] : List Int) = []⌝) ∨
        (∃ γn, isNodeSuffix γn hl_val(none()) ∗ suffixContent γn [])) $$ []
    · ileft; isplit <;> (ipureintro; rfl)
    iapply Node.newSuffix_spec $$ Hs
    iintro %new %γ'' Hnew Hfrag
    wp_pures
    wp_bind (_ ← _)
    iapply wp_store $$ Hpt
    iintro !> Hpt
    wp_pures
    -- LP: open the client AU, agree `vs = [x']`, update to `insAfterHead vs x`, commit.
    iapply fupd_wp
    iauopen HAU with ⟨%vs, Hcontent, Hclose⟩
    icases Hclose with ⟨-, Hcommit⟩
    icombine Hauth Hcontent gives %Hvs
    subst vs
    ihave Hboth : iprop(suffixAuth γ [x'] ∗ suffixContent γ [x']) $$ [Hauth Hcontent]
    · iframe Hauth Hcontent
    imod (suffixContent_update [x', x]) $$ Hboth with ⟨Hauth, Hcontent⟩
    imod Hcommit $$ [Hcontent] with HΦ
    · simp only [insAfterHead]
      iexact Hcontent
    imodintro
    -- re-establish `hd`'s lock invariant, now pointing at `new` (right disjunct).
    ihave HR : iprop(∃ (v0 : Int) (nx0 : Val), c ↦ hl_val((#v0, &nx0)) ∗
        ((⌜nx0 = hl_val(none())⌝ ∗ suffixAuth γ [v0])
          ∨ ∃ (γ0 : GName) (ws0 : List Int),
              isNodeSuffix γ0 nx0 ∗ suffixContent γ0 ws0 ∗ suffixAuth γ (v0 :: ws0)))
        $$ [Hpt Hauth Hnew Hfrag]
    · iexists x', new
      iframe Hpt
      iright
      iexists γ'', [x]
      iframe Hnew Hfrag
      iexact Hauth
    ihave Hres : iprop(SpinLock.isLock γl lk
          iprop(∃ (v0 : Int) (nx0 : Val), c ↦ hl_val((#v0, &nx0)) ∗
            ((⌜nx0 = hl_val(none())⌝ ∗ suffixAuth γ [v0])
              ∨ ∃ (γ0 : GName) (ws0 : List Int),
                  isNodeSuffix γ0 nx0 ∗ suffixContent γ0 ws0 ∗ suffixAuth γ (v0 :: ws0))) ∗
        (SpinLock.locked γl ∗ ∃ (v0 : Int) (nx0 : Val), c ↦ hl_val((#v0, &nx0)) ∗
          ((⌜nx0 = hl_val(none())⌝ ∗ suffixAuth γ [v0])
            ∨ ∃ (γ0 : GName) (ws0 : List Int),
                isNodeSuffix γ0 nx0 ∗ suffixContent γ0 ws0 ∗ suffixAuth γ (v0 :: ws0))))
        $$ [Hlock Hlocked HR]
    · iframe Hlock Hlocked HR
    iapply release_spec $$ Hres
    iintro -
    iexact HΦ
  · -- CASE 2: `hd` has a successor node `γn`/`nx` with suffix `ws`.
    ihave Hs : iprop((⌜nx = hl_val(none())⌝ ∗ ⌜ws = []⌝) ∨
        (∃ γn, isNodeSuffix γn nx ∗ suffixContent γn ws)) $$ [Hnext Hfrag_n]
    · iright; iexists γn; iframe Hnext Hfrag_n
    iapply Node.newSuffix_spec $$ Hs
    iintro %new %γ'' Hnew Hfrag
    wp_pures
    wp_bind (_ ← _)
    iapply wp_store $$ Hpt
    iintro !> Hpt
    wp_pures
    iapply fupd_wp
    iauopen HAU with ⟨%vs, Hcontent, Hclose⟩
    icases Hclose with ⟨-, Hcommit⟩
    icombine Hauth Hcontent gives %Hvs
    subst vs
    ihave Hboth : iprop(suffixAuth γ (x' :: ws) ∗ suffixContent γ (x' :: ws)) $$ [Hauth Hcontent]
    · iframe Hauth Hcontent
    imod (suffixContent_update (x' :: x :: ws)) $$ Hboth with ⟨Hauth, Hcontent⟩
    imod Hcommit $$ [Hcontent] with HΦ
    · simp only [insAfterHead]
      iexact Hcontent
    imodintro
    ihave HR : iprop(∃ (v0 : Int) (nx0 : Val), c ↦ hl_val((#v0, &nx0)) ∗
        ((⌜nx0 = hl_val(none())⌝ ∗ suffixAuth γ [v0])
          ∨ ∃ (γ0 : GName) (ws0 : List Int),
              isNodeSuffix γ0 nx0 ∗ suffixContent γ0 ws0 ∗ suffixAuth γ (v0 :: ws0)))
        $$ [Hpt Hauth Hnew Hfrag]
    · iexists x', new
      iframe Hpt
      iright
      iexists γ'', (x :: ws)
      iframe Hnew Hfrag
      iexact Hauth
    ihave Hres : iprop(SpinLock.isLock γl lk
          iprop(∃ (v0 : Int) (nx0 : Val), c ↦ hl_val((#v0, &nx0)) ∗
            ((⌜nx0 = hl_val(none())⌝ ∗ suffixAuth γ [v0])
              ∨ ∃ (γ0 : GName) (ws0 : List Int),
                  isNodeSuffix γ0 nx0 ∗ suffixContent γ0 ws0 ∗ suffixAuth γ (v0 :: ws0))) ∗
        (SpinLock.locked γl ∗ ∃ (v0 : Int) (nx0 : Val), c ↦ hl_val((#v0, &nx0)) ∗
          ((⌜nx0 = hl_val(none())⌝ ∗ suffixAuth γ [v0])
            ∨ ∃ (γ0 : GName) (ws0 : List Int),
                isNodeSuffix γ0 nx0 ∗ suffixContent γ0 ws0 ∗ suffixAuth γ (v0 :: ws0))))
        $$ [Hlock Hlocked HR]
    · iframe Hlock Hlocked HR
    iapply release_spec $$ Hres
    iintro -
    iexact HΦ

/-- Remove-after on suffix content: `v0 :: v1 :: rest ↦ v0 :: rest` (drops the
element right after the head). No-op when there is nothing after the head. -/
def removeAfterHead : List Int → List Int
  | [] => []
  | [v0] => [v0]
  | v0 :: _ :: rest => v0 :: rest

/-- Logically-atomic **remove-after**: to any client, `Node.removeAfter hd` appears to
delete the element right after `hd` in one atomic step, `v0 :: v1 :: rest ⇝ v0 :: rest`.
Two-lock (hd + its successor); the LP is the splice `hd.next := s.next`.  (Statement
only — proof `sorry`.) -/
theorem Node.removeAfter_suffix_spec (γ : GName) (hd : Val) :
    isNodeSuffix (GF := GF) γ hd ⊢
      ⟪ ∀ vs, suffixContent γ vs ⟫
        hl(&Node.removeAfter &hd) @ ∅
      ⟪ suffixContent γ (removeAfterHead vs) | RET hl_val(#()) ⟫ := by
  sorry

end SpecsV4


end LockList

end Iris.Examples.HeapLang
