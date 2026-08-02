module

public import Iris.Examples.SafeAPI
public import Iris.ProgramLogic.Atomic
public import Iris.HeapLang.Lib.IInv
public import Iris.HeapLang.Lib.FracAgreeLocal

@[expose] public section
namespace Iris.Examples.HeapLang

structure Arr where
  cells : List (Nat × Int)
  counter : Nat
deriving DecidableEq, Repr

def Arr.idUqi (arr : Arr) : Prop := (arr.cells.map (·.1)).Nodup

structure Arr.wellFormed (arr : Arr) : Prop where
  idUqi : arr.idUqi
  counterFresh : ∀ p ∈ arr.cells, p.1 < arr.counter

def Arr.init (x : Int) : Arr := { cells := [(0, x)], counter := 1 }

def Arr.insert (arr : Arr) (id : Nat) (val : Int) : Arr × Option Nat :=
  if arr.cells.any (·.1 = id)
    then ({
      cells := arr.cells.flatMap λ c => if c.1 = id then [c, (arr.counter, val)] else [c],
      counter := arr.counter + 1
    }, some arr.counter)
    else (arr, none)

def Arr.cellsBefore (cells : List (Nat × Int)) (id : Nat) : List (Nat × Int) :=
  match cells with
  | [] => []
  | (id', x) :: cs =>
    if id' = id
      then [(id', x)]
      else (id', x) :: Arr.cellsBefore cs id

def Arr.revoke (arr : Arr) (id : Nat) : Arr × Option Unit :=
  if arr.cells.any (·.1 = id)
    then ({
      cells := Arr.cellsBefore arr.cells id,
      counter := arr.counter
    }, some ())
    else (arr, none)

open Iris.HeapLang

def Impl.platformNew : Val := hl_val%
  λ _,
    let cell := ref(#());
    let lock := &RwLock.new cell;
    &Arc.new lock

def Impl.execute : Val := hl_val%
  λ platform exclusive f,
    let gate := &Arc.get(platform);
    if exclusive then
      let _ := &RwLock.write_acquire(gate);
      let result := f #();
      &RwLock.write_release(gate);
      result
    else
      let _ := &RwLock.read_acquire(gate);
      let result := f #();
      &RwLock.read_release(gate);
      result

def Impl.new : Val := hl_val%
  λ value next,
    let contents := ref((#false, (value, next)));
    let lock := &RwLock.new contents;
    &Arc.new lock

def Impl.init : Val := hl_val%
  λ value, &new value (none())

def Impl.insert : Val := hl_val%
  λ platform node value,
    &execute platform #false (λ _,
      let lock := &Arc.get(node);
      let ptr := &RwLock.write_acquire(lock);
      let contents := !ptr;
      let revoked := fst(contents);
      let payload := snd(contents);
      let oldValue := fst(payload);
      let oldNext := snd(payload);
      if revoked then
        (&RwLock.write_release(lock);
         none())
      else
        (let newNode := &new value oldNext;
         let edge := &Arc.clone(newNode);
         ptr ← (#false, (oldValue, some(edge)));
         &RwLock.write_release(lock);  -- LINEARIZATION POINT
         some(newNode)))

def Impl.revokeSuffix : Val := hl_val%
  rec go current :=
    match current with
    | none() => #()
    | some(node) =>
      let lock := &Arc.get(node);
      let ptr := &RwLock.write_acquire(lock);
      let contents := !ptr;
      let payload := snd(contents);
      let value := fst(payload);
      let next := snd(payload);
      ptr ← (#true, (value, none()));
      &RwLock.write_release(lock);
      go next;
      &Arc.drop &RwLock.drop node

def Impl.revoke : Val := hl_val%
  λ platform node,
    &execute platform #true (λ _,
      let lock := &Arc.get(node);
      let ptr := &RwLock.write_acquire(lock);
      let contents := !ptr;
      let revoked := fst(contents);
      let payload := snd(contents);
      let value := fst(payload);
      let next := snd(payload);
      if revoked then
        (&RwLock.write_release(lock);
         none())
      else
        (ptr ← (#false, (value, none()));
         &RwLock.write_release(lock);
         &revokeSuffix next;
         some(#())))


section Specs

open Iris.BI
structure Arrγ where
  γ : GName

section RA

end RA

variable {GF : BundledGFunctors}
variable [HeapLangGS hlc GF] [RwLockG GF] [ArcG GF]

noncomputable section Resources

/-- The one namespace every array invariant lives in.  Clients that want their own
    invariants have to pick a namespace disjoint from this one. -/
def arrN : Namespace := ndot nroot "arr"

def arrContent (γ : Arrγ) (σ : Arr) : IProp GF := iprop% sorry
def isPlatform (ρ : GName) (s : RwLock.State) (platform : Val) : IProp GF := sorry
def isArrInv (γ : Arrγ) (γp : GName) (platform : Val) : IProp GF := sorry
instance instIsArrInvPersistent (γ : Arrγ) (γp : GName) (platform : Val) :
    Persistent (isArrInv (GF := GF) γ γp platform) := by sorry
def arrFrag (γ : Arrγ) (σ : Arr) : IProp GF := sorry
def Arr.isList (γ : Arrγ) (σ : Arr) : IProp GF := sorry
def Arr.isId (γ : Arrγ) (node : Val) (id : Nat) : IProp GF := sorry

end Resources


theorem Impl.init_spec (x : Int) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.init #x)
    ⦃ root, RET root;
      ∃ γ, Arr.isList γ (Arr.init x) ∗ Arr.isId γ root 0 ⦄ := by
  sorry

theorem Impl.platformNew_spec :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.platformNew #())
    ⦃ platform, RET platform;
      ∃ γp, isPlatform γp .free platform ⦄ := by sorry

theorem Impl.isList_bind
    (γ : Arrγ) (γp : GName) (σ : Arr) (platform : Val) :
  ⊢@{IProp GF}
    Arr.isList γ σ -∗
    isPlatform γp .free platform ={⊤}=∗
    isArrInv γ γp platform ∗ arrFrag γ σ := by
  sorry

theorem Impl.Arr.isId_clone_spec
    (γ : Arrγ) (γp : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv γ γp platform -∗
    ⦃ Arr.isId γ node id ⦄
      hl(&Arc.clone &node)
    ⦃ RET node;
      Arr.isId γ node id ∗ Arr.isId γ node id ⦄ := by sorry


theorem Impl.execute_shared_spec
    (γ : Arrγ) (γP : GName) (platform f : Val) (Q : Arr → Arr → Val → IProp GF) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    (isArrInv γ γP platform -∗ rwGuard γP .read -∗
       ⟪ ∀ σ, arrFrag γ σ ⟫
         hl(&f #()) @ ↑arrN
       ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r ∗ rwGuard γP .read | RET r ⟫) -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&Impl.execute &platform #false &f) @ ↑arrN
    ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r | RET r ⟫ := by
  sorry


theorem Impl.execute_exclusive_spec
    (γ : Arrγ) (γP : GName) (platform f : Val) (Q : Arr → Arr → Val → IProp GF) :
  ⊢@{IProp GF}
    isArrInv γ γP platform -∗
    (∀ σ,
       ⦃ arrContent γ σ ∗ rwGuard γP .write ⦄
         hl(&f #())
       ⦃ r, RET r; ∃ σ', arrContent γ σ' ∗ Q σ σ' r ∗ rwGuard γP .write ⦄) -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&Impl.execute &platform #true &f) @ ↑arrN
    ⟪ ∃ r, ∃ σ', arrFrag γ σ' ∗ Q σ σ' r | RET r ⟫ := by sorry

theorem Impl.insert_spec
    (γ : Arrγ) (γp : GName) (platform node : Val) (id : Nat) (x : Int) :
  ⊢@{IProp GF}
    isArrInv γ γp platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&Impl.insert &platform &node #x) @ ↑arrN
    ⟪ ∃ ret,
        arrFrag γ (Arr.insert σ id x).1 ∗
        Arr.isId γ node id ∗
        match (Arr.insert σ id x).2 with
        | none => iprop% ⌜ret = hl_val(none())⌝
        | some nid => iprop%
            ∃ newNode : Val,
              ⌜ret = hl_val(some(&newNode))⌝ ∗
              Arr.isId γ newNode nid
      | RET ret
    ⟫ := by sorry

theorem Impl.revoke_spec
    (γ : Arrγ) (γp : GName) (platform node : Val) (id : Nat) :
  ⊢@{IProp GF}
    isArrInv γ γp platform -∗
    Arr.isId γ node id -∗
    ⟪ ∀ σ, arrFrag γ σ ⟫
      hl(&Impl.revoke &platform &node) @ ↑arrN
    ⟪ arrFrag γ (Arr.revoke σ id).1 ∗ Arr.isId γ node id
      | RET match (Arr.revoke σ id).2 with
            | none => hl_val(none())
            | some _ => hl_val(some(#()))
    ⟫ := by sorry

end Specs

end Iris.Examples.HeapLang
