/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.ULiftInst
public import Iris.Algebra.OFE
public import Iris.Algebra.UPred
public import Iris.Algebra.GenMap
public import Iris.Algebra.COFESolver
public import Init.Data.Vector

@[expose] public section

namespace Iris

open COFE

abbrev GType := Nat

@[rocq_alias gFunctor]
abbrev GFunctor.{u, v, w} := Σ F : OFunctorPre.{u, v, w}, RFunctorContractive F

@[rocq_alias gFunctors]
def BundledGFunctors.{u, v, w} := GType → GFunctor.{u, v, w}

def BundledGFunctors.default : BundledGFunctors := fun _ => ⟨constOF (ULift Unit), by infer_instance⟩

def BundledGFunctors.set (GF : BundledGFunctors.{u, v, w}) (i : Nat) (FB : GFunctor.{u, v, w}) :
    BundledGFunctors.{u, v, w} :=
  fun j => if j = i then FB else GF j

#rocq_ignore gid "Use `GType` (= `Nat`) to index `BundledGFunctors` directly."
#rocq_ignore gFunctors.nil "`BundledGFunctors` is a function `GType → GFunctor`; no list combinators."
#rocq_ignore gFunctors.singleton "`BundledGFunctors` is a function `GType → GFunctor`; no list combinators."
#rocq_ignore gFunctors.app "`BundledGFunctors` is a function `GType → GFunctor`; no list combinators."

@[rocq_alias gname]
abbrev GName := Nat

#rocq_ignore gnameO "Use `LeibnizO GName`."

@[rocq_alias iResF]
abbrev IResF (GF : BundledGFunctors.{u, u, u}) : OFunctorPre.{u, u, u} :=
  DiscreteFunOF (fun i => GenMapOF (GF i).fst)

#rocq_ignore subG "Superseded by `ElemG`."
#rocq_ignore subG_inv "Lemma about `subG`; obsolete with `ElemG`."
#rocq_ignore subG_refl "Lemma about `subG`; obsolete with `ElemG`."
#rocq_ignore subG_app_l "Lemma about `subG`; obsolete with `ElemG`."
#rocq_ignore subG_app_r "Lemma about `subG`; obsolete with `ElemG`."

instance (GF : BundledGFunctors.{u, u, u}) (i : GName) : RFunctorContractive ((GF i).fst) := (GF i).snd

section IProp

variable (GF : BundledGFunctors.{u, u, u})

@[rocq_alias iProp_solution.iPrePropO, rocq_alias iProp_solution.iProp_result]
def IPre : Type u := OFunctor.Fix (UPredOF (IResF GF))

@[rocq_alias iProp_solution.iPreProp_cofe]
instance : COFE (IPre GF) := inferInstanceAs (COFE (OFunctor.Fix _))

@[rocq_alias iProp_solution.iResUR]
def IResUR : Type u := (i : GType) → GenMap (GF i |>.fst (IPre GF) (IPre GF))

#rocq_ignore iResUR "Sealed copy of `iProp_solution.iResUR`; not needed since Lean does not seal it."

instance : UCMRA (IResUR GF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GenMap (GF i |>.fst (IPre GF) (IPre GF)))

abbrev IProp : Type u := UPred (IResUR GF)

@[rocq_alias iProp_solution.iProp_unfold]
def IProp.unfold : IProp GF -n> IPre GF :=
  OFE.Iso.hom <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

@[rocq_alias iProp_solution.iProp_fold]
def IProp.fold : IPre GF -n> IProp GF :=
  OFE.Iso.inv <| OFunctor.Fix.iso (F := (UPredOF (IResF GF)))

end IProp

end Iris
