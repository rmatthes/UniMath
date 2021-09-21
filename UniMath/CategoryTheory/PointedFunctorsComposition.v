
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-  Definition of composition of pointed functors


************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Section def_ptd.

Variable C : precategory.
Variable hs : has_homsets C.

Definition ptd_compose (Z Z' : ptd_obj C hs) : precategory_Ptd C hs.
Proof.
  exists (functor_compose hs hs Z Z').
  apply (# (functorial_composition _ _ _ hs hs) (ptd_pt _ hs Z,, ptd_pt _ hs Z':
    precategory_binproduct [C, C, hs] [C, C, hs] ⟦ (functor_identity_as_ob C hs,,functor_identity_as_ob C hs),
                                                   (pr1 Z,, pr1 Z') ⟧)).
Defined.

End def_ptd.
