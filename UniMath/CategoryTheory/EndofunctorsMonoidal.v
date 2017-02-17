(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015

Modified by: Anders Mörtberg, 2016
             Ralph Matthes, 2017

************************************************************)


(** **********************************************************

Contents :

- Definition of the (weak) monoidal structure on endofunctors
  (however, the definitions are not confined to endofunctors)


************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

(** There is a monoidal structure on endofunctors, given by composition.
    While this is considered to be strict in set-theoretic category theory,
    it ain't strict in type theory with respect to convertibility.
    So we consider it to be a weak monoidal structure instead.
*)
Section Monoidal_Structure_on_Endofunctors.

(** while this is normally used for endofunctors, it can be done more generally *)

Context {C D : precategory}.

Definition ρ_functor (X : functor C D) :
  nat_trans (functor_composite X (functor_identity D)) X := nat_trans_functor_id_right X.

Definition ρ_functor_inv (X : functor C D) :
  nat_trans X (functor_composite X (functor_identity D)) := ρ_functor X.

Definition λ_functor (X : functor C D) :
  nat_trans (functor_composite (functor_identity C) X) X := ρ_functor X.

Definition λ_functor_inv (X : functor C D) :
  nat_trans X (functor_composite (functor_identity C) X) := ρ_functor X.


Context {E F: precategory}.

Definition α_functor (X : functor C D)(Y : functor D E)(Z : functor E F) :
  nat_trans (functor_composite (functor_composite X Y) Z)
            (functor_composite X (functor_composite Y Z)) := nat_trans_functor_assoc X Y Z.

Definition α_functor_inv (X : functor C D)(Y : functor D E)(Z : functor E F) :
  nat_trans (functor_composite X (functor_composite Y Z))
            (functor_composite (functor_composite X Y) Z) := α_functor X Y Z.

End Monoidal_Structure_on_Endofunctors.
