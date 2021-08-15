(** **********************************************************
    a relativized version of pointed endofunctors

Ralph Matthes

2021


************************************************************)


(** **********************************************************

Contents :

-    Definition of precategory of protomonads over a functor
-    Forgetful functor to functor precategory
-    instantiation to the non-relativized case

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.PointedFunctors.

Local Open Scope cat.

Section def_ptm.

  Context {C D : precategory}.
  Context (hs : has_homsets D).
  Context (J : functor C D).

Definition ptm_obj : UU := ∑ F : functor C D, J ⟹ F.

Coercion functor_from_ptm_obj (F : ptm_obj) : functor C D := pr1 F.

Definition ptm_pt (F : ptm_obj) : J ⟹ F := pr2 F.

Definition is_ptm_mor {F G : ptm_obj}(α: F ⟹ G) : UU := ∏ c : C, ptm_pt F c · α c = ptm_pt G c.

Definition ptm_mor (F G : ptm_obj) : UU :=
  ∑ α : F ⟹ G, is_ptm_mor α.

Coercion nat_trans_from_ptm_mor {F G : ptm_obj} (a : ptm_mor F G) : nat_trans F G := pr1 a.

Lemma eq_ptm_mor {F G : ptm_obj} (a b : ptm_mor F G)
  : a = b ≃ (a : F ⟹ G) = b.
Proof.
  apply subtypeInjectivity.
  intro x.
  apply impred; intros ?.
  apply hs.
Defined.

Definition ptm_mor_commutes {F G : ptm_obj} (α : ptm_mor F G)
  : ∏ c : C, ptm_pt F c · α c = ptm_pt G c.
Proof.
  exact (pr2 α).
Qed.

Definition ptm_id (F : ptm_obj) : ptm_mor F F.
Proof.
  exists (nat_trans_id _ ).
  abstract (
      intro c;
      apply id_right) .
Defined.

Definition ptm_comp {F F' F'' : ptm_obj} (α : ptm_mor F F') (α' : ptm_mor F' F'')
  : ptm_mor F F''.
Proof.
  exists (nat_trans_comp _ _ _ α α').
  abstract (
      intro c; simpl;
      rewrite assoc ;
      set (H:=ptm_mor_commutes α c); simpl in H; rewrite H; clear H ;
      set (H:=ptm_mor_commutes α' c); simpl in H; rewrite H; clear H ;
      apply idpath ).
Defined.

Definition ptm_ob_mor : precategory_ob_mor.
Proof.
  exists ptm_obj.
  exact ptm_mor.
Defined.

Definition ptm_precategory_data : precategory_data.
Proof.
  exists ptm_ob_mor.
  exists ptm_id.
  exact @ptm_comp.
Defined.

Lemma is_precategory_ptm : is_precategory ptm_precategory_data.
Proof.
  repeat split; simpl; intros.
  - apply (invmap (eq_ptm_mor _ _ )).
    apply (@id_left (functor_precategory C D hs)).
  - apply (invmap (eq_ptm_mor _ _ )).
    apply (@id_right (functor_precategory _ _ hs )).
  - apply (invmap (eq_ptm_mor _ _ )).
    apply (@assoc (functor_precategory _ _ hs)).
  - apply (invmap (eq_ptm_mor _ _ )).
    apply (@assoc' (functor_precategory _ _ hs)).
Qed.

Definition precategory_Ptm : precategory := tpair _ _ is_precategory_ptm.

Definition J_Ptm : precategory_Ptm.
Proof.
  exists J.
  exact (nat_trans_id _ ).
Defined.

Lemma eq_ptm_mor_precat {F G : precategory_Ptm} (a b : F --> G)
  : a = b ≃ (a : ptm_mor F G) = b.
Proof.
  use tpair.
  intro H.
  exact H.
  apply idisweq.
Defined.

(** Forgetful functor to functor category *)

Definition ptm_forget_data : functor_data precategory_Ptm [C, D, hs].
Proof.
  exists (λ a, pr1 a).
  exact (λ a b f, pr1 f).
Defined.

Lemma is_functor_ptm_forget : is_functor ptm_forget_data.
Proof.
  split; intros; red; intros; apply idpath.
Qed.

Definition functor_ptm_forget : functor _ _ := tpair _ _ is_functor_ptm_forget.

End def_ptm.

Section instantiate_with_id.

  Context {C : precategory}.
  Context (hs : has_homsets C).


  Lemma Ptd_is_instance_of_Ptm: precategory_ob_mor_from_precategory_data (precategory_Ptm hs (functor_identity C)) =
                                precategory_ob_mor_from_precategory_data (precategory_Ptd C hs).
  Proof.
     apply idpath.
  Qed.

  (* morally, both precategories are identical - the code from [PointedFunctors.v] was mostly copied *)

End instantiate_with_id.
