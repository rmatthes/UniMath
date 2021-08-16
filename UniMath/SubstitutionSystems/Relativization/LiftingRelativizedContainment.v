(**

Ralph Matthes
2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.SubstitutionSystems.Relativization.Protomonads.
Require Import UniMath.SubstitutionSystems.Relativization.DoublyRelativizedRefinedContainment.

Require Import UniMath.SubstitutionSystems.LamSignature.

Local Open Scope cat.

Section lifting_def.

  Context {C D E : precategory}.
  Context (hsD : has_homsets D).
  Context (hs : has_homsets E).
  Context {J : functor C D}.
  Context (Ze : precategory_Ptm hsD J).

Let homsetsCE : has_homsets [C, E, hs] := functor_category_has_homsets _ _ hs.

  Context (H : functor [C, E, hs] [C, E, hs]).

  Definition lifting_of_relativized_containment : UU :=
    ∏ (T: functor C E), drelrefcont_left_functor hs J (pr1 Ze) T ⟹
                        functor_composite (functor_opp H) (drelrefcont_left_functor hs J (pr1 Ze) (H T)).

  Definition lifting_of_relativized_containment_op_type : UU :=
    ∏ (X T: functor C E), drelrefcont_type J (pr1 Ze) X T -> drelrefcont_type J (pr1 Ze) (H X) (H T).

  Definition lifting_of_relativized_containment_op:
    lifting_of_relativized_containment -> lifting_of_relativized_containment_op_type.
  Proof.
    intros lift X T mbind.
    exact (lift T X mbind).
  Defined.

  Lemma pointwise_naturality_of_lifting (lift: lifting_of_relativized_containment) (T: functor C E)
        (X X' : [C, E, hs]^op) (α : [C, E, hs]^op ⟦ X, X' ⟧)
        (mbind : pr1 (drelrefcont_left_functor hs J (pr1 Ze) T X)) (C1 C2 : C) (f : D ⟦ J C1, pr1 Ze C2 ⟧):
          pr1 (pr1 (lift T) X' (# (drelrefcont_left_functor hs J (pr1 Ze) T) α mbind)) C1 C2 f =
          drelrefcont_left_functor_on_morphism_op J (pr1 Ze) (H T) (# H α) (pr1 (pr1 (lift T) X mbind)) C1 C2 f.
  Proof.
    generalize f. apply toforallpaths. clear f.
    generalize C2. apply toforallpaths. clear C2.
    generalize C1. apply toforallpaths. clear C1.
    assert (aux :=  pr2 (lift T) X X' α).
    apply toforallpaths in aux.
    assert (auxinst := maponpaths pr1 (aux mbind)).
    exact auxinst.
Qed.

End lifting_def.

Section Examples.

  (** first the motivating example of self-composition that is not relativized but otherwise challenging *)

  Context {C : precategory}.
  Context (hs : has_homsets C).
  Context (Ze : precategory_Ptm hs (functor_identity C)).

  Local Notation "'EndC'":= ([C, C, hs]) .

  (** first try the operation only *)
  Definition lifting_of_flat_op_op (X T: functor C C) (mbind: drelrefcont_type (functor_identity C) (pr1 Ze) X T) :
    drelrefcont_op (functor_identity C) (pr1 Ze) (Flat_H C hs X) (Flat_H C hs T).
  Proof.
    intros C1 C2 f.
    exact (pr1 mbind (X C1) (T C2) (pr1 mbind C1 C2 f · (pr2 Ze) (T C2))). (** we need protomonads! *)
  Defined.

  Lemma lifting_of_flat_op_ok (X T: functor C C) (mbind: drelrefcont_type (functor_identity C) (pr1 Ze) X T) :
    drelrefcont_natural (lifting_of_flat_op_op X T mbind).
  Proof.
    intros C1 C1' C2 C2' h1 h2 f.
    cbn.
    eapply pathscomp0.
    { apply (pr2 mbind). }
    unfold lifting_of_flat_op_op.
    apply maponpaths.
    cbn.
    eapply pathscomp0.
    2: { apply cancel_postcomposition.
         apply (pr2 mbind).
    }
    eapply pathscomp0.
    { do 2 rewrite <- assoc.
      do 2 apply maponpaths.
      apply pathsinv0.
      apply (nat_trans_ax (pr2 Ze) _ _ (# T h2)).
    }
    do 2 rewrite assoc.
    apply idpath.
  Qed.

  Definition lifting_of_flat_op: lifting_of_relativized_containment_op_type hs hs Ze (Flat_H C hs).
  Proof.
    intros X T mbind.
    exists (lifting_of_flat_op_op X T mbind).
    exact (lifting_of_flat_op_ok X T mbind).
  Defined.

  (* now with naturality in [X]: *)
  Definition lifting_of_flat: lifting_of_relativized_containment hs hs Ze (Flat_H C hs).
  Proof.
    intro T.
    use make_nat_trans.
    - intros X mbind.
      cbn in X.
      cbn.
      apply lifting_of_flat_op.
      cbn in mbind.
      exact mbind.
    - intros X X' α.
      cbn in X, X', α.
      (* show_id_type. *)
      apply funextfun. intro mbind.
      apply (drelrefcont_type_eq hs).
      intros C1 C2 f.
      cbn.
      unfold drelrefcont_left_functor_on_morphism_op, lifting_of_flat_op_op, Flat_H_mor, HorizontalComposition.horcomp.
      cbn.
      repeat rewrite <- assoc.
      apply maponpaths.
      cbn in mbind.
      assert (aux := pr2 mbind _ _ _ _ (α C1) (identity (T C2)) (pr1 mbind C1 C2 f · pr2 Ze (T C2))).
      rewrite functor_id in aux.
      rewrite id_right in aux.
      eapply pathscomp0.
      2: { apply pathsinv0.
           exact aux.
      }
      rewrite functor_id.
      rewrite id_right.
      apply idpath.
  Defined.

End Examples.
