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
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.SubstitutionSystems.Relativization.Protomonads.
Require Import UniMath.SubstitutionSystems.Relativization.DoublyRelativizedRefinedContainment.

Require Import UniMath.SubstitutionSystems.LamSignature.

Local Open Scope cat.

Section lifting_def.

  Context {C D E : precategory}.
  Context (hs : has_homsets E).
  Context (J : functor C D).
  Context (hsD : has_homsets D).

Let homsetsCE : has_homsets [C, E, hs] := functor_category_has_homsets _ _ hs.

  Context (H : functor [C, E, hs] [C, E, hs]).

  Definition lifting_of_relativized_containment : UU :=
    ∏ (T: functor C E), functor_composite (functor_opp (pair_functor (functor_ptm_forget hsD J) (functor_identity _)))
                                          (drelrefcont_functor hs J hsD T) ⟹
                       functor_composite (functor_opp (pair_functor (functor_ptm_forget hsD J) H))
                                          (drelrefcont_functor hs J hsD (H T)).

  Definition lifting_of_relativized_containment_op_type : UU := ∏ (Ze: precategory_Ptm hsD J) (X T: functor C E),
    drelrefcont_type J (pr1 Ze) X T -> drelrefcont_type J (pr1 Ze) (H X) (H T).

  Definition lifting_of_relativized_containment_op:
    lifting_of_relativized_containment -> lifting_of_relativized_containment_op_type.
  Proof.
    intros lift Ze X T mbind.
    exact (lift T (Ze,,X) mbind).
  Defined.

  Lemma pointwise_naturality_of_lifting (lift: lifting_of_relativized_containment) (T: functor C E)
        {Ze Ze' : (precategory_Ptm hsD J)^op} (π : (precategory_Ptm hsD J)^op ⟦Ze, Ze'⟧)
        {X X' : [C, E, hs]^op} (α : [C, E, hs]^op ⟦ X, X' ⟧)
        (mbind : pr1 (drelrefcont_functor hs J hsD T (pr1 Ze,,X))) (c1 c2 : C) (f : D ⟦ J c1, pr1 Ze' c2 ⟧):
    pr1 (pr1 (lift T) (Ze',,X') (# (drelrefcont_functor hs J hsD T)
                                   ((pr1 π,,α):(([C, D, hsD] ⊠ [C, E, hs])^op)⟦(pr1 Ze,,X),(pr1 Ze',,X')⟧) mbind)) c1 c2 f =
    drelrefcont_functor_on_morphism_op J  (H T) (pr1 π) (# H α) (pr1 (pr1 (lift T) (Ze,,X) mbind)) c1 c2 f.
  Proof.
    generalize f. apply toforallpaths. clear f.
    generalize c2. apply toforallpaths. clear c2.
    generalize c1. apply toforallpaths. clear c1.
    assert (aux :=  pr2 (lift T) (Ze,,X) (Ze',,X') (π,,α)).
    apply toforallpaths in aux.
    assert (auxinst := maponpaths pr1 (aux mbind)).
    exact auxinst.
  Qed.

End lifting_def.

Section Examples.

  (** first the motivating example of self-composition that is not relativized but otherwise challenging *)

  Context {C : precategory}.
  Context (hs : has_homsets C).

  Local Notation "'EndC'":= ([C, C, hs]) .

  (** first try the operation only *)
  Definition lifting_of_flat_op_op (Ze : precategory_Ptm hs (functor_identity C)) (X T: functor C C) (mbind: drelrefcont_type (functor_identity C) (pr1 Ze) X T) :
    drelrefcont_op (functor_identity C) (pr1 Ze) (Flat_H C hs X) (Flat_H C hs T).
  Proof.
    intros c1 c2 f.
    exact (pr1 mbind (X c1) (T c2) (pr1 mbind c1 c2 f · (pr2 Ze) (T c2))). (** we need protomonads! *)
  Defined.

  Lemma lifting_of_flat_op_ok (Ze : precategory_Ptm hs (functor_identity C)) (X T: functor C C) (mbind: drelrefcont_type (functor_identity C) (pr1 Ze) X T) :
    drelrefcont_natural (lifting_of_flat_op_op Ze X T mbind).
  Proof.
    intros c1 c1' c2 c2' h1 h2 f.
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

  Definition lifting_of_flat_op: lifting_of_relativized_containment_op_type hs (functor_identity C) hs (Flat_H C hs).
  Proof.
    intros Ze X T mbind.
    exists (lifting_of_flat_op_op Ze X T mbind).
    exact (lifting_of_flat_op_ok Ze X T mbind).
  Defined.

  (* now with naturality in [Ze] and [X]: *)
  Definition lifting_of_flat: lifting_of_relativized_containment hs (functor_identity C) hs (Flat_H C hs).
  Proof.
    intro T.
    use make_nat_trans.
    - intros ZeX mbind.
      cbn in ZeX.
      cbn.
      apply lifting_of_flat_op.
      cbn in mbind.
      exact mbind.
    - intros ZeX ZeX' πα.
      cbn in ZeX, ZeX', πα.
      induction ZeX as [Ze X]. induction ZeX' as [Ze' X']. induction πα as [π α].
      (* show_id_type. *)
      apply funextfun. intro mbind.
      apply (drelrefcont_type_eq hs).
      intros c1 c2 f.
      cbn.
      unfold drelrefcont_functor_on_morphism_op, lifting_of_flat_op_op, Flat_H_mor, HorizontalComposition.horcomp.
      cbn.
      repeat rewrite <- assoc.
      apply maponpaths.
      cbn in mbind.
      assert (aux := pr2 mbind _ _ _ _ (pr1 α c1) (identity (T c2)) (pr1 mbind c1 c2 (f · pr1 π c2) · pr2 Ze (T c2))).
      rewrite functor_id in aux.
      rewrite id_right in aux.
      eapply pathscomp0.
      2: { apply pathsinv0.
           exact aux.
      }
      rewrite functor_id.
      rewrite id_right.
      do 3 apply maponpaths.
      apply (pr2 π).
  Defined.

End Examples.
