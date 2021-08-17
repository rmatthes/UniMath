(** inspired by relativized refined containment as studied in Abel, Matthes Uustalu, TCS 333 (2005) 3 – 66, doi:10.1016/j.tcs.2004.10.017 *)

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
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.SubstitutionSystems.Relativization.Protomonads.

Local Open Scope cat.

Notation "A ⊠ B" := (precategory_binproduct A B) (at level 38).

Section containment_def.

  Context {C E : precategory}.
  Context (hs : has_homsets E).
  Context (X T : functor C E).

  Definition containment_op : UU := ∏ (c1 c2: C), C⟦c1, c2⟧ -> E⟦X c1, T c2⟧.

  Definition containment_natural (leq: containment_op) : UU :=
    forall (c1 c1' c2 c2': C) (h1: c1' --> c1) (h2: c2 --> c2') (f: c1 --> c2),
      #X h1 · (leq c1 c2 f) · #T h2 = leq c1' c2' (h1 · f · h2).

  Lemma isaprop_containment_natural (leq: containment_op): isaprop (containment_natural leq).
  Proof.
    repeat (apply impred; intros).
    apply hs.
  Qed.

  Definition containment_type : UU := ∑ (leq: containment_op), containment_natural leq.

  Lemma containment_type_eq (leq leq': containment_type):
    (forall (c1 c2: C) (f: c1 --> c2), pr1 leq c1 c2 f = pr1 leq' c1 c2 f) -> leq = leq'.
  Proof.
    intro Hyp.
    assert (Hyp' : pr1 leq = pr1 leq').
    { apply funextsec; intro c1. apply funextsec; intro c2. apply funextsec; intro f.
      apply Hyp.
    }
    apply (total2_paths_f Hyp'), proofirrelevance, isaprop_containment_natural.
  Qed.

  Lemma isaset_containment_type: isaset containment_type.
  Proof.
    apply (isofhleveltotal2 2).
    - apply impred; intro c1. apply impred; intro c2. apply impred; intro f. apply hs.
    - intro leq. apply isasetaprop, isaprop_containment_natural.
  Qed.

  Definition containment: hSet := containment_type ,, isaset_containment_type.

End containment_def.

Section drelrefcont_def.

  Context {C D E : precategory}.
  Context (hs : has_homsets E).
  Context (J Z : functor C D).
  Context (X T : functor C E).

  Definition drelrefcont_op : UU := ∏ (c1 c2: C), D⟦J c1, Z c2⟧ -> E⟦X c1, T c2⟧.
  Definition drelrefcont_natural (mbind: drelrefcont_op) : UU :=
    forall (c1 c1' c2 c2': C) (h1: c1' --> c1) (h2: c2 --> c2') (f: J c1 --> Z c2),
      #X h1 · (mbind c1 c2 f) · #T h2 = mbind c1' c2' (#J h1 · f · #Z h2).

  Lemma isaprop_drelrefcont_natural (mbind: drelrefcont_op): isaprop (drelrefcont_natural mbind).
  Proof.
    repeat (apply impred; intros).
    apply hs.
  Qed.

  Definition drelrefcont_type : UU := ∑ (mbind: drelrefcont_op), drelrefcont_natural mbind.

  Lemma drelrefcont_type_eq (mbind mbind': drelrefcont_type): (forall (c1 c2: C) (f: J c1 --> Z c2), pr1 mbind c1 c2 f = pr1 mbind' c1 c2 f) -> mbind = mbind'.
  Proof.
    intro Hyp.
    assert (Hyp' : pr1 mbind = pr1 mbind').
    { apply funextsec; intro c1. apply funextsec; intro c2. apply funextsec; intro f.
      apply Hyp.
    }
    apply (total2_paths_f Hyp'), proofirrelevance, isaprop_drelrefcont_natural.
  Qed.

  Lemma isaset_drelrefcont_type: isaset drelrefcont_type.
  Proof.
    apply (isofhleveltotal2 2).
    - apply impred; intro c1. apply impred; intro c2. apply impred; intro f. apply hs.
    - intro mbind. apply isasetaprop, isaprop_drelrefcont_natural.
  Qed.

  Definition drelrefcont: hSet := drelrefcont_type ,, isaset_drelrefcont_type.

End drelrefcont_def.

Arguments drelrefcont_natural {_ _ _ _ _ _ _ } _.

Section leq_from_mbind.

  Context {C D E : precategory}.
  Context (hs : has_homsets E).
  Context (J : functor C D).
  Context (hsD : has_homsets D).
  Context (Ze : precategory_Ptm hsD J).
  Context (X T : functor C E).


  Definition leq_from_mbind (mbind: drelrefcont_type J (pr1 Ze) X T): containment_type X T.
  Proof.
    use tpair.
    - intros c1 c2 f.
      exact (pr1 mbind c1 c2 (#J f · pr2 Ze c2)).
    - intros c1 c1' c2 c2' h1 h2 f.
      eapply pathscomp0.
      { apply (pr2 mbind). }
      apply maponpaths.
      do 2 rewrite functor_comp.
      repeat rewrite <- assoc.
      do 2 apply maponpaths.
      apply pathsinv0.
      apply nat_trans_ax.
  Defined.

End leq_from_mbind.

Section drelrefcont_dependent_on_Z_and_X.

  Context {C D E : precategory}.
  Context (hs : has_homsets E).
  Context (J : functor C D).
  Context (hsD : has_homsets D).
  Context (T : functor C E).

  Definition drelrefcont_functor_on_morphism_op {Z Z': functor C D} (π: Z' ⟹ Z)
             {X X': functor C E} (α: X' ⟹ X) (mbind: drelrefcont_op J Z X T): drelrefcont_op J Z' X' T.
  Proof.
    intros c1 c2 f.
    exact (α c1 · mbind c1 c2 (f · π c2)).
  Defined.

  Lemma drelrefcont_functor_on_morphism_op_ok {Z Z': functor C D} (π: Z' ⟹ Z)
        {X X': functor C E} (α: X' ⟹ X) (mbind: drelrefcont_op J Z X T):
    drelrefcont_natural mbind -> drelrefcont_natural (drelrefcont_functor_on_morphism_op π α mbind).
  Proof.
    intro Hyp.
    intros c1 c1' c2 c2' h1 h2 f.
    unfold drelrefcont_functor_on_morphism_op.
    rewrite assoc.
    rewrite nat_trans_ax.
    eapply pathscomp0.
    { do 2 rewrite <- assoc. apply maponpaths. rewrite assoc. apply Hyp. }
    do 2 apply maponpaths.
    repeat rewrite <- assoc.
    do 2 apply maponpaths.
    apply pathsinv0.
    apply nat_trans_ax.
  Qed.

  Definition drelrefcont_functor_data: functor_data ([C, D, hsD] ⊠ [C, E, hs])^op HSET.
  Proof.
    use make_functor_data.
    - intro ZX. apply (drelrefcont hs J (pr1 ZX) (pr2 ZX) T).
    - intros ZX ZX' πα mbind. induction ZX as [Z X]. induction ZX' as [Z' X']. induction πα as [π α]. cbn in π, α.
      exists (drelrefcont_functor_on_morphism_op π α (pr1 mbind)).
      apply drelrefcont_functor_on_morphism_op_ok.
      exact (pr2 mbind).
  Defined.

  Lemma is_functor_drelrefcont_functor_data: is_functor drelrefcont_functor_data.
  Proof.
    split.
    - intro ZX. induction ZX as [Z X].
      apply funextfun. intro mbind.
      (* show_id_type. *)
      apply (drelrefcont_type_eq hs).
      intros c1 c2 f.
      cbn.
      unfold drelrefcont_functor_on_morphism_op.
      rewrite id_right.
      apply id_left.
    - intros ZX ZX' ZX'' πα πα'.
      apply funextfun. intro mbind.
      apply (drelrefcont_type_eq hs).
      intros c1 c2 f.
      cbn.
      unfold drelrefcont_functor_on_morphism_op.
      rewrite assoc.
      do 2 apply maponpaths.
      rewrite <- assoc.
      apply idpath.
  Qed.

  Definition drelrefcont_functor: functor ([C, D, hsD] ⊠ [C, E, hs])^op HSET.
  Proof.
    use make_functor.
    - exact drelrefcont_functor_data.
    - exact is_functor_drelrefcont_functor_data.
  Defined.

End drelrefcont_dependent_on_Z_and_X.
