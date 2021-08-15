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

Require Import UniMath.SubstitutionSystems.Relativization.Protomonads.

Local Open Scope cat.

Section drelrefcont_def.

  Context {C D E : precategory}.
  Context (hs : has_homsets E).
  Context (J Z : functor C D).
  Context (X T : functor C E).

  Definition drelrefcont_op : UU := ∏ (C1 C2: C), D⟦J C1, Z C2⟧ -> E⟦X C1, T C2⟧.
  Definition drelrefcont_natural (mbind: drelrefcont_op) : UU :=
    forall (C1 C1' C2 C2': C) (h1: C1' --> C1) (h2: C2 --> C2') (f: J C1 --> Z C2),
      #X h1 · (mbind C1 C2 f) · #T h2 = mbind C1' C2' (#J h1 · f · #Z h2).

  Lemma isaprop_drelrefcont_natural (mbind: drelrefcont_op): isaprop (drelrefcont_natural mbind).
  Proof.
    repeat (apply impred; intros).
    apply hs.
  Qed.

  Definition drelrefcont_type : UU := ∑ (mbind: drelrefcont_op), drelrefcont_natural mbind.

  Lemma drelrefcont_type_eq (mbind mbind': drelrefcont_type): (forall (C1 C2: C) (f: J C1 --> Z C2), pr1 mbind C1 C2 f = pr1 mbind' C1 C2 f) -> mbind = mbind'.
  Proof.
    intro Hyp.
    assert (Hyp' : pr1 mbind = pr1 mbind').
    { apply funextsec; intro C1. apply funextsec; intro C2. apply funextsec; intro f.
      apply Hyp.
    }
    apply (total2_paths_f Hyp'), proofirrelevance, isaprop_drelrefcont_natural.
  Qed.

  Lemma isaset_drelrefcont_type: isaset drelrefcont_type.
  Proof.
    apply (isofhleveltotal2 2).
    - apply impred; intro C1. apply impred; intro C2. apply impred; intro f. apply hs.
    - intro mbind. apply isasetaprop, isaprop_drelrefcont_natural.
  Qed.

  Definition drelrefcont: hSet := drelrefcont_type ,, isaset_drelrefcont_type.

End drelrefcont_def.

Arguments drelrefcont_natural {_ _ _ _ _ _ _} _.

Section drelrefcont_dependent_on_X.

  Context {C D E : precategory}.
  Context (hs : has_homsets E).
  Context (J Z : functor C D).
  Context (T : functor C E).

  Definition drelrefcont_left_functor_on_morphism_op {X X': functor C E} (α: X' ⟹ X) (mbind: drelrefcont_op J Z X T): drelrefcont_op J Z X' T.
  Proof.
    intros C1 C2 f.
    exact (α C1 · mbind C1 C2 f).
  Defined.

  Lemma drelrefcont_left_functor_on_morphism_op_ok (X X': functor C E) (α: X' ⟹ X) (mbind: drelrefcont_op J Z X T):
    drelrefcont_natural mbind -> drelrefcont_natural (drelrefcont_left_functor_on_morphism_op α mbind).
  Proof.
    intro Hyp.
    intros C1 C1' C2 C2' h1 h2 f.
    unfold drelrefcont_left_functor_on_morphism_op.
    rewrite assoc.
    rewrite nat_trans_ax.
    eapply pathscomp0.
    { do 2 rewrite <- assoc. apply maponpaths. rewrite assoc. apply Hyp. }
    apply idpath.
  Qed.

  Definition drelrefcont_left_functor_data: functor_data [C, E, hs]^op HSET.
  Proof.
    use make_functor_data.
    - intro X. apply (drelrefcont hs J Z X T).
    - intros X X' α mbind. cbn in α.
      exists (drelrefcont_left_functor_on_morphism_op α (pr1 mbind)).
      apply drelrefcont_left_functor_on_morphism_op_ok.
      exact (pr2 mbind).
  Defined.

  Lemma is_functor_drelrefcont_left_functor_data: is_functor drelrefcont_left_functor_data.
  Proof.
    split.
    - intro X.
      apply funextfun. intro mbind.
      (* show_id_type. *)
      apply (drelrefcont_type_eq hs).
      intros C1 C2 f.
      cbn.
      unfold drelrefcont_left_functor_on_morphism_op.
      apply id_left.
    - intros X X' X'' α α'.
      apply funextfun. intro mbind.
      apply (drelrefcont_type_eq hs).
      intros C1 C2 f.
      cbn.
      unfold drelrefcont_left_functor_on_morphism_op.
      rewrite assoc.
      apply idpath.
  Qed.

  Definition drelrefcont_left_functor: functor [C, E, hs]^op HSET.
  Proof.
    use make_functor.
    - exact drelrefcont_left_functor_data.
    - exact is_functor_drelrefcont_left_functor_data.
  Defined.

End drelrefcont_dependent_on_X.
