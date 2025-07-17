(** * The displayed category of types of a given h-level *)

(** ** Contents

  - Definitions
    - [disp_hlevel]: The displayed category of types of [hlevel] n
    - [disp_prop]: The displayed category of propositions
    - [disp_HSET]: The displayed category of sets
  - Equivalence of the total category of [disp_HSET] with [HSET_univalent_category]
 *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Categories.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Isos.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.NaturalTransformations.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Univalence.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Functors.

Require Import UniMath.Induction.M.CategoryTheory_legacy.categories.Type.Core.
Require Import UniMath.Induction.M.CategoryTheory_legacy.categories.HSET.Core.
Require Import UniMath.Induction.M.CategoryTheory_legacy.categories.HSET.Univalence.

Require Import UniMath.Induction.M.CategoryTheory_legacy.catiso.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Adjunctions.Core.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Equivalences.Core.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Equivalences.FullyFaithful.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Equivalences.CompositesAndInverses.

Require Import UniMath.Induction.M.CategoryTheory_legacy.DisplayedCats.Core.
Require Import UniMath.Induction.M.CategoryTheory_legacy.DisplayedCats.Constructions.

(** ** Definitions *)

(** *** [disp_hlevel]: The displayed category of types of [hlevel] n *)

Definition disp_hlevel (n : nat) : disp_precat type_precat :=
  disp_full_sub type_precat (isofhlevel n).

(** *** [disp_prop]: The displayed category of propositions *)

Definition disp_prop : disp_precat type_precat := disp_hlevel 1.

(** *** [disp_HSET]: The displayed category of sets *)

Definition disp_HSET : disp_precat type_precat := disp_hlevel 2.

(** ** Equivalence of the total category of [disp_HSET] with [HSET_univalent_category] *)

Definition disp_HSET_equiv_HSET_adjunction_data :
  adjunction_data (total_precategory disp_HSET) HSET_univalent_category.
Proof.
  use tpair; [|use tpair].
  - use make_functor.
    + use make_functor_data.
      * exact (idfun _).
      * intros ? ? f; exact (pr1 f).
    + split.
      * intro; reflexivity.
      * intros ? ? ?; reflexivity.
  - use make_functor.
    + use make_functor_data.
      * exact (idfun _).
      * intros ? ? f; exact (f,, tt).
    + split.
      * intro; reflexivity.
      * intros ? ? ?; reflexivity.
  - split.
    + use make_nat_trans.
      * intros x.
        use tpair.
        -- exact (idfun _).
        -- exact tt.
      * (** [is_nat_trans] *)
        intros ? ? ?.
        apply subtypePath.
        -- intro. apply isapropunit.
        -- unfold funcomp; apply funextfun; intro; reflexivity.
    + use make_nat_trans.
      * intros ?; exact (idfun _).
      * intros ? ? ?; apply funextfun; intro; reflexivity.
Defined.

(** The displayed category of sets over [type_precat] is equivalent to the
    direct definition of [HSET] as a category. *)
Lemma disp_HSET_equiv_HSET :
  forms_equivalence disp_HSET_equiv_HSET_adjunction_data.
Proof.
  split.
  - intros ?; apply identity_is_iso.
  - intros ?; apply identity_is_iso.
Qed.

Lemma disp_HSET_adj_equivalence_of_precats_left :
  adj_equivalence_of_precats (left_functor disp_HSET_equiv_HSET_adjunction_data).
Proof.
  use make_adj_equivalence_of_precats.
  - exact (right_functor disp_HSET_equiv_HSET_adjunction_data).
  - exact (adjunit disp_HSET_equiv_HSET_adjunction_data).
  - exact (adjcounit disp_HSET_equiv_HSET_adjunction_data).
  - use make_form_adjunction.
    + intro; reflexivity.
    + intro; reflexivity.
  - apply disp_HSET_equiv_HSET.
Defined.

Local Definition isaset' (X : UU) : hProp := (isaset X,, isapropisaset _).

Lemma has_homsets_disp_HSET : has_homsets (total_precategory disp_HSET).
Proof.
  intros ? ?.
  apply (equivalence_homtype_property (right_functor disp_HSET_equiv_HSET_adjunction_data) (adj_equivalence_of_precats_inv disp_HSET_adj_equivalence_of_precats_left) isaset' has_homsets_HSET).
Qed.
