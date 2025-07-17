(** * Near-univalence of [type_precat] *)

(** The precategory of types is not quite univalent - it doesn't have
    hom-sets. However, it is the case that [idtoiso] is a weak equivalence.

    Much of this material is copied near-verbatim from the results for
    sets. *)

Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Categories.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Functors.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Isos.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Univalence.

Require Import UniMath.Induction.M.CategoryTheory_legacy.categories.Type.Core.
Require Import UniMath.Induction.M.CategoryTheory_legacy.categories.Type.MonoEpiIso.

Local Open Scope cat.

Definition univalenceweq (X X' : UU) : (X = X') ≃ (X ≃ X') :=
   tpair _ _ (univalenceAxiom X X').

Definition type_id_weq_iso (A B : ob type_precat) :
  (A = B) ≃ (iso A B) :=
  weqcomp (univalence _ _) (type_equiv_weq_iso A B).

Lemma type_id_weq_iso_is (A B : ob type_precat):
    @idtoiso _ A B = pr1 (type_id_weq_iso A B).
Proof.
  apply funextfun.
  intro p; elim p.
  apply eq_iso; simpl.
  - apply funextfun; intro.
    apply idpath.
Defined.

Lemma type_is_weq_idtoiso (A B : ob type_precat):
   isweq (@idtoiso _ A B).
Proof.
  rewrite type_id_weq_iso_is.
  apply (pr2 (type_id_weq_iso A B)).
Defined.