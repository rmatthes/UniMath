(** **********************************************************

Contents:

- Construction of a gbind operation from an initial algebra

This file is inspired from LiftingInitial_alt.v (we continue to use omega cocontinuity instead of
Kan extensions) and takes some code from there.

Written by: Ralph Matthes 2021

************************************************************)

Set Kernel Term Sharing.

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.Relativization.Protomonads.
Require Import UniMath.SubstitutionSystems.Relativization.DoublyRelativizedRefinedContainment.
Require Import UniMath.SubstitutionSystems.Relativization.LiftingRelativizedContainment.


Local Open Scope subsys.

Local Open Scope cat.

Local Coercion alg_carrier : algebra_ob >-> ob.

Section construction.

  Context (C D : precategory) (hs : has_homsets D) (J: functor C D) (CP : BinCoproducts D).

  Context (ID : Initial D) (CC : Colims_of_shape nat_graph D).
  Context (H : functor [C, D, hs] [C, D, hs]) (HH : is_omega_cocont H).

Let hsCD : has_homsets [C, D, hs] := functor_category_has_homsets C D hs.
Let CPCD : BinCoproducts [C, D, hs] := BinCoproducts_functor_precat _ _ CP hs.
Let EndCD := [[C, D, hs], [C, D, hs], hsCD].
Let CPEndCD:= BinCoproducts_functor_precat _ _ CPCD hsCD: BinCoproducts EndCD.

Definition Const_plus_H (X : functor C D) : functor [C, D, hs] [C, D, hs]
  := BinCoproduct_of_functors _ _ CPCD (constant_functor [C, D, hs] [C, D, hs] X) H.

Definition J_H : functor [C, D, hs] [C, D, hs]
 := Const_plus_H J.

Let Alg : precategory := FunctorAlg J_H hsCD.

Let InitialCD : Initial [C, D, hs].
Proof.
  apply Initial_functor_precat, ID.
Defined.

Let Colims_of_shape_nat_graph_CD : Colims_of_shape nat_graph [C, D, hs].
Proof.
  apply ColimsFunctorCategory_of_shape, CC.
Defined.

Lemma is_omega_cocont_J_H : is_omega_cocont J_H.
Proof.
  apply is_omega_cocont_BinCoproduct_of_functors; try apply functor_category_has_homsets.
  - apply is_omega_cocont_constant_functor, functor_category_has_homsets.
  - apply HH.
Defined.

Definition InitAlg : Alg :=
  InitialObject (colimAlgInitial hsCD InitialCD is_omega_cocont_J_H (Colims_of_shape_nat_graph_CD _)).


Section construction_for_unknown_protomonad.

  Context (Ze : precategory_Ptm hs J).
  Context (lift : lifting_of_relativized_containment hs hs Ze H).


Definition SpecializedRelativizedGMIt_stepterm_type (T : functor C D) (G : functor [C, D, hs] [C, D, hs]): UU :=
  drelrefcont_left_functor hs J (pr1 Ze) T ⟹
       functor_composite (functor_opp J_H) (drelrefcont_left_functor hs J (pr1 Ze) (G T)).

Definition SpecializedRelativizedGMIt_type (T : functor C D)
  (G : functor [C, D, hs] [C, D, hs]) (ρ : [C, D, hs] ⟦ G T, T ⟧)
  (ϕ : SpecializedRelativizedGMIt_stepterm_type T G) : UU :=
  ∃! gbind : drelrefcont_type J (pr1 Ze) (alg_carrier _ InitAlg) T, forall (c1 c2: C) (f: J c1 --> pr1 Ze c2),
      pr1(alg_map J_H InitAlg) c1 · (pr1 gbind c1 c2 f) = pr1 (pr1 ϕ (alg_carrier _ InitAlg) gbind) c1 c2 f · pr1 ρ c2.

(* A J_H algebra is a protomonad *)

Definition eta_from_alg (T : algebra_ob J_H) : [C, D, hs] ⟦ J,  `T ⟧.
Proof.
  exact (BinCoproductIn1 _ (CPCD _ _) · alg_map _ T).
Defined.

Local Notation η := eta_from_alg.

Definition ptm_from_alg (T : algebra_ob J_H) : precategory_Ptm hs J.
Proof.
  exists (pr1 T).
  exact (η T).
Defined.


Definition tau_from_alg (T : algebra_ob J_H) : [C, D, hs] ⟦H `T, `T⟧.
Proof.
  exact (BinCoproductIn2 _ (CPCD _ _) · alg_map _ T).
Defined.

Local Notation τ := tau_from_alg.

Context (k : Ze --> ptm_from_alg InitAlg).

Local Definition G : functor [C, D, hs] [C, D, hs]
  := Const_plus_H (pr1 Ze).

Local Definition ρ : [C, D, hs] ⟦ G `InitAlg, `InitAlg ⟧ :=
  @BinCoproductArrow [C, D, hs] _ _ (CPCD (pr1 Ze) (H `InitAlg)) _  (pr1 k) (τ InitAlg).

Local Definition ϕ_op_op (X: C ⟶ D) (mbind : pr1 (drelrefcont_left_functor hs J (pr1 Ze) `InitAlg X)):
   drelrefcont_op J (pr1 Ze) (functor_opp J_H X) (G `InitAlg).
Proof.
  intros c1 c2 f.
  (* unfold J_H, functor_opp. cbn. unfold BinCoproduct_of_functors_ob. *)
  exact (@BinCoproductOfArrows D _ _ (CP _ _) _ _ (CP _ _) f (pr1 (lift `InitAlg X mbind) c1 c2 f)).
Defined.

Local Lemma ϕ_op_ok (X: C ⟶ D) (mbind : pr1 (drelrefcont_left_functor hs J (pr1 Ze) `InitAlg X)):
  drelrefcont_natural (ϕ_op_op X mbind).
Proof.
  intros c1 c1' c2 c2' h1 h2 f.
  unfold functor_opp, J_H.
  eapply pathscomp0.
  { cbn. unfold BinCoproduct_of_functors_mor. apply cancel_postcomposition.
    apply BinCoproductOfArrows_comp.
  }
  eapply pathscomp0.
  { apply BinCoproductOfArrows_comp. }
  cbn.
  unfold ϕ_op_op.
  apply maponpaths.
  apply (pr2 (lift `InitAlg X mbind)).
Qed.

Local Definition ϕ_op: nat_trans_data (drelrefcont_left_functor hs J (pr1 Ze) `InitAlg)
                                      (functor_opp J_H ∙ drelrefcont_left_functor hs J (pr1 Ze) (G `InitAlg)).
Proof.
  intro X. cbn in X.
  intro mbind.
  use tpair.
  - exact (ϕ_op_op X mbind).
  - exact (ϕ_op_ok X mbind).
Defined.

Local Lemma ϕ_op_is_nat_trans: is_nat_trans _ _ ϕ_op.
Proof.
  intros X X' α.
  apply funextfun; intro mbind.
  apply (drelrefcont_type_eq hs); intros c1 c2 f.
  eapply pathscomp0.
  2: { cbn.
       unfold ϕ_op_op.
       unfold drelrefcont_left_functor_on_morphism_op.
       apply cancel_postcomposition.
       cbn. unfold coproduct_nat_trans_data.
       change (nat_trans_id (pr1 J)) with (identity(C:=[C,D,hs]) J).
       (* show_id_type. *)
       set (RHS := BinCoproductOfArrows D (CP (J c1) (pr1(H X') c1)) (CP (J c1) (pr1(H X) c1)) (identity (J c1)) (pr1(# H α) c1)).
       match goal with |- @paths _ _ ?ID => change ID with RHS end.
       apply idpath.
  }
  eapply pathscomp0.
  2: { apply pathsinv0. apply BinCoproductOfArrows_comp. }
  eapply pathscomp0.
  { cbn. unfold drelrefcont_left_functor_on_morphism_op, ϕ_op_op. apply idpath. }
  rewrite id_left.
  apply maponpaths.
  set (LHS := pr1 (lift `InitAlg X' (#(drelrefcont_left_functor hs J (pr1 Ze) `InitAlg) α mbind)) c1 c2 f).
  match goal with |- @paths _ ?ID _ => change ID with LHS end.
  apply pointwise_naturality_of_lifting.
Qed.

Local Definition ϕ: SpecializedRelativizedGMIt_stepterm_type `InitAlg G := ϕ_op ,, ϕ_op_is_nat_trans.

Context (SRGMIt: SpecializedRelativizedGMIt_type `InitAlg G ρ ϕ).
(** of course, this should be constructed somewhere *)

(* now exploit this operation *)
Definition gbindWithLaw: drelrefcont_type J (pr1 Ze) `InitAlg `InitAlg := pr1 (pr1 SRGMIt).

Definition gbind: drelrefcont_op J (pr1 Ze) `InitAlg `InitAlg := pr1 gbindWithLaw.
Definition gbind_natural:
  forall (c1 c1' c2 c2': C) (h1: c1' --> c1) (h2: c2 --> c2') (f: J c1 --> pr1 Ze c2),
    #(pr1 `InitAlg) h1 · (gbind c1 c2 f) · #(pr1 `InitAlg) h2 =
    gbind c1' c2' (#J h1 · f · #(pr1 Ze) h2) :=
  pr2 gbindWithLaw.

Lemma gbind_laws (c1 c2: C) (f: J c1 --> pr1 Ze c2):
  pr1(alg_map J_H InitAlg) c1 · gbind c1 c2 f =
  BinCoproductArrow D (CP (J c1) (pr1(H `InitAlg) c1)) (f · pr1 k c2)
                    (pr1(lift `InitAlg `InitAlg gbindWithLaw) c1 c2 f · pr1(τ InitAlg) c2).
Proof.
  eapply pathscomp0.
  apply (pr2 (pr1 SRGMIt)).
  unfold ϕ. unfold ϕ_op. cbn. unfold ϕ_op_op. cbn. unfold coproduct_nat_trans_data.
  apply precompWithBinCoproductArrow.
Qed.

Corollary gbind_law1 (c1 c2: C) (f: J c1 --> pr1 Ze c2):
  pr1(η InitAlg) c1 · gbind c1 c2 f = f · pr1 k c2.
Proof.
  unfold eta_from_alg.
  cbn.
  rewrite <- assoc.
  eapply pathscomp0.
  { apply maponpaths.
    apply gbind_laws.
  }
  apply BinCoproductIn1Commutes.
Qed.

Corollary gbind_law2 (c1 c2: C) (f: J c1 --> pr1 Ze c2):
  pr1(τ InitAlg) c1 · gbind c1 c2 f = pr1(lift `InitAlg `InitAlg gbindWithLaw) c1 c2 f · pr1(τ InitAlg) c2.
Proof.
  unfold tau_from_alg.
  cbn.
  rewrite <- assoc.
  eapply pathscomp0.
  { apply maponpaths.
    apply gbind_laws.
  }
  apply BinCoproductIn2Commutes.
Qed.

End construction_for_unknown_protomonad.

Section instantiation_for_term_protomonad.

  Local Definition Ze : precategory_Ptm hs J := ptm_from_alg InitAlg.

  Context (lifti: lifting_of_relativized_containment hs hs Ze H).
  (** assume it just for this specific [Ze], but would normally be constructed uniformly in [Ze] *)

  Local Definition k : Ze --> ptm_from_alg InitAlg := identity Ze.

  Context (SRGMIti: SpecializedRelativizedGMIt_type Ze `InitAlg (G Ze) (ρ Ze k) (ϕ Ze lifti)).

  Definition gbindiWithLaw: drelrefcont_type  J `InitAlg `InitAlg `InitAlg := gbindWithLaw Ze lifti k SRGMIti.
  Definition gbindi: drelrefcont_op J `InitAlg `InitAlg `InitAlg := gbind Ze lifti k SRGMIti.

  Definition gbindi_natural: forall (c1 c1' c2 c2': C) (h1: c1' --> c1) (h2: c2 --> c2') (f: J c1 --> pr1 `InitAlg c2),
      #(pr1 `InitAlg) h1 · (gbindi c1 c2 f) · #(pr1 `InitAlg) h2 = gbindi c1' c2' (#J h1 · f · #(pr1 `InitAlg) h2)
    := gbind_natural Ze lifti k SRGMIti.

  Lemma gbindi_law1 (c1 c2: C) (f: J c1 --> pr1 `InitAlg c2):
    pr1(eta_from_alg InitAlg) c1 · gbindi c1 c2 f = f.
  Proof.
    eapply pathscomp0.
    { apply gbind_law1. }
    apply id_right.
  Qed.

  Lemma gbindi_law2 (c1 c2: C) (f: J c1 --> pr1 `InitAlg c2):
    pr1(tau_from_alg InitAlg) c1 · gbindi c1 c2 f = pr1(lifti `InitAlg `InitAlg gbindiWithLaw) c1 c2 f · pr1(tau_from_alg InitAlg) c2.
    apply gbind_law2.
  Qed.

  Lemma gbindi_law3 (c: C): gbindi c c (pr1(eta_from_alg InitAlg) c) = identity (pr1 `InitAlg c).
  Proof.
  Abort.

End instantiation_for_term_protomonad.

End construction.
