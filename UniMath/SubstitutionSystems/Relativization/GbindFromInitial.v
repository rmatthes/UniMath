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
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
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

Context (lift : lifting_of_relativized_containment hs J hs H).

Section construction_for_unknown_protomonad.

  Context (Ze : precategory_Ptm hs J).

  Local Definition drelrefcont_functor_with_fixed_protomonad (T : functor C D) := functor_fix_fst_arg _ _ _ (drelrefcont_functor hs J hs T) (pr1 Ze).

Definition RelativizedGMIt_stepterm_type (T : functor C D): UU :=
  drelrefcont_functor_with_fixed_protomonad T ⟹
  functor_composite (functor_opp J_H) (drelrefcont_functor_with_fixed_protomonad T).

Definition RelativizedGMIt_property {T : functor C D} (ϕ : RelativizedGMIt_stepterm_type T)
  (gbind: drelrefcont_type J (pr1 Ze) `InitAlg T) {c1 c2: C} (f: J c1 --> pr1 Ze c2) : UU :=
  pr1(alg_map J_H InitAlg) c1 · (pr1 gbind c1 c2 f) = pr1 (pr1 ϕ `InitAlg gbind) c1 c2 f.

Definition RelativizedGMIt_type (T : functor C D)
  (ϕ : RelativizedGMIt_stepterm_type T) : UU :=
  ∃! gbind : drelrefcont_type J (pr1 Ze) `InitAlg T,
             forall (c1 c2: C) (f: J c1 --> pr1 Ze c2), RelativizedGMIt_property ϕ gbind f.

Definition SpecializedRelativizedGMIt_stepterm_type (T : functor C D) (G : functor [C, D, hs] [C, D, hs]): UU :=
  drelrefcont_functor_with_fixed_protomonad T ⟹
  functor_composite (functor_opp J_H) (drelrefcont_functor_with_fixed_protomonad (G T)).

Definition SpecializedRelativizedGMIt_property {T : functor C D} {G : functor [C, D, hs] [C, D, hs]} (ρ : [C, D, hs] ⟦ G T, T ⟧)
  (ϕ : SpecializedRelativizedGMIt_stepterm_type T G)
  (gbind: drelrefcont_type J (pr1 Ze) `InitAlg T) {c1 c2: C} (f: J c1 --> pr1 Ze c2) : UU :=
  pr1(alg_map J_H InitAlg) c1 · (pr1 gbind c1 c2 f) = pr1 (pr1 ϕ `InitAlg gbind) c1 c2 f · pr1 ρ c2.

Definition SpecializedRelativizedGMIt_type (T : functor C D)
  (G : functor [C, D, hs] [C, D, hs]) (ρ : [C, D, hs] ⟦ G T, T ⟧)
  (ϕ : SpecializedRelativizedGMIt_stepterm_type T G) : UU :=
  ∃! gbind : drelrefcont_type J (pr1 Ze) `InitAlg T,
             forall (c1 c2: C) (f: J c1 --> pr1 Ze c2), SpecializedRelativizedGMIt_property ρ ϕ gbind f.

Section Specialization.

  Context {T : functor C D} {G : functor [C, D, hs] [C, D, hs]} (ρ : [C, D, hs] ⟦ G T, T ⟧)
          (ϕ : SpecializedRelativizedGMIt_stepterm_type T G).

  Definition generalϕ_op_op {X : [C, D, hs]^op} (mbind : drelrefcont_type J (pr1 Ze) X T):
    drelrefcont_op J (pr1 Ze) (functor_opp J_H X) T.
  Proof.
    intros c1 c2 f.
    exact (pr1(pr1 ϕ X mbind) c1 c2 f · pr1 ρ c2).
  Defined.

  Lemma generalϕ_op_ok {X : [C, D, hs]^op} (mbind : drelrefcont_type J (pr1 Ze) X T):
    drelrefcont_natural (generalϕ_op_op mbind).
  Proof.
    intros c1 c1' c2 c2' h1 h2 f.
    unfold generalϕ_op_op. cbn.
    eapply pathscomp0.
    2: { apply cancel_postcomposition.
         apply (pr2 (pr1 ϕ X mbind)).
    }
    repeat rewrite <- assoc.
    do 2 apply maponpaths.
    apply pathsinv0.
    apply nat_trans_ax.
  Qed.

  Definition generalϕ_op: nat_trans_data (drelrefcont_functor_with_fixed_protomonad T)
                                         (functor_opp J_H ∙ drelrefcont_functor_with_fixed_protomonad T).
  Proof.
    intros X mbind.
    use tpair.
    - exact (generalϕ_op_op mbind).
    - exact (generalϕ_op_ok mbind).
  Defined.

  Lemma generalϕ_op_is_nat_trans: is_nat_trans _ _ generalϕ_op.
  Proof.
    intros X X' α.
    apply funextfun; intro mbind.
    apply (drelrefcont_type_eq hs); intros c1 c2 f.
    cbn.
    unfold generalϕ_op_op.
    cbn.
    assert (aux := pr2 ϕ).
    assert (auxinst := aux X X' α).
    apply toforallpaths in auxinst.
    assert (auxinst1 := maponpaths pr1 (auxinst mbind)).
    apply toforallpaths in auxinst1.
    assert (auxinst2 := auxinst1 c1).
    apply toforallpaths in auxinst2.
    assert (auxinst3 := auxinst2 c2).
    apply toforallpaths in auxinst3.
    assert (auxinst4 := auxinst3 f).
    clear aux auxinst auxinst1 auxinst2 auxinst3.
    cbn in auxinst4.
    eapply pathscomp0.
    { apply cancel_postcomposition.
      exact auxinst4. }
    clear auxinst4.
    unfold drelrefcont_functor_on_morphism_op.
    rewrite <- assoc.
    apply idpath.
  Qed.

  Definition generalϕ : RelativizedGMIt_stepterm_type T := generalϕ_op ,, generalϕ_op_is_nat_trans.

  Lemma property_for_generalϕ_is_the_specialized_property
        (gbind: drelrefcont_type J (pr1 Ze) `InitAlg T) {c1 c2: C} (f: J c1 --> pr1 Ze c2) :
    RelativizedGMIt_property generalϕ gbind f = SpecializedRelativizedGMIt_property ρ ϕ gbind f.
  Proof.
    apply idpath.
  Qed.

End Specialization.

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

Local Definition ϕ_op_op (X: C ⟶ D) (mbind : pr1 (drelrefcont_functor hs J hs `InitAlg (pr1 Ze,,X))):
   drelrefcont_op J (pr1 Ze) (functor_opp J_H X) (G `InitAlg).
Proof.
  intros c1 c2 f.
  (* unfold J_H, functor_opp. cbn. unfold BinCoproduct_of_functors_ob. *)
  exact (@BinCoproductOfArrows D _ _ (CP _ _) _ _ (CP _ _) f (pr1 (lift `InitAlg (Ze,,X) mbind) c1 c2 f)).
Defined.

Local Lemma ϕ_op_ok (X: C ⟶ D) (mbind : pr1 (drelrefcont_functor hs J hs `InitAlg (pr1 Ze,,X))):
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
  apply (pr2 (lift `InitAlg (Ze,,X) mbind)).
Qed.

Local Definition ϕ_op: nat_trans_data (drelrefcont_functor_with_fixed_protomonad `InitAlg)
                                      (functor_opp J_H ∙ drelrefcont_functor_with_fixed_protomonad (G `InitAlg)).
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
       unfold drelrefcont_functor_with_fixed_protomonad, drelrefcont_functor_on_morphism_op.
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
  { cbn. unfold drelrefcont_functor_with_fixed_protomonad, drelrefcont_functor_on_morphism_op, ϕ_op_op. apply idpath. }
  rewrite id_left. rewrite id_right.
  apply maponpaths.
  set (LHS := pr1 (lift `InitAlg (Ze,,X') (#(drelrefcont_functor_with_fixed_protomonad `InitAlg) α mbind)) c1 c2 f).
  match goal with |- @paths _ ?ID _ => change ID with LHS end.
  unfold drelrefcont_functor_with_fixed_protomonad in LHS. simpl in LHS. unfold functor_fix_fst_arg_mor in LHS.
  eapply pathscomp0.
  { assert (aux := pointwise_naturality_of_lifting hs J hs H lift `InitAlg (identity Ze) α mbind c1 c2 f).
    apply aux.
  }
  unfold drelrefcont_functor_on_morphism_op.
  rewrite id_right.
  apply idpath.
Qed.

Local Definition ϕ: SpecializedRelativizedGMIt_stepterm_type `InitAlg G := ϕ_op ,, ϕ_op_is_nat_trans.

Context (SRGMIt: SpecializedRelativizedGMIt_type `InitAlg G ρ ϕ).
(** of course, this should be constructed somewhere *)

(* now exploit this operation *)
Definition gbindWithLaw_type: UU := drelrefcont_type J (pr1 Ze) `InitAlg `InitAlg.
Definition gbindWithLaw: gbindWithLaw_type := pr1 (pr1 SRGMIt).

Definition gbind: drelrefcont_op J (pr1 Ze) `InitAlg `InitAlg := pr1 gbindWithLaw.
Definition gbind_natural:
  forall (c1 c1' c2 c2': C) (h1: c1' --> c1) (h2: c2 --> c2') (f: J c1 --> pr1 Ze c2),
    #(pr1 `InitAlg) h1 · (gbind c1 c2 f) · #(pr1 `InitAlg) h2 =
    gbind c1' c2' (#J h1 · f · #(pr1 Ze) h2) :=
  pr2 gbindWithLaw.

Definition gbind_property (gbwl: gbindWithLaw_type) {c1 c2: C} (f: J c1 --> pr1 Ze c2): UU :=
  SpecializedRelativizedGMIt_property ρ ϕ gbwl f.

Definition gbind_property_nicer (gbwl: gbindWithLaw_type) {c1 c2: C} (f: J c1 --> pr1 Ze c2): UU :=
  pr1(alg_map J_H InitAlg) c1 · pr1 gbwl c1 c2 f =
  BinCoproductArrow D (CP (J c1) (pr1(H `InitAlg) c1)) (f · pr1 k c2)
                    (pr1(lift `InitAlg (Ze,,`InitAlg) gbwl) c1 c2 f · pr1(τ InitAlg) c2).

Lemma gbind_property_impl_gbind_property_nicer (gbwl: gbindWithLaw_type)
      {c1 c2: C} (f: J c1 --> pr1 Ze c2): gbind_property gbwl f -> gbind_property_nicer gbwl f.
Proof.
  intro Hyp. red. do 2 red in Hyp.
  unfold ϕ, ϕ_op in Hyp. cbn in Hyp. unfold ϕ_op_op in Hyp. cbn in Hyp. unfold coproduct_nat_trans_data in Hyp.
  eapply pathscomp0.
  exact Hyp.
  apply precompWithBinCoproductArrow.
Qed.

Lemma gbind_property_nicer_impl_gbind_property (gbwl: gbindWithLaw_type)
      {c1 c2: C} (f: J c1 --> pr1 Ze c2): gbind_property_nicer gbwl f -> gbind_property gbwl f.
Proof.
  intro Hyp. red in Hyp. do 2 red.
  unfold ϕ, ϕ_op. cbn. unfold ϕ_op_op. cbn. unfold coproduct_nat_trans_data.
  eapply pathscomp0.
  exact Hyp.
  apply pathsinv0.
  apply precompWithBinCoproductArrow.
Qed.


Definition gbind_property_parts (gbwl: gbindWithLaw_type) {c1 c2: C} (f: J c1 --> pr1 Ze c2): UU :=
  pr1(η InitAlg) c1 · pr1 gbwl c1 c2 f = f · pr1 k c2 ×
  pr1(τ InitAlg) c1 · pr1 gbwl c1 c2 f = pr1(lift `InitAlg (Ze,,`InitAlg) gbwl) c1 c2 f · pr1(τ InitAlg) c2.

Lemma gbind_property_nicer_impl_gbind_property_parts (gbwl: gbindWithLaw_type)
      {c1 c2: C} (f: J c1 --> pr1 Ze c2): gbind_property_nicer gbwl f -> gbind_property_parts gbwl f.
Proof.
  intro Hyp. red in Hyp. red. split.
  - unfold eta_from_alg.
    cbn.
    rewrite <- assoc.
    eapply pathscomp0.
    { apply maponpaths.
      apply Hyp.
    }
    apply BinCoproductIn1Commutes.
  - unfold tau_from_alg.
    cbn.
    rewrite <- assoc.
    eapply pathscomp0.
    { apply maponpaths.
      apply Hyp.
    }
    apply BinCoproductIn2Commutes.
Qed.

Lemma gbind_property_parts_impl_gbind_property_nicer (gbwl: gbindWithLaw_type)
      {c1 c2: C} (f: J c1 --> pr1 Ze c2): gbind_property_parts gbwl f -> gbind_property_nicer gbwl f.
Proof.
  intro Hyp. induction Hyp as [Hyp1 Hyp2].
  red.
  apply BinCoproductArrowUnique.
  - rewrite assoc. exact Hyp1.
  - rewrite assoc. exact Hyp2.
Qed.

Corollary gbind_laws (c1 c2: C) (f: J c1 --> pr1 Ze c2):
  pr1(alg_map J_H InitAlg) c1 · gbind c1 c2 f =
  BinCoproductArrow D (CP (J c1) (pr1(H `InitAlg) c1)) (f · pr1 k c2)
                    (pr1(lift `InitAlg (Ze,,`InitAlg) gbindWithLaw) c1 c2 f · pr1(τ InitAlg) c2).
Proof.
  apply gbind_property_impl_gbind_property_nicer.
  apply (pr2 (pr1 SRGMIt)).
Qed.

Corollary gbind_law1 (c1 c2: C) (f: J c1 --> pr1 Ze c2):
  pr1(η InitAlg) c1 · gbind c1 c2 f = f · pr1 k c2.
Proof.
  assert (aux := gbind_property_nicer_impl_gbind_property_parts gbindWithLaw f (gbind_laws c1 c2 f)).
  exact (pr1 aux).
Qed.

Corollary gbind_law2 (c1 c2: C) (f: J c1 --> pr1 Ze c2):
  pr1(τ InitAlg) c1 · gbind c1 c2 f = pr1(lift `InitAlg (Ze,,`InitAlg) gbindWithLaw) c1 c2 f · pr1(τ InitAlg) c2.
Proof.
  assert (aux := gbind_property_nicer_impl_gbind_property_parts gbindWithLaw f (gbind_laws c1 c2 f)).
  exact (pr2 aux).
Qed.

Lemma gbind_unique (gbwl: gbindWithLaw_type):
  (forall (c1 c2: C) (f: J c1 --> pr1 Ze c2), gbind_property_parts gbwl f) -> gbwl = gbindWithLaw.
Proof.
  intro Hyp.
  apply path_to_ctr.
  intros c1 c2 f.
  apply gbind_property_nicer_impl_gbind_property.
  apply gbind_property_parts_impl_gbind_property_nicer.
  apply Hyp.
Qed.


(* only a first experimentation:
Context (GlobalAss: forall (c: C), pr1 (lift `InitAlg (Ze,,`InitAlg) gbindWithLaw) c c (pr1 (pr2 Ze) c) = identity (pr1 (functor_opp H `InitAlg) c)).
Lemma gbind_law3 (c: C): gbind c c (pr1(pr2 Ze) c) = identity (pr1 `InitAlg c).
Proof.
  assert (Hvar: pr1(η InitAlg) c · gbind c c (pr1(pr2 Ze) c) = pr1(η InitAlg) c).
  { eapply pathscomp0. apply gbind_law1. apply (pr2 k). }
  assert (Hconstr: pr1(τ InitAlg) c · gbind c c (pr1(pr2 Ze) c) = pr1(τ InitAlg) c).
  { eapply pathscomp0. apply gbind_law2.
    rewrite GlobalAss. apply id_left. }
Abort.
*)

End construction_for_unknown_protomonad.


Section instantiation_for_trivial_protomonad.

  Local Definition Ze0 : precategory_Ptm hs J := J_Ptm hs J.

  Local Definition k0 : Ze0 --> ptm_from_alg InitAlg.
  Proof.
    use tpair.
    - exact (eta_from_alg InitAlg).
    - intro c. apply id_left.
  Defined.

  Context (SRGMIt0: SpecializedRelativizedGMIt_type Ze0 `InitAlg (G Ze0) (ρ Ze0 k0) (ϕ Ze0)).

  Definition gbind0WithLaw: gbindWithLaw_type Ze0 := gbindWithLaw Ze0 k0 SRGMIt0.
  Definition gbind0: drelrefcont_op J J `InitAlg `InitAlg := gbind Ze0 k0 SRGMIt0.

  Definition gbind0_natural: forall (c1 c1' c2 c2': C) (h1: c1' --> c1) (h2: c2 --> c2') (f: J c1 --> J c2),
      # (pr1 `InitAlg) h1 · (gbind0 c1 c2 f) · #(pr1 `InitAlg) h2 = gbind0 c1' c2' (#J h1 · f · #J h2)
    := gbind_natural Ze0 k0 SRGMIt0.

  Lemma gbind0_law1 (c1 c2: C) (f: J c1 --> J c2):
    pr1(eta_from_alg InitAlg) c1 · gbind0 c1 c2 f = f · pr1(eta_from_alg InitAlg) c2.
  Proof.
    apply gbind_law1.
  Qed.

  Lemma gbind0_law2 (c1 c2: C) (f: J c1 --> J c2):
    pr1(tau_from_alg InitAlg) c1 · gbind0 c1 c2 f = pr1(lift `InitAlg (Ze0,,`InitAlg) gbind0WithLaw) c1 c2 f · pr1(tau_from_alg InitAlg) c2.
    apply gbind_law2.
  Qed.

End instantiation_for_trivial_protomonad.

Section instantiation_for_term_protomonad.

  Local Definition Ze1 : precategory_Ptm hs J := ptm_from_alg InitAlg.

  Local Definition k1 : Ze1 --> ptm_from_alg InitAlg := identity Ze1.

  Context (SRGMIt1: SpecializedRelativizedGMIt_type Ze1 `InitAlg (G Ze1) (ρ Ze1 k1) (ϕ Ze1)).

  Definition gbind1WithLaw: gbindWithLaw_type Ze1 := gbindWithLaw Ze1 k1 SRGMIt1.
  Definition gbind1: drelrefcont_op J `InitAlg `InitAlg `InitAlg := gbind Ze1 k1 SRGMIt1.

  Definition gbind1_natural: forall (c1 c1' c2 c2': C) (h1: c1' --> c1) (h2: c2 --> c2') (f: J c1 --> pr1 `InitAlg c2),
      #(pr1 `InitAlg) h1 · (gbind1 c1 c2 f) · #(pr1 `InitAlg) h2 = gbind1 c1' c2' (#J h1 · f · #(pr1 `InitAlg) h2)
    := gbind_natural Ze1 k1 SRGMIt1.

  Lemma gbind1_law1 (c1 c2: C) (f: J c1 --> pr1 `InitAlg c2):
    pr1(eta_from_alg InitAlg) c1 · gbind1 c1 c2 f = f.
  Proof.
    eapply pathscomp0.
    { apply gbind_law1. }
    apply id_right.
  Qed.

  Lemma gbind1_law2 (c1 c2: C) (f: J c1 --> pr1 `InitAlg c2):
    pr1(tau_from_alg InitAlg) c1 · gbind1 c1 c2 f = pr1(lift `InitAlg (Ze1,,`InitAlg) gbind1WithLaw) c1 c2 f · pr1(tau_from_alg InitAlg) c2.
    apply gbind_law2.
  Qed.

  (* would be an instance of [gbind_law3]:
  Lemma gbind1_law3 (c: C): gbind1 c c (pr1(eta_from_alg InitAlg) c) = identity (pr1 `InitAlg c).
  Proof.
  Abort.
*)

End instantiation_for_term_protomonad.

Section different_protomonads.

  Context (Ze1 Ze2 : precategory_Ptm hs J).

  Context (T1 T2: functor C D).

  Definition stepterm_transformer_type: UU :=
    drelrefcont_functor_with_fixed_protomonad Ze1 T1 ⟹ drelrefcont_functor_with_fixed_protomonad Ze2 T2.

  Section fusion_law.

  Context (ψ: stepterm_transformer_type).
  Context (ϕ1: RelativizedGMIt_stepterm_type Ze1 T1) (ϕ2: RelativizedGMIt_stepterm_type Ze2 T2).

  Definition is_stepterm_transformer: UU :=
    forall (mbind : drelrefcont_type J (pr1 Ze1) `InitAlg T1),
      pr1 ψ (J_H `InitAlg) (pr1 ϕ1 `InitAlg mbind)  = pr1 ϕ2 `InitAlg (pr1 ψ `InitAlg mbind).

  Lemma isaprop_is_stepterm_transformer: isaprop is_stepterm_transformer.
  Proof.
    apply impred; intros.
    apply (isaset_drelrefcont_type hs).
  Qed.

  Context (RGMIt1: RelativizedGMIt_type Ze1 T1 ϕ1) (RGMIt2: RelativizedGMIt_type Ze2 T2 ϕ2).

  Let gbind1: drelrefcont_type J (pr1 Ze1) `InitAlg T1 := pr1 (pr1 RGMIt1).
  Let gbind2: drelrefcont_type J (pr1 Ze2) `InitAlg T2 := pr1 (pr1 RGMIt2).

  Theorem relativized_fusion_law: is_stepterm_transformer -> pr1 ψ `InitAlg gbind1 = gbind2.
  Proof.
    intro isstt.
    apply path_to_ctr.
    intros c1 c2 f.
    red.
    assert (issttinst1 := maponpaths pr1 (isstt gbind1)).
    eapply pathscomp0.
    2: { eapply (maponpaths (fun x: drelrefcont_op J (pr1 Ze2) (functor_opp J_H `InitAlg) T2 => x c1 c2 f)).
         exact issttinst1. }
    clear issttinst1.
    assert (ψnatinst := nat_trans_ax ψ _ _ (alg_map J_H InitAlg)).
    apply toforallpaths in ψnatinst.
    assert (ψnatinst1 := ψnatinst gbind1).
    assert (ψnatinst2 := maponpaths pr1 ψnatinst1).
    apply toforallpaths in ψnatinst2.
    assert (ψnatinst3 := ψnatinst2 c1).
    apply toforallpaths in ψnatinst3.
    assert (ψnatinst4 := ψnatinst3 c2).
    apply toforallpaths in ψnatinst4.
    assert (ψnatinst5 := ψnatinst4 f).
    clear ψnatinst ψnatinst1 ψnatinst2 ψnatinst3 ψnatinst4.
    cbn in ψnatinst5.
    unfold drelrefcont_functor_on_morphism_op in ψnatinst5.
    rewrite id_right in ψnatinst5.
    apply pathsinv0.
    eapply pathscomp0.
    2: { exact ψnatinst5. }
    clear ψnatinst5.
    eapply (maponpaths (fun x => pr1 (pr1 ψ (J_H `InitAlg) x) c1 c2 f)).
    clear c1 c2 f.
    apply (drelrefcont_type_eq hs).
    intros c1 c2 f.
    cbn.
    rewrite id_right.
    apply pathsinv0.
    apply (pr2 (pr1 RGMIt1)).
  Qed.

  End fusion_law.

  Section specialized_fusion_law.

    Context (ψ: stepterm_transformer_type).

    Context {G1 : functor [C, D, hs] [C, D, hs]} (ρ1 : [C, D, hs] ⟦ G1 T1, T1 ⟧).
    Context {G2 : functor [C, D, hs] [C, D, hs]} (ρ2 : [C, D, hs] ⟦ G2 T2, T2 ⟧).

    Context (ϕ1: SpecializedRelativizedGMIt_stepterm_type Ze1 T1 G1) (ϕ2: SpecializedRelativizedGMIt_stepterm_type Ze2 T2 G2).
    Context (SRGMIt1: SpecializedRelativizedGMIt_type Ze1 T1 G1 ρ1 ϕ1) (SRGMIt2: SpecializedRelativizedGMIt_type Ze2 T2 G2 ρ2 ϕ2).

  Let gbind1: drelrefcont_type J (pr1 Ze1) `InitAlg T1 := pr1 (pr1 SRGMIt1).
  Let gbind2: drelrefcont_type J (pr1 Ze2) `InitAlg T2 := pr1 (pr1 SRGMIt2).

  Corollary specialized_relativized_fusion_law: is_stepterm_transformer ψ (generalϕ Ze1 ρ1 ϕ1) (generalϕ Ze2 ρ2 ϕ2) -> pr1 ψ `InitAlg gbind1 = gbind2.
  Proof.
    apply relativized_fusion_law.
  Qed.

  End specialized_fusion_law.


  Section base_change.

  Context (π: Ze2 --> Ze1) (γ: T1 ⟹ T2).

  Definition mbind_base_change_op_op {X : [C, D, hs]^op} (mbind : drelrefcont_type J (pr1 Ze1) X T1):
    drelrefcont_op J (pr1 Ze2) X T2.
  Proof.
    intros c1 c2 f.
    exact (pr1 mbind c1 c2 (f · pr1 π c2) · γ c2).
  Defined.

  Lemma mbind_base_change_op_ok {X : [C, D, hs]^op} (mbind : drelrefcont_type J (pr1 Ze1) X T1):
    drelrefcont_natural (mbind_base_change_op_op mbind).
  Proof.
    intros c1 c1' c2 c2' h1 h2 f.
    unfold mbind_base_change_op_op.
    eapply pathscomp0.
    2: { rewrite <- assoc.
         rewrite nat_trans_ax.
         rewrite assoc.
         rewrite <- (assoc (# J h1)).
         apply cancel_postcomposition.
         apply (pr2 mbind).
    }
    repeat rewrite <- assoc.
    do 2 apply maponpaths.
    apply pathsinv0.
    apply nat_trans_ax.
  Qed.

  Definition mbind_base_change_op: nat_trans_data (drelrefcont_functor_with_fixed_protomonad Ze1 T1)
                                                   (drelrefcont_functor_with_fixed_protomonad Ze2 T2).
  Proof.
    intros X mbind. cbn in mbind.
    use tpair.
      - exact (mbind_base_change_op_op mbind).
      - exact (mbind_base_change_op_ok mbind).
  Defined.

  Lemma mbind_base_change_op_is_nat_trans: is_nat_trans _ _ mbind_base_change_op.
  Proof.
    intros X X' α.
    apply funextfun; intro mbind.
    apply (drelrefcont_type_eq hs); intros c1 c2 f.
    cbn.
    unfold mbind_base_change_op_op, drelrefcont_functor_on_morphism_op.
    cbn.
    rewrite <- assoc.
    apply maponpaths.
    do 2 rewrite id_right.
    apply idpath.
  Qed.

  Definition mbind_base_change: stepterm_transformer_type := mbind_base_change_op ,, mbind_base_change_op_is_nat_trans.

  End base_change.

End different_protomonads.

Section base_change_for_term_substitution.

  Context {Ze1 Ze2 : precategory_Ptm hs J}.
  Context (π: Ze2 --> Ze1).
  Context (k1: Ze1 --> ptm_from_alg InitAlg).
  Context (k2: Ze2 --> ptm_from_alg InitAlg).
  Context (k2_ok: k2 = π · k1).
  Context (SRGMIt1: SpecializedRelativizedGMIt_type Ze1 `InitAlg (G Ze1) (ρ Ze1 k1) (ϕ Ze1)).
  Context (SRGMIt2: SpecializedRelativizedGMIt_type Ze2 `InitAlg (G Ze2) (ρ Ze2 k2) (ϕ Ze2)).

  Let gbindWithLaw1 : drelrefcont_type J (pr1 Ze1) `InitAlg `InitAlg := gbindWithLaw Ze1 k1 SRGMIt1.
  Let gbindWithLaw2 : drelrefcont_type J (pr1 Ze2) `InitAlg `InitAlg := gbindWithLaw Ze2 k2 SRGMIt2.

  Lemma gbind_base_change: pr1 (mbind_base_change Ze1 Ze2 `InitAlg `InitAlg π (nat_trans_id _)) `InitAlg gbindWithLaw1 =
                           gbindWithLaw2.
  Proof.
    apply specialized_relativized_fusion_law.
    intro mbind.
    apply (drelrefcont_type_eq hs); intros c1 c2 f.
    cbn.
    unfold mbind_base_change_op_op, generalϕ_op, generalϕ_op_op, ϕ_op_op.
    cbn.
    unfold ϕ_op_op.
    cbn.
    rewrite id_right.
    eapply pathscomp0.
    { apply precompWithBinCoproductArrow. }
    eapply pathscomp0.
    2: { apply pathsinv0.
         apply precompWithBinCoproductArrow. }
    rewrite <- assoc.
    rewrite k2_ok.
    apply maponpaths.
    apply cancel_postcomposition.
    change (ColimFunctor hs (initChain InitialCD J_H) (λ a : C, CC (diagram_pointwise hs (initChain InitialCD J_H) a))) with `InitAlg.
    change (pr1 (lift `InitAlg (Ze1,, `InitAlg)
                      mbind)
                c1 c2 (f · pr1 π c2) =
            pr1 (lift `InitAlg (Ze2,, `InitAlg)
                      (mbind_base_change_op Ze1 Ze2 `InitAlg `InitAlg π (nat_trans_id (pr1 `InitAlg)) `InitAlg mbind))
                c1 c2 f).
    assert (aux := pr2 (lift `InitAlg) _ _ ((π,,nat_trans_id (pr1 `InitAlg)): (precategory_Ptm hs J)^op ⊠ [C, D, hs]^op ⟦ (Ze1,,`InitAlg), (Ze2,,`InitAlg) ⟧)).
    apply toforallpaths in aux.
    assert (aux1 := aux mbind).
    assert (aux2 := maponpaths pr1 aux1).
    apply toforallpaths in aux2.
    assert (aux3 := aux2 c1).
    apply toforallpaths in aux3.
    assert (aux4 := aux3 c2).
    apply toforallpaths in aux4.
    assert (aux5 := aux4 f).
    clear aux aux1 aux2 aux3 aux4.
    cbn in aux5.
    unfold drelrefcont_functor_on_morphism_op in aux5.
    rewrite (functor_id H) in aux5.
    rewrite id_left in aux5.
    eapply pathscomp0.
    { apply pathsinv0.
      exact aux5. }
    clear aux5.
    eapply (maponpaths (fun x => pr1 (lift `InitAlg (Ze2,, `InitAlg) x) c1 c2 f)).
    clear c1 c2 f.
    apply (drelrefcont_type_eq hs).
    intros c1 c2 f.
    cbn.
    rewrite id_left.
    unfold mbind_base_change_op_op.
    apply pathsinv0.
    apply id_right.
  Qed.

End base_change_for_term_substitution.

Section application_to_the_two_instances.

  Context (SRGMIt1: SpecializedRelativizedGMIt_type Ze1 `InitAlg (G Ze1) (ρ Ze1 k1) (ϕ Ze1)).
  Context (SRGMIt0: SpecializedRelativizedGMIt_type Ze0 `InitAlg (G Ze0) (ρ Ze0 k0) (ϕ Ze0)).

  Lemma gbind0_vs_gbind1: pr1 (mbind_base_change Ze1 Ze0 `InitAlg `InitAlg k0 (nat_trans_id _)) `InitAlg (gbind1WithLaw SRGMIt1) =
                          gbind0WithLaw SRGMIt0.
  Proof.
    apply gbind_base_change.
    apply pathsinv0.
    apply id_right.
  Qed.

End application_to_the_two_instances.


End construction.
