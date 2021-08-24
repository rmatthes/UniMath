
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of signatures
-    Proof that two forms of strength laws are equivalent


************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrength.
Require Import UniMath.CategoryTheory.Monoidal.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.PointedFunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.Notation.

Local Open Scope subsys.

(** Goal: define signatures as pairs of a rank-2 functor and a "strength" *)

(** * Definition of signatures *)

Section fix_a_category.

Context (C : precategory) (hs : has_homsets C).

(** in the original definition, this second category was the same as the first one *)
Context (D : precategory) (hsD : has_homsets D).

(** we do not yet have a use of this third category being different from the very first one *)
Context (D' : precategory) (hsD' : has_homsets D').

Section about_signatures.

(** [H] is a rank-2 functor: a functor between functor categories *)
Context (H : functor [C, D', hsD'] [C, D, hsD]).

(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hs).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]).


(** ** Source and target of the natural transformation [θ] *)


(** Source is given by [(X,Z) => H(X)∙U(Z)] *)
Definition θ_source: ([C, D', hsD'] ⊠ Ptd) ⟶ [C, D, hsD].
Proof.
  apply (functor_composite (pair_functor H U)).
  apply (functor_composite binswap_pair_functor).
  apply functorial_composition.
Defined.

Lemma θ_source_ok: functor_on_objects θ_source =  λ FX : [C, D', hsD'] ⊠ Ptd, H (pr1 FX) • U (pr2 FX).
Proof.
  apply idpath.
Qed.

(** Target is given by [(X,Z) => H(X∙U(Z))] *)
Definition θ_target : ([C, D', hsD'] ⊠ Ptd) ⟶ [C, D, hsD].
Proof.
  apply (functor_composite (pair_functor (functor_identity _) U)).
  apply (functor_composite binswap_pair_functor).
  use (functor_composite _ H).
  apply functorial_composition.
Defined.

Lemma θ_target_ok: functor_on_objects θ_target =  λ FX : [C, D', hsD'] ⊠ Ptd, H (pr1 FX • U (pr2 FX)).
Proof.
  apply idpath.
Qed.

(** * Two alternative versions of the strength laws *)


(** We assume a suitable (bi)natural transformation [θ] *)
Hypothesis θ : θ_source ⟹ θ_target.

(** [θ] is supposed to satisfy two strength laws *)

Definition θ_Strength1 : UU := ∏ X : [C, D', hsD'],
  (θ (X ⊗ (id_Ptd C hs))) · # H (identity X : functor_composite (functor_identity C) X ⟹ pr1 X)
          = nat_trans_id _ .

Section Strength_law_1_intensional.

(** needs the heterogeneous formulation of the monoidal operation to type-check *)
Definition θ_Strength1_int : UU
  := ∏ X : [C, D', hsD'],
           θ (X ⊗ (id_Ptd C hs)) · # H (λ_functor _) = λ_functor _.

Lemma isaprop_θ_Strength1_int: isaprop θ_Strength1_int.
Proof.
  apply impred; intros X x x'.
  apply isaset_nat_trans; try exact hsD.
Qed.

Lemma θ_Strength1_int_implies_θ_Strength1 : θ_Strength1_int → θ_Strength1.
Proof.
  unfold θ_Strength1_int, θ_Strength1.
  intros T X.
  assert (TX := T X).
  apply nat_trans_eq; try assumption.
  intro c; cbn.
  assert (T2 := nat_trans_eq_pointwise TX c).
  cbn in *.
  assert (X0 : λ_functor X = identity (X : [C, D', hsD'])).
  { apply nat_trans_eq; try assumption; intros; apply idpath. }
  rewrite X0 in T2.
  apply T2.
Qed.

(* practically the same proof works in the opposite direction *)
Lemma θ_Strength1_implies_θ_Strength1_int : θ_Strength1 → θ_Strength1_int.
Proof.
  unfold θ_Strength1_int, θ_Strength1.
  intros T X.
  assert (TX := T X).
  apply nat_trans_eq; try assumption.
  intro c; cbn.
  assert (T2 := nat_trans_eq_pointwise TX c).
  cbn in *.
  assert (X0 : λ_functor X = identity (X : [C, D', hsD'])).
  { apply nat_trans_eq; try assumption; intros; apply idpath. }
  rewrite X0.
  apply T2.
Qed.


End Strength_law_1_intensional.


Definition θ_Strength2 : UU := ∏ (X : [C, D', hsD']) (Z Z' : Ptd) (Y : [C, D', hsD'])
           (α : functor_compose hs hsD' (functor_composite (U Z) (U Z')) X --> Y),
    θ (X ⊗ (Z p• Z' : Ptd)) · # H α =
    θ (X ⊗ Z') •• (U Z) · θ ((functor_compose hs hsD' (U Z') X) ⊗ Z) ·
       # H (α : functor_compose hs hsD' (U Z) (X • (U Z')) --> Y).


Section Strength_law_2_intensional.
 (* does not typecheck in the heterogeneous formulation *)
Definition θ_Strength2_int : UU
  := ∏ (X : [C, D', hsD']) (Z Z' : Ptd),
      θ (X ⊗ (Z p• Z')) · #H (α_functor (U Z) (U Z') X )  =
      (α_functor (U Z) (U Z') (H X) : [C, D, hsD] ⟦ functor_compose hs hsD (functor_composite (U Z) (U Z')) (H X), functor_composite (U Z) (functor_composite (U Z') (H X)) ⟧
      ) ·
      θ (X ⊗ Z') •• (U Z) · θ ((functor_compose hs hsD' (U Z') X) ⊗ Z) .

Lemma isaprop_θ_Strength2_int: isaprop θ_Strength2_int.
Proof.
  apply impred; intros X.
  apply impred; intros Z.
  apply impred; intros Z'.
  apply isaset_nat_trans; try exact hsD.
Qed.

Lemma θ_Strength2_int_implies_θ_Strength2 : θ_Strength2_int → θ_Strength2.
Proof.
  unfold θ_Strength2_int, θ_Strength2.
  intros T X Z Z' Y a.
  apply nat_trans_eq; try assumption.
  intro c.

  assert (TXZZ' := T X Z Z').
  assert (TXZZ'c := nat_trans_eq_pointwise TXZZ' c).
  cbn in TXZZ'c.
  clear T TXZZ'.
  rewrite id_left in TXZZ'c.
  cbn. rewrite <- TXZZ'c; clear TXZZ'c.
  rewrite <- assoc.
  apply maponpaths.
  assert (functor_comp_H := functor_comp H (α_functor (pr1 Z) (pr1 Z') X)
           (a : functor_compose hs hsD' (U Z) (functor_composite (U Z') X) --> Y)).
  assert (functor_comp_H_c := nat_trans_eq_pointwise functor_comp_H c).
  cbn in functor_comp_H_c.
  eapply pathscomp0.
  2: { apply functor_comp_H_c. }
  clear functor_comp_H functor_comp_H_c.
  revert c.
  apply nat_trans_eq_pointwise.
  apply maponpaths.
  apply nat_trans_eq; try assumption.
  intro c; apply pathsinv0, id_left.
Qed.

(* for curiosity also the other direction *)
Lemma θ_Strength2_implies_θ_Strength2_int : θ_Strength2 → θ_Strength2_int.
Proof.
  unfold θ_Strength2_int, θ_Strength2.
  intros T X Z Z'.
  assert (TXZZ'_inst := T X Z Z' (functor_compose hs hsD' (U Z)
          (functor_composite (U Z') X)) (α_functor (pr1 Z) (pr1 Z') X)).
  eapply pathscomp0.
  { apply TXZZ'_inst. }
  clear T TXZZ'_inst.
  apply nat_trans_eq; try assumption.
  intro c.
  cbn.
  rewrite id_left.
  rewrite <- assoc.
  apply maponpaths.
  eapply pathscomp0; [| apply id_right].
  apply maponpaths.
  assert (functor_id_H := functor_id H (functor_compose hs hsD' (pr1 Z) (functor_composite (pr1 Z') X))).
  assert (functor_id_H_c := nat_trans_eq_pointwise functor_id_H c).
  eapply pathscomp0; [| apply functor_id_H_c].
  clear functor_id_H functor_id_H_c.
  revert c.
  apply nat_trans_eq_pointwise.
  apply maponpaths.
  apply nat_trans_eq; try assumption;
  intro c; apply idpath.
Qed.

Definition θ_Strength2_int_nicer : UU := ∏ (X : [C, D', hsD']) (Z Z' : Ptd),
      θ (X ⊗ (Z p• Z'))  =
      (α_functor (U Z) (U Z') (H X) : [C, D, hsD] ⟦ functor_compose hs hsD (functor_composite (U Z) (U Z')) (H X), functor_composite (U Z) (functor_composite (U Z') (H X)) ⟧) ·
      θ (X ⊗ Z') •• (U Z) · θ ((functor_compose hs hsD' (U Z') X) ⊗ Z) · #H (α_functor_inv (U Z) (U Z') X ).


Lemma θ_Strength2_int_implies_θ_Strength2_int_nicer: θ_Strength2_int -> θ_Strength2_int_nicer.
Proof.
  intro Hyp.
  intros X Z Z'.
  assert (HypX := Hyp X Z Z').
  set (auxiso := functor_on_z_iso H (_,,(α_functor_pointwise_is_z_iso hsD' (U Z) (U Z') X))).
  apply pathsinv0 in HypX. apply (z_iso_inv_on_left _ _ _ _ auxiso) in HypX.
  assumption.
Qed.

Lemma θ_Strength2_int_nicer_implies_θ_Strength2_int: θ_Strength2_int_nicer -> θ_Strength2_int.
  intro Hyp.
  intros X Z Z'.
  assert (HypX := Hyp X Z Z').
  set (auxiso := functor_on_z_iso H (_,,(α_functor_pointwise_is_z_iso hsD' (U Z) (U Z') X))).
  apply (z_iso_inv_to_right _ _ _ _ auxiso).
  assumption.
Qed.

End Strength_law_2_intensional.

(** Not having a general theory of binatural transformations, we isolate
    naturality in each component here *)

Lemma θ_nat_1 (X X' : [C, D', hsD']) (α : X --> X') (Z : Ptd)
  : compose (C := [C, D, hsD]) (# H α ∙∙ nat_trans_id (pr1 (U Z))) (θ (X' ⊗ Z)) =
        θ (X ⊗ Z) · # H (α ∙∙ nat_trans_id (pr1 (U Z))).
Proof.
  set (t := nat_trans_ax θ).
  set (t' := t (X ⊗ Z) (X' ⊗ Z)).
  set (t'' := t' (precatbinprodmor α (identity _ ))).
  cbn in t''.
  exact t''.
Qed.

(* the following makes sense but is wrong
Lemma θ_nat_1' (X X' : EndC) (α : X --> X') (Z : Ptd)
  : compose(C:=EndC) (# H α øø (U Z)) (θ (X' ⊗ Z)) =
        θ (X ⊗ Z)· # H (α øø (U Z)).
Proof.
Abort.
*)

Lemma θ_nat_1_pointwise (X X' : [C, D', hsD']) (α : X --> X') (Z : Ptd) (c : C)
  :  pr1 (# H α) ((pr1 Z) c) · pr1 (θ (X' ⊗ Z)) c =
       pr1 (θ (X ⊗ Z)) c · pr1 (# H (α ∙∙ nat_trans_id (pr1 Z))) c.
Proof.
  assert (t := θ_nat_1 _ _ α Z).
  assert (t' := nat_trans_eq_weq hsD _ _ t c).
  clear t.
  cbn in t'.
  etrans.
  2: exact t'.
  clear t'.
  apply pathsinv0.
  etrans.
  { apply cancel_postcomposition.
    apply maponpaths.
    apply functor_id. }
  rewrite <- assoc.
  rewrite id_left.
  apply idpath.
Qed.

Lemma θ_nat_2 (X : [C, D', hsD']) (Z Z' : Ptd) (f : Z --> Z')
  : compose (C := [C, D, hsD]) (identity (H X) ∙∙ pr1 f) (θ (X ⊗ Z')) =
       θ (X ⊗ Z) · # H (identity X ∙∙ pr1 f).
Proof.
  set (t := nat_trans_ax θ).
  set (t' := t (X ⊗ Z) (X ⊗ Z') (precatbinprodmor (identity _ ) f)).
  cbn in t'.
  unfold precatbinprodmor in t'.
  cbn in t'.
  set (T := functor_id H X).
  cbn in *.
  rewrite T in t'. clear T.
  exact t'.
Qed.

Lemma θ_nat_2_pointwise (X : [C, D', hsD']) (Z Z' : Ptd) (f : Z --> Z') (c : C)
  :  # (pr1 (H X)) ((pr1 f) c) · pr1 (θ (X ⊗ Z')) c =
       pr1 (θ (X ⊗ Z)) c · pr1 (# H (identity X ∙∙ pr1 f)) c .
Proof.
  set (t := θ_nat_2 X _ _ f).
  set (t' := nat_trans_eq_weq hsD _ _ t c).
  clearbody t'; clear t.
  cbn in t'.
  rewrite id_left in t'.
  exact t'.
Qed.

End about_signatures.

Section Strength_laws.
(** define strength laws *)

End Strength_laws.


Definition StrengthForSignature (H : [C, D', hsD'] ⟶ [C, D, hsD] ) : UU :=
  ∑ θ : nat_trans (θ_source H) (θ_target H) , θ_Strength1_int H θ × θ_Strength2_int H θ.

Definition Signature : UU
  := ∑ H : [C, D', hsD'] ⟶ [C, D, hsD] , StrengthForSignature H.

Coercion Signature_Functor (S : Signature) : functor _ _ := pr1 S.

Definition theta (H : Signature) : (θ_source H) ⟹ (θ_target H) := pr1 (pr2 H).

Definition Sig_strength_law1 (H : Signature) : θ_Strength1_int _ _ := pr1 (pr2 (pr2 H)).

Definition Sig_strength_law2 (H : Signature) : θ_Strength2_int _ _ := pr2 (pr2 (pr2 H)).

Lemma StrengthForSignature_eq (H : [C, D', hsD'] ⟶ [C, D, hsD] ) (sθ1 sθ2 : StrengthForSignature H) :
  pr1 sθ1 = pr1 sθ2 -> sθ1 = sθ2.
Proof.
  intro Heq.
  apply subtypePath; trivial.
  intro θ. apply isapropdirprod.
  + apply isaprop_θ_Strength1_int.
  + apply isaprop_θ_Strength2_int.
Qed.

End fix_a_category.

Section homogeneous_case.

Context (C : precategory) (hs : has_homsets C).

Local Definition ptd := monoidal_precat_of_pointedfunctors hs.
Local Definition endo := monoidal_precat_of_endofunctors hs.
Local Definition forget := forgetful_functor_from_ptd_as_strong_monoidal_functor hs.

Local Lemma auxH1 (H : functor [C, C, hs] [C, C, hs]) (X : functor C C) :
  # H
    (nat_trans_id (pr1 X)
        ∙∙ nat_z_iso_to_trans_inv
        (make_nat_z_iso (functor_identity C) (functor_identity C) (nat_trans_id (functor_identity C))
                    (is_nat_z_iso_nat_trans_id (functor_identity C)))) =
  identity (H (functor_identity C ∙ X)).
Proof.
  apply functor_id_id.
  apply nat_trans_eq; try assumption; intro c.
  cbn.
  rewrite id_left.
  apply functor_id.
Qed.

Local Lemma auxH2 (H : functor [C, C, hs] [C, C, hs]) (X : functor C C)
      (Z Z': precategory_Ptd C hs) :
  # H (nat_trans_id (pr1 X) ∙∙ nat_trans_id (functor_composite (pr1 Z) (pr1 Z'))) =
  identity (H (((pr1 Z) ∙ (pr1 Z')) ∙ X)).
Proof.
  apply functor_id_id.
  apply nat_trans_eq; try assumption; intro c.
  cbn.
  rewrite id_left.
  apply functor_id.
Qed.

Section relative_strength_instantiates_to_signature.

  Context (H : functor [C, C, hs] [C, C, hs])
          (rs : rel_strength forget H).

  Local Definition ϛ : rel_strength_nat forget H := pr1 rs.

  Local Definition ϛ_pentagon_eq : rel_strength_pentagon_eq forget H ϛ
    := pr1 (pr2 rs).

  Local Definition ϛ_rectangle_eq : rel_strength_rectangle_eq forget H ϛ
    := pr2 (pr2 rs).

  Local Definition θ : θ_source C hs C hs C hs H ⟹ θ_target C hs C hs C hs H
    := pre_whisker binswap_pair_functor ϛ.

  Lemma signature_from_rel_strength_laws : θ_Strength1_int C hs C hs C hs H θ ×
                                           θ_Strength2_int C hs C hs C hs H θ.
  Proof.
    split; red.
    - intro X.
      cbn.
      apply nat_trans_eq; try assumption; intro c.
      cbn.
      assert (Hyp := nat_trans_eq_weq hs _ _ (ϛ_pentagon_eq X) c).
      cbn in Hyp.
      rewrite functor_id in Hyp.
      do 2 rewrite id_left in Hyp.
      etrans.
      2: exact Hyp.
      clear Hyp.
      rewrite <- assoc.
      apply maponpaths.
      etrans.
      apply pathsinv0.
      apply id_left.
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (nat_trans_eq_weq hs _ _ (auxH1 H X) c).
    - intros X Z Z'.
      cbn.
      apply nat_trans_eq; try assumption; intro c.
      cbn.
      rewrite id_left.
      assert (Hyp := nat_trans_eq_weq hs _ _ (ϛ_rectangle_eq Z Z' X) c).
      cbn in Hyp.
      do 2 rewrite functor_id in Hyp.
      do 3 rewrite id_left in Hyp.
      rewrite id_right in Hyp.
      etrans.
      2: exact Hyp.
      clear Hyp.
      apply cancel_postcomposition.
      etrans.
      apply pathsinv0.
      apply id_right.
      apply maponpaths.
      apply pathsinv0.
      apply (nat_trans_eq_weq hs _ _ (auxH2 H X Z Z') c).
  Qed.

  Definition signature_from_rel_strength : Signature C hs C hs C hs.
  Proof.
    exists H. exists θ.
    exact signature_from_rel_strength_laws.
  Defined.

End relative_strength_instantiates_to_signature.

Section strength_in_signature_is_a_relative_strength.

  Context (sig : Signature C hs C hs C hs).

  Local Definition H := pr1 sig.
  Local Definition θ' := pr1 (pr2 sig).
  Local Definition ϛ' : rel_strength_nat forget H := pre_whisker binswap_pair_functor θ'.

  Local Definition θ'_strength_law1 := Sig_strength_law1 _ _ _ _ _ _ sig.
  Local Definition θ'_strength_law2 := Sig_strength_law2 _ _ _ _ _ _ sig.

  Lemma rel_strength_from_signature_laws : rel_strength_pentagon_eq forget H ϛ' ×
                                           rel_strength_rectangle_eq forget H ϛ'.
  Proof.
    split.
    - intro X.
      apply nat_trans_eq; try assumption; intro c.
      cbn.
      assert (Hyp := nat_trans_eq_weq hs _ _ (θ'_strength_law1 X) c).
      cbn in Hyp.
      fold θ' H in Hyp.
      rewrite functor_id.
      do 2 rewrite id_left.
      etrans.
      2: exact Hyp.
      clear Hyp.
      rewrite <- assoc.
      apply maponpaths.
      apply pathsinv0.
      etrans.
      apply pathsinv0.
      apply id_left.
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (nat_trans_eq_weq hs _ _ (auxH1 H X) c).
    - intros Z Z' X.
      apply nat_trans_eq; try assumption; intro c.
      cbn.
      assert (Hyp := nat_trans_eq_weq hs _ _ (θ'_strength_law2 X Z Z') c).
      cbn in Hyp.
      fold θ' H in Hyp.
      do 2 rewrite functor_id.
      do 3 rewrite id_left.
      rewrite id_right.
      rewrite id_left in Hyp.
      etrans.
      2: exact Hyp.
      clear Hyp.
      apply cancel_postcomposition.
      etrans.
      2: apply id_right.
      apply maponpaths.
      apply (nat_trans_eq_weq hs _ _ (auxH2 H X Z Z') c).
  Qed.

  Definition rel_strength_from_signature : rel_strength forget H := (ϛ',,rel_strength_from_signature_laws).

End strength_in_signature_is_a_relative_strength.

End homogeneous_case.


Arguments theta {_ _ _ _ _ _} _ .
Arguments θ_source {_ _ _ _ _ _ } _ .
Arguments θ_target {_ _ _ _ _ _ } _ .
Arguments θ_Strength1 {_ _ _ _ _ _ _ } _ .
Arguments θ_Strength2 {_ _ _ _ _ _ _ } _ .
Arguments θ_Strength1_int {_ _ _ _ _ _ _} _ .
Arguments θ_Strength2_int {_ _ _ _ _ _ _} _ .
Arguments Sig_strength_law1 {_ _ _ _ _ _} _.
Arguments Sig_strength_law2 {_ _ _ _ _ _} _.
Arguments Signature_Functor {_ _ _ _ _ _} _.
Arguments θ_Strength1_int_implies_θ_Strength1 {_ _ _ _ _ _ _} _ _.
Arguments θ_Strength2_int_implies_θ_Strength2 {_ _ _ _ _ _ _} _ _.
Arguments θ_Strength2_int_implies_θ_Strength2_int_nicer {_ _ _ _ _ _ _} _ _.
