(** Constructs the actegory with the action of the endomorphisms by precomposition on a fixed hom-category of a bicategory

Author: Ralph Matthes 2022

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.WhiskeredMonoidalFromBicategory.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.Monoidal.CoproductsInActegories.

Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

Import Bicat.Notations.
Import BifunctorNotations.

Local Open Scope cat.

Section Action_From_Precomposition.

Context {C : bicat}.
Context (c0 d0 : ob C).

Local Definition endocat : category := hom c0 c0.
Local Definition Mon_endo: monoidal endocat := monoidal_from_bicat_and_ob c0.
Local Definition homcat : category := hom c0 d0.


Definition action_from_precomp_data : bifunctor_data endocat homcat homcat.
Proof.
  use make_bifunctor_data.
  - intros v f. exact (v · f).
  - intros v f1 f2 β. exact (v ◃ β).
  - intros f v1 v2 α. exact (α ▹ f).
Defined.

(* (** we explicitly do not opacify the following definition: *) *)
Definition action_from_precomp_laws : is_bifunctor action_from_precomp_data.
Proof.
  repeat split.
  - intros v f. apply lwhisker_id2.
  - intros f v. apply id2_rwhisker.
  - intros v f1 f2 f3 β1 β2. apply pathsinv0, lwhisker_vcomp.
  - intros f v1 v2 v3 α1 α2. apply pathsinv0, rwhisker_vcomp.
  - intros v1 v2 f1 f2 α β. apply vcomp_whisker.
Qed. (* Defined. *)

Definition action_from_precomp : bifunctor endocat homcat homcat :=
  make_bifunctor action_from_precomp_data action_from_precomp_laws.

Definition actegory_from_precomp_data : actegory_data Mon_endo homcat.
Proof.
  exists action_from_precomp.
  repeat split.
  - intro f. apply lunitor.
  - intro f. apply linvunitor.
  - intros v w f. apply rassociator.
  - intros v w f. apply lassociator.
Defined.

Lemma actegory_from_precomp_laws : actegory_laws Mon_endo actegory_from_precomp_data.
Proof.
  repeat split.
  - intros f g β. cbn. apply vcomp_lunitor.
  - cbn. apply lunitor_linvunitor.
  - cbn. apply linvunitor_lunitor.
  - intros v w f f' β. cbn. apply lwhisker_lwhisker_rassociator.
  - intros v v' w f α. cbn. apply pathsinv0, rwhisker_rwhisker_alt.
  - intros v w w' f α. cbn. apply rwhisker_lwhisker_rassociator.
  - cbn. apply rassociator_lassociator.
  - cbn. apply lassociator_rassociator.
  - intros v f. cbn. apply lunitor_lwhisker.
  - intros w v v' f. cbn. apply rassociator_rassociator.
Qed.

Definition actegory_from_precomp : actegory Mon_endo homcat :=
  actegory_from_precomp_data,,actegory_from_precomp_laws.

End Action_From_Precomposition.

Section TheHomogeneousCase.

Context {C : bicat}.
Context (c0 : ob C).

(*
(** requires [action_from_precomp] with known proofs of the laws *)
Definition action_in_actegory_from_precomp_as_self_action :
  actegory_action (Mon_endo c0) (actegory_from_precomp c0 c0) = actegory_action (Mon_endo c0) (actegory_with_canonical_self_action (Mon_endo c0)).
Proof.
  change (pr11 (actegory_from_precomp c0 c0) = pr11 (actegory_with_canonical_self_action (Mon_endo c0))).
  apply idpath.
Defined.
*)
(*
Lemma actegory_from_precomp_as_self_action :
  actegory_from_precomp c0 c0 = actegory_with_canonical_self_action (Mon_endo c0).
Proof.
  use total2_paths_f.
  2: { apply isaprop_actegory_laws. }
  use total2_paths_f.
  { apply action_in_actegory_from_precomp_as_self_action. }
  use total2_paths_f.
  { apply idpath. }
  use total2_paths_f.
  { apply idpath. }
  apply idpath.
Qed. (* slow *)
*)

(* the following is a test only since we are only interested in pointed tensorial strength:
Lemma lax_lineators_from_precomp_and_self_action_agree (H: functor (homcat c0 c0) (homcat c0 c0)) :
  lineator_lax (Mon_endo c0) (actegory_from_precomp c0 c0)
                             (actegory_from_precomp c0 c0) H =
  lineator_lax (Mon_endo c0) (actegory_with_canonical_self_action (Mon_endo c0))
                             (actegory_with_canonical_self_action (Mon_endo c0)) H.
Proof.
  Time (apply idpath). (* ~40s *)
  Time Qed. (* ~40s *)
(* if instead of equality, [≃] is asked for:
  use weqfibtototal.
  intro ld.
  use weqimplimpl.
  4: { apply isaprop_lineator_laxlaws. }
  3: { apply isaprop_lineator_laxlaws. }
  - intro ldl. Time (exact ldl). (* ~50s *)
  - intro ldl. Time (exact ldl). (* ~ 40s *)
Time Defined. (* ~100s *) *)
*)

Section Lifting.

  Context {W : category} (Mon_W : monoidal W) {F : W ⟶ endocat c0} (U : MonoidalFunctorsWhiskered.fmonoidal Mon_W (Mon_endo c0) F).

Local Definition lifted_act_from_precomp : actegory Mon_W (endocat c0) :=
      lifted_actegory (Mon_endo c0) (actegory_from_precomp c0 c0) Mon_W U.
Local Definition lifted_act_from_self : actegory Mon_W (endocat c0) :=
  lifted_actegory (Mon_endo c0) (actegory_with_canonical_self_action (Mon_endo c0)) Mon_W U.

Definition lax_lineators_data_from_lifted_precomp_and_lifted_self_action_agree_aux (H: functor (homcat c0 c0) (homcat c0 c0)) :
  lineator_data Mon_W lifted_act_from_precomp lifted_act_from_precomp H <->
  lineator_data Mon_W lifted_act_from_self lifted_act_from_self H.
Proof.
  split.
  + intro ld.
    intros v x.
    set (ld_inst := ld v x).
    cbn.
    exact ld_inst.
  + intro ld.
    intros v x.
    set (ld_inst := ld v x).
    cbn.
    exact ld_inst.
Time Defined. (* looks desperate, but next definition needs the very definition *)


Definition lax_lineators_data_from_lifted_precomp_and_lifted_self_action_agree (H: functor (homcat c0 c0) (homcat c0 c0)) :
  lineator_data Mon_W lifted_act_from_precomp lifted_act_from_precomp H ≃
  lineator_data Mon_W lifted_act_from_self lifted_act_from_self H.
Proof.
  use weq_iso.
  + exact (pr1 (lax_lineators_data_from_lifted_precomp_and_lifted_self_action_agree_aux H)).
  + exact (pr2 (lax_lineators_data_from_lifted_precomp_and_lifted_self_action_agree_aux H)).
  + intro ld.
    intros v x.
    cbn.
    exact (ld v x).
  + intro ld. apply idpath.
  + intro ld. apply idpath.
Time Defined.

Lemma lax_lineators_from_lifted_precomp_and_lifted_self_action_agree (H: functor (homcat c0 c0) (homcat c0 c0)) :
  lineator_lax Mon_W lifted_act_from_precomp lifted_act_from_precomp H ≃
  lineator_lax Mon_W lifted_act_from_self lifted_act_from_self H.
Proof.
  (* use weqfibtototal.    not seen to terminate*)
  apply (weqbandf (lax_lineators_data_from_lifted_precomp_and_lifted_self_action_agree H)).
  intro ld.
  use weqimplimpl.
  4: { apply isaprop_lineator_laxlaws. }
  3: { apply isaprop_lineator_laxlaws. }
  - intro ldl.
    red; repeat split.
    + intros v x1 x2 g.
      assert (Hyp := pr1 ldl v x1 x2 g).
      simpl.
      change ((F v ◃ # H g) • ld v x2 = ld v x1 • # H (F v ◃ g)). (* this is what the goal would look like after cbn *)
      exact Hyp.
    + intros v1 v2 x f.
      assert (Hyp := pr12 ldl v1 v2 x f).
      simpl.
      change ((# F f ▹ H x) • ld v2 x = ld v1 x • # H (# F f ▹ x)).
      exact Hyp.
    + intros v w x.
      assert (Hyp := pr122 ldl v w x).
      simpl.
      change (ld (v ⊗_{ Mon_W} w) x
                • # H
                ((pr1 (MonoidalFunctorsWhiskered.fmonoidal_preservestensorstrongly U v w) ▹ x) • rassociator (F v) (F w) x) =
                (((pr1 (MonoidalFunctorsWhiskered.fmonoidal_preservestensorstrongly U v w) ▹ H x)
                    • rassociator (F v) (F w) (H x)) • (F v ◃ ld w x)) • ld v (F w · x)).
      exact Hyp.
    + intro x.
      assert (Hyp := pr222 ldl x).
      simpl.
      change (ld (monoidal_unit Mon_W) x
                • # H ((pr1 (MonoidalFunctorsWhiskered.fmonoidal_preservesunitstrongly U) ▹ x) • lunitor x) =
                (pr1 (MonoidalFunctorsWhiskered.fmonoidal_preservesunitstrongly U) ▹ H x) • lunitor (H x)).
      exact Hyp.
  - intro ldl.
    red; repeat split.
    + intros v x1 x2 g.
      assert (Hyp := pr1 ldl v x1 x2 g).
      cbn. (* simpl does not suffice *)
      exact Hyp.
    + intros v1 v2 x f.
      assert (Hyp := pr12 ldl v1 v2 x f).
      cbn.
      exact Hyp.
    + intros v w x.
      assert (Hyp := pr122 ldl v w x).
      cbn.
      exact Hyp.
    + intro x.
      assert (Hyp := pr222 ldl x).
      cbn.
      exact Hyp.
Admitted.  (* Time Defined. not seen to terminate *)

End Lifting.

Let lifted_act_from_precomp_inst := lifted_act_from_precomp (monoidal_pointed_objects (Mon_endo c0)) (forget_monoidal_pointed_objects_monoidal (Mon_endo c0)).

Lemma lax_lineators_from_lifted_precomp_and_lifted_self_action_agree_inst (H: functor (homcat c0 c0) (homcat c0 c0)) :
  lineator_lax (monoidal_pointed_objects (Mon_endo c0)) lifted_act_from_precomp_inst lifted_act_from_precomp_inst H ≃
  lineator_lax (monoidal_pointed_objects (Mon_endo c0))
                   (actegory_with_canonical_pointed_action (Mon_endo c0))
                   (actegory_with_canonical_pointed_action (Mon_endo c0)) H.
Proof.
  exact (lax_lineators_from_lifted_precomp_and_lifted_self_action_agree (monoidal_pointed_objects (Mon_endo c0)) (forget_monoidal_pointed_objects_monoidal (Mon_endo c0)) H).
Qed.

(* (** we should no longer need the proofs of the laws after this result  - is the following command effective? *)
Opaque action_from_precomp_laws. *)

End TheHomogeneousCase.

Section Instantiation_To_Bicategory_Of_Categories.

  Context (C D : category).

  Definition actegoryfromprecomp : actegory (Mon_endo(C:=bicat_of_cats) C)
                                           (homcat(C:=bicat_of_cats) C D)
    := actegory_from_precomp(C:=bicat_of_cats) C D.

  Lemma actegoryfromprecomp_action_pointwise_ok (v : functor C C) (f : functor C D) :
    v ⊗_{actegoryfromprecomp} f = functor_compose v f.
  Proof.
    cbn.
    apply idpath.
  Qed.



Section DistributionOfCoproducts.

Section BinaryCoproduct.

  Context (BCP : BinCoproducts D).

  Definition BCP_homcat_CAT : BinCoproducts (homcat(C:=bicat_of_cats) C D).
  Proof.
    apply BinCoproducts_functor_precat.
    exact BCP.
  Defined.

  Definition actfromprecomp_bincoprod_distributor_data :
    bincoprod_distributor_data (Mon_endo(C:=bicat_of_cats) C) BCP_homcat_CAT actegoryfromprecomp.
  Proof.
    intros F G1 G2.
    cbn.
    use make_nat_trans.
    - intro c. apply identity.
    - intros c c' f.
      rewrite id_left; apply id_right.
  Defined.

  Lemma actfromprecomp_bincoprod_distributor_law :
    bincoprod_distributor_iso_law _ _ _ actfromprecomp_bincoprod_distributor_data.
  Proof.
    intros F G.
    split.
    - apply nat_trans_eq; [apply D |].
      intro c.
      cbn.
      rewrite id_left.
      apply pathsinv0, BinCoproduct_endo_is_identity.
      + apply BinCoproductIn1Commutes.
      + apply BinCoproductIn2Commutes.
    - etrans.
      { apply postcompWithBinCoproductArrow. }
      etrans.
      2: { apply pathsinv0, BinCoproductArrowEta. }
      apply maponpaths_12;
        (rewrite id_right; apply nat_trans_eq; [apply D |]; intro c; apply id_right).
  Qed.

  Definition actfromprecomp_bincoprod_distributor :
    bincoprod_distributor (Mon_endo(C:=bicat_of_cats) C) BCP_homcat_CAT actegoryfromprecomp :=
    _,,actfromprecomp_bincoprod_distributor_law.

End BinaryCoproduct.

Section Coproduct.

  Context {I : UU} (CP : Coproducts I D).

  Definition CP_homcat_CAT : Coproducts I (homcat(C:=bicat_of_cats) C D).
  Proof.
    apply Coproducts_functor_precat.
    exact CP.
  Defined.

  Definition actfromprecomp_coprod_distributor_data :
    coprod_distributor_data (Mon_endo(C:=bicat_of_cats) C) CP_homcat_CAT actegoryfromprecomp.
  Proof.
    intros F Gs.
    cbn.
    use make_nat_trans.
    - intro c. apply identity.
    - intros c c' f.
      rewrite id_left; apply id_right.
  Defined.

  Lemma actfromprecomp_coprod_distributor_law :
    coprod_distributor_iso_law _ _ _ actfromprecomp_coprod_distributor_data.
  Proof.
    intros F Gs.
    split.
    - apply nat_trans_eq; [apply D |].
      intro c.
      cbn.
      rewrite id_left.
      apply pathsinv0, Coproduct_endo_is_identity.
      intro i.
      unfold coproduct_nat_trans_data.
      cbn in Gs.
      apply (CoproductInCommutes I D (λ i0 : I, Gs i0 (pr1 F c)) (CP _) _
               (λ i0 : I, coproduct_nat_trans_in_data I C D CP Gs i0 (pr1 F c)) i).
    - etrans.
      { apply postcompWithCoproductArrow. }
      etrans.
      2: { apply pathsinv0, CoproductArrowEta. }
      apply maponpaths, funextsec; intro i;
        (rewrite id_right; apply nat_trans_eq; [apply D |]; intro c; apply id_right).
  Qed.

  Definition actfromprecomp_coprod_distributor :
    coprod_distributor (Mon_endo(C:=bicat_of_cats) C) CP_homcat_CAT actegoryfromprecomp :=
    _,,actfromprecomp_coprod_distributor_law.

End Coproduct.

End DistributionOfCoproducts.

End Instantiation_To_Bicategory_Of_Categories.
