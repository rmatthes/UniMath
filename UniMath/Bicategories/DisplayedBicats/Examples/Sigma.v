(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

   Dependent sum of displayed bicategories
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition make_total_ob {C : bicat} {D : disp_bicat C} {a : C} (aa : D a)
  : total_bicat D
  := (a,, aa).

Definition make_total_mor {C : bicat} {D : disp_bicat C}
           {a b : C} {f : C⟦a, b⟧}
           {aa : D a} {bb : D b} (ff : aa -->[f] bb)
  : make_total_ob aa --> make_total_ob bb
  := (f,, ff).

Definition make_total_cell {C : bicat} {D : disp_bicat C}
           {a b : C} {f g : C⟦a, b⟧} {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : aa -->[g] bb}
           (η : f ==> g)
           (ηη : ff ==>[η] gg)
  : (make_total_mor ff) ==> (make_total_mor gg)
  := (η,, ηη).

(* Useful? *)
Lemma total_cell_eq {C : bicat} {D : disp_bicat C}
      {a b : C} {f g : C⟦a, b⟧} {aa : D a} {bb : D b}
      {ff : aa -->[f] bb} {gg : aa -->[g] bb}
      (x y : make_total_mor ff ==> make_total_mor gg)
      (e : pr1 x = pr1 y)
      (ee : pr2 x = transportb (λ η : f ==> g, ff ==>[ η] gg) e (pr2 y))
  : x = y.
Proof.
  exact (total2_paths2_b e ee).
Defined.

Section Sigma.
  Variable (C : bicat)
           (D : disp_bicat C)
           (E : disp_bicat (total_bicat D)).

  Definition sigma_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    exists (λ c, ∑ (d : D c), (E (c,,d))).
    intros x y xx yy f.
    exact (∑ (fD : pr1 xx -->[f] pr1 yy), pr2 xx -->[f,,fD] pr2 yy).
  Defined.

  Definition sigma_disp_cat_id_comp
    : disp_cat_id_comp _ sigma_disp_cat_ob_mor.
  Proof.
    apply tpair.
    - intros x xx.
      exists (id_disp _). exact (id_disp (pr2 xx)).
    - intros x y z f g xx yy zz ff gg.
      exists (pr1 ff ;; pr1 gg). exact (pr2 ff ;; pr2 gg).
  Defined.

  Definition sigma_disp_cat_data : disp_cat_data C
    := (_ ,, sigma_disp_cat_id_comp).

  Definition sigma_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
  Proof.
    exists sigma_disp_cat_data.
    red.
    intros c c' f g x d d' ff gg.
    cbn in *.
    use (∑ xx : pr1 ff ==>[x] pr1 gg , _).
    set (PPP := @prebicat_cells (total_bicat D) (c,, pr1 d) (c',, pr1 d')
                                (f,, pr1 ff) (g,, pr1 gg)).
    exact (pr2 ff ==>[(x,, xx) : PPP] pr2 gg).
  Defined.

  Definition sigma_bicat_data : disp_prebicat_data C.
  Proof.
    exists sigma_prebicat_1_id_comp_cells.
    repeat split; cbn; first [intros * | intros].
    - exists (disp_id2 _). exact (disp_id2 _).
    - exists (disp_lunitor (pr1 f')). exact (disp_lunitor (pr2 f')).
    - exists (disp_runitor (pr1 f')). exact (disp_runitor (pr2 f')).
    - exists (disp_linvunitor (pr1 f')). exact (disp_linvunitor (pr2 f')).
    - exists (disp_rinvunitor (pr1 f')). exact (disp_rinvunitor (pr2 f')).
    - exists (disp_rassociator (pr1 ff) (pr1 gg) (pr1 hh)).
      exact (disp_rassociator (pr2 ff) (pr2 gg) (pr2 hh)).
    - exists (disp_lassociator (pr1 ff) (pr1 gg) (pr1 hh)).
      exact (disp_lassociator (pr2 ff) (pr2 gg) (pr2 hh)).
    - intros xx yy.
      exists (disp_vcomp2 (pr1 xx) (pr1 yy)).
      exact (disp_vcomp2 (pr2 xx) (pr2 yy)).
    - intros xx.
      exists (disp_lwhisker (pr1 ff) (pr1 xx)).
      exact (disp_lwhisker (pr2 ff) (pr2 xx)).
    - intros xx.
      exists (disp_rwhisker (pr1 gg) (pr1 xx)).
      exact (disp_rwhisker (pr2 gg) (pr2 xx)).
  Defined.

  (* Needed? *)
  Lemma total_sigma_cell_eq
        {a b : total_bicat E}
        {f g : total_bicat E ⟦a,b⟧}
        (x y : f ==> g)
        (eq1 : pr1 x = pr1 y)
        (eq2 : pr2 x = transportb (λ z, pr2 f ==>[z] pr2 g) eq1 (pr2 y))
    : x = y.
  Proof.
    induction x as (x, xx).
    induction y as (y, yy).
    cbn in *.
    induction eq1.
    cbn in *.
    apply pair_path_in2.
    exact eq2.
  Defined.

  Lemma sigma_prebicat_laws : disp_prebicat_laws sigma_bicat_data.
  Proof.
    repeat split; red; cbn; intros *;
      use (@total2_reassoc_paths'
             (_ ==> _) (fun x' => _ ==>[ x'] _)
             (fun x'xx => _ ==>[ make_total_cell (pr1 x'xx) (pr2 x'xx)] _));
      cbn.
    - apply disp_id2_left.
    - apply (disp_id2_left (pr2 ηη)).
    - apply disp_id2_right.
    - apply (disp_id2_right (pr2 ηη)).
    - apply disp_vassocr.
    - apply (disp_vassocr (pr2 ηη) (pr2 φφ) (pr2 ψψ)).
    - apply disp_lwhisker_id2.
    - apply (disp_lwhisker_id2 (pr2 ff) (pr2 gg)).
    - apply disp_id2_rwhisker.
    - apply (disp_id2_rwhisker (pr2 ff) (pr2 gg)).
    - apply disp_lwhisker_vcomp.
    - apply (disp_lwhisker_vcomp (ff := (pr2 ff)) (pr2 ηη) (pr2 φφ)).
    - apply disp_rwhisker_vcomp.
    - apply (disp_rwhisker_vcomp (ii := pr2 ii) (pr2 ηη) (pr2 φφ)).
    - apply disp_vcomp_lunitor.
    - apply (disp_vcomp_lunitor (pr2 ηη)).
    - apply disp_vcomp_runitor.
    - apply (disp_vcomp_runitor (pr2 ηη)).
    - apply disp_lwhisker_lwhisker.
    - apply (disp_lwhisker_lwhisker (pr2 ff) (pr2 gg) (pr2 ηη)).
    - apply disp_rwhisker_lwhisker.
    - apply (disp_rwhisker_lwhisker (pr2 ff) (pr2 ii) (pr2 ηη)).
    - apply disp_rwhisker_rwhisker.
    - apply (disp_rwhisker_rwhisker _ _ (pr2 hh) (pr2 ii) (pr2 ηη)).
    - apply disp_vcomp_whisker.
    - apply (disp_vcomp_whisker _ _ _ _ _ (pr2 ff) (pr2 gg) (pr2 hh) (pr2 ii) (pr2 ηη) (pr2 φφ)).
    - apply disp_lunitor_linvunitor.
    - apply (disp_lunitor_linvunitor (pr2 ff)).
    - apply disp_linvunitor_lunitor.
    - apply (disp_linvunitor_lunitor (pr2 ff)).
    - apply disp_runitor_rinvunitor.
    - apply (disp_runitor_rinvunitor (pr2 ff)).
    - apply disp_rinvunitor_runitor.
    - apply (disp_rinvunitor_runitor (pr2 ff)).
    - apply disp_lassociator_rassociator.
    - apply (disp_lassociator_rassociator (pr2 ff) (pr2 gg) (pr2 hh)).
    - apply disp_rassociator_lassociator.
    - apply (disp_rassociator_lassociator _ (pr2 ff) (pr2 gg) (pr2 hh)).
    - apply disp_runitor_rwhisker.
    - apply (disp_runitor_rwhisker (pr2 ff) (pr2 gg)).
    - apply disp_lassociator_lassociator.
    - apply (disp_lassociator_lassociator (pr2 ff) (pr2 gg) (pr2 hh) (pr2 ii)).
  Qed.

  Definition sigma_prebicat : disp_prebicat C
    := sigma_bicat_data,, sigma_prebicat_laws.

  Lemma has_disp_cellset_sigma_prebicat
    : has_disp_cellset sigma_prebicat.
  Proof.
    red; cbn; intros.
    apply isaset_total2.
    - apply disp_cellset_property.
    - intros. apply disp_cellset_property.
  Qed.

  Definition sigma_bicat
    : disp_bicat C
    := sigma_prebicat,, has_disp_cellset_sigma_prebicat.

  Definition disp_2cells_isaprop_sigma
             (HD : disp_2cells_isaprop D)
             (HE : disp_2cells_isaprop E)
    : disp_2cells_isaprop sigma_bicat.
  Proof.
    intro; intros.
    apply isaproptotal2.
    - intro; apply HE.
    - intros; apply HD.
  Qed.

End Sigma.

Section SigmaTotalUnivalent.
  Context {C : bicat}
          {D₁ : disp_bicat C}
          (D₂ : disp_bicat (total_bicat D₁)).

  Local Notation E₁ := (total_bicat D₂).
  Local Notation E₂ := (total_bicat (sigma_bicat C D₁ D₂)).

  Definition E₁_univalent_2_0
             (HC_2_0 : is_univalent_2_0 C)
             (HD₁_2_0 : disp_univalent_2_0 D₁)
             (HD₂_2_0 : disp_univalent_2_0 D₂)
    : is_univalent_2_0 E₁.
  Proof.
    apply total_is_univalent_2_0.
    - apply total_is_univalent_2_0.
      + exact HC_2_0.
      + exact HD₁_2_0.
    - exact HD₂_2_0.
  Defined.

  Definition E₁_univalent_2_1
             (HC_2_1 : is_univalent_2_1 C)
             (HD₁_2_1 : disp_univalent_2_1 D₁)
             (HD₂_2_1 : disp_univalent_2_1 D₂)
    : is_univalent_2_1 E₁.
  Proof.
    apply total_is_univalent_2_1.
    - apply total_is_univalent_2_1.
      + exact HC_2_1.
      + exact HD₁_2_1.
    - exact HD₂_2_1.
  Defined.

  Definition E₁_to_E₂ : E₁ → E₂
    := λ x, (pr11 x ,, (pr21 x ,, pr2 x)).

  Definition E₂_to_E₁ : E₂ → E₁
    := λ x, ((pr1 x ,, pr12 x) ,, pr22 x).

  Definition E₂_to_E₁_weq : E₂ ≃ E₁.
  Proof.
    use make_weq.
    - exact E₂_to_E₁.
    - use isweq_iso.
      + exact E₁_to_E₂.
      + apply idpath.
      + apply idpath.
  Defined.

  Definition path_E₂_to_path_E₁_weq
             (x y : E₂)
    : x = y ≃ E₂_to_E₁ x = E₂_to_E₁ y.
  Proof.
    use make_weq.
    - exact (maponpaths E₂_to_E₁).
    - exact (isweqmaponpaths E₂_to_E₁_weq x y).
  Defined.

  Definition mor_E₁_to_E₂
             {x y : E₁}
    : x --> y → E₁_to_E₂ x --> E₁_to_E₂ y
    := λ f, (pr11 f ,, (pr21 f ,, pr2 f)).

  Definition mor_E₂_to_E₁
             {x y : E₂}
    : x --> y → E₂_to_E₁ x --> E₂_to_E₁ y
    := λ f, ((pr1 f ,, pr12 f) ,, pr22 f).

  Definition mor_E₂_to_E₁_weq
             {x y : E₂}
    : x --> y ≃ E₂_to_E₁ x --> E₂_to_E₁ y.
  Proof.
    use make_weq.
    - exact mor_E₂_to_E₁.
    - use isweq_iso.
      + exact mor_E₁_to_E₂.
      + apply idpath.
      + apply idpath.
  Defined.

  Definition path_mor_E₂_to_path_mor_E₁_weq
             {x y : E₂}
             (f g : x --> y)
    : f = g ≃ mor_E₂_to_E₁ f = mor_E₂_to_E₁ g.
  Proof.
    use make_weq.
    - exact (maponpaths mor_E₂_to_E₁).
    - exact (isweqmaponpaths mor_E₂_to_E₁_weq f g).
  Defined.

  Definition cell_E₁_to_E₂
             {x y : E₁}
             {f g : x --> y}
    : f ==> g → mor_E₁_to_E₂ f ==> mor_E₁_to_E₂ g
    := λ α, (pr11 α ,, (pr21 α ,, pr2 α)).

  Definition cell_E₂_to_E₁
             {x y : E₂}
             {f g : x --> y}
    : f ==> g → mor_E₂_to_E₁ f ==> mor_E₂_to_E₁ g
    := λ α, ((pr1 α ,, pr12 α) ,, pr22 α).

  Definition cell_E₁_to_E₂_id₂
             {x y : E₁}
             (f : x --> y)
    : cell_E₁_to_E₂ (id₂ f) = id₂ (mor_E₁_to_E₂ f)
    := idpath _.

  Definition cell_E₂_to_E₁_id₂
             {x y : E₂}
             (f : x --> y)
    : cell_E₂_to_E₁ (id₂ f) = id₂ (mor_E₂_to_E₁ f)
    := idpath _.

  Definition cell_E₁_to_E₂_vcomp
             {x y : E₁}
             {f g h : x --> y}
             (α : f ==> g) (β : g ==> h)
    : cell_E₁_to_E₂ α • cell_E₁_to_E₂ β = cell_E₁_to_E₂ (α • β)
    := idpath _.

  Definition cell_E₂_to_E₁_vcomp
             {x y : E₂}
             {f g h : x --> y}
             (α : f ==> g) (β : g ==> h)
    : cell_E₂_to_E₁ α • cell_E₂_to_E₁ β = cell_E₂_to_E₁ (α • β)
    := idpath _.

  Definition cell_E₁_to_E₂_is_invertible
             {x y : E₁}
             {f g : x --> y}
             (α : f ==> g)
    : is_invertible_2cell α → is_invertible_2cell (cell_E₁_to_E₂ α).
  Proof.
    intros Hα.
    use tpair.
    - exact (cell_E₁_to_E₂ Hα^-1).
    - split.
      + exact ((cell_E₁_to_E₂_vcomp α Hα^-1)
                  @ maponpaths cell_E₁_to_E₂ (pr12 Hα)
                  @ cell_E₁_to_E₂_id₂ _).
      + exact ((cell_E₁_to_E₂_vcomp Hα^-1 α)
                 @ maponpaths cell_E₁_to_E₂ (pr22 Hα)
                 @ cell_E₁_to_E₂_id₂ _).
  Defined.

  Definition cell_E₂_to_E₁_is_invertible
             {x y : E₂}
             {f g : x --> y}
             (α : f ==> g)
    : is_invertible_2cell α → is_invertible_2cell (cell_E₂_to_E₁ α).
  Proof.
    intros Hα.
    use tpair.
    - exact (cell_E₂_to_E₁ Hα^-1).
    - split.
      + exact ((cell_E₂_to_E₁_vcomp α Hα^-1)
                 @ maponpaths cell_E₂_to_E₁ (pr12 Hα)
                 @ cell_E₂_to_E₁_id₂ _).
      + exact ((cell_E₂_to_E₁_vcomp Hα^-1 α)
                 @ maponpaths cell_E₂_to_E₁ (pr22 Hα)
                 @ cell_E₂_to_E₁_id₂ _).
  Defined.

  Definition iso_in_E₂
             {x y : E₂}
             (f g : x --> y)
    : invertible_2cell (mor_E₂_to_E₁ f) (mor_E₂_to_E₁ g) → invertible_2cell f g.
  Proof.
    intros α.
    use tpair.
    - exact (cell_E₁_to_E₂ (cell_from_invertible_2cell α)).
    - use tpair.
      + exact (cell_E₁_to_E₂ α^-1).
      + split.
        * exact ((cell_E₁_to_E₂_vcomp α α^-1)
                   @ maponpaths cell_E₁_to_E₂ (pr122 α)
                   @ cell_E₁_to_E₂_id₂ (mor_E₂_to_E₁ f)).
        * exact ((cell_E₁_to_E₂_vcomp α^-1 α)
                   @ maponpaths cell_E₁_to_E₂ (pr222 α)
                   @ cell_E₁_to_E₂_id₂ (mor_E₂_to_E₁ g)).
  Defined.

  Definition iso_in_E₂_inv
             {x y : E₂}
             (f g : x --> y)
    : invertible_2cell f g → invertible_2cell (mor_E₂_to_E₁ f) (mor_E₂_to_E₁ g).
  Proof.
    intros α.
    use tpair.
    - exact (cell_E₂_to_E₁ (cell_from_invertible_2cell α)).
    - use tpair.
      + exact (cell_E₂_to_E₁ α^-1).
      + split.
        * exact ((cell_E₂_to_E₁_vcomp α α^-1)
                   @ maponpaths cell_E₂_to_E₁ (pr122 α)
                   @ cell_E₂_to_E₁_id₂ _).
        * exact ((cell_E₂_to_E₁_vcomp α^-1 α)
                   @ maponpaths cell_E₂_to_E₁ (pr222 α)
                   @ cell_E₂_to_E₁_id₂ _).
  Defined.

  Definition iso_in_E₂_weq
             {x y : E₂}
             (f g : x --> y)
    : invertible_2cell (mor_E₂_to_E₁ f) (mor_E₂_to_E₁ g) ≃ invertible_2cell f g.
  Proof.
    use make_weq.
    - exact (iso_in_E₂ f g).
    - use isweq_iso.
      + exact (iso_in_E₂_inv f g).
      + intros α.
        use subtypePath.
        { intro ; apply isaprop_is_invertible_2cell. }
        apply idpath.
      + intros α.
        use subtypePath.
        { intro ; apply isaprop_is_invertible_2cell. }
        apply idpath.
  Defined.

  Definition idtoiso_2_1_alt_E₂
             {x y : E₂}
             (f g : x --> y)
             (HC_2_1 : is_univalent_2_1 C)
             (HD₁_2_1 : disp_univalent_2_1 D₁)
             (HD₂_2_1 : disp_univalent_2_1 D₂)
    : f = g ≃ invertible_2cell f g.
  Proof.
    refine ((iso_in_E₂_weq f g)
              ∘ (idtoiso_2_1 _ _ ,, _)
              ∘ path_mor_E₂_to_path_mor_E₁_weq f g)%weq.
    apply E₁_univalent_2_1; assumption.
  Defined.

  Definition sigma_is_univalent_2_1
             (HC_2_1 : is_univalent_2_1 C)
             (HD₁_2_1 : disp_univalent_2_1 D₁)
             (HD₂_2_1 : disp_univalent_2_1 D₂)
    : is_univalent_2_1 E₂.
  Proof.
    intros x y f g.
    use weqhomot.
    - exact (idtoiso_2_1_alt_E₂ f g HC_2_1 HD₁_2_1 HD₂_2_1).
    - intros p.
      induction p ; cbn.
      use subtypePath.
      {
        intro.
        apply (@isaprop_is_invertible_2cell (total_bicat (sigma_bicat C D₁ D₂))).
      }
      apply idpath.
  Defined.

  Definition adjequiv_in_E₂
             (x y : E₂)
    : adjoint_equivalence (E₂_to_E₁ x) (E₂_to_E₁ y) → adjoint_equivalence x y.
  Proof.
    intros l.
    use equiv_to_adjequiv.
    - exact (mor_E₁_to_E₂ l).
    - use tpair.
      + use tpair.
        * exact (mor_E₁_to_E₂ (left_adjoint_right_adjoint l)).
        * split.
          ** exact (cell_E₁_to_E₂ (left_adjoint_unit l)).
          ** exact (cell_E₁_to_E₂ (left_adjoint_counit l)).
      + split.
        * exact (cell_E₁_to_E₂_is_invertible _ (left_equivalence_unit_iso l)).
        * exact (cell_E₁_to_E₂_is_invertible _ (left_equivalence_counit_iso l)).
  Defined.

  Definition adjequiv_in_E₂_inv
             (x y : E₂)
    : adjoint_equivalence x y → adjoint_equivalence (E₂_to_E₁ x) (E₂_to_E₁ y).
  Proof.
    intros l.
    use equiv_to_adjequiv.
    - exact (mor_E₂_to_E₁ l).
    - use tpair.
      + use tpair.
        * exact (mor_E₂_to_E₁ (left_adjoint_right_adjoint l)).
        * split.
          ** exact (cell_E₂_to_E₁ (left_adjoint_unit l)).
          ** exact (cell_E₂_to_E₁ (left_adjoint_counit l)).
      + split.
        * exact (cell_E₂_to_E₁_is_invertible _ (left_equivalence_unit_iso l)).
        * exact (cell_E₂_to_E₁_is_invertible _ (left_equivalence_counit_iso l)).
  Defined.

  Definition adjequiv_in_E₂_weq
             (x y : E₂)
             (HC_2_1 : is_univalent_2_1 C)
             (HD₁_2_1 : disp_univalent_2_1 D₁)
             (HD₂_2_1 : disp_univalent_2_1 D₂)
    : adjoint_equivalence (E₂_to_E₁ x) (E₂_to_E₁ y) ≃ adjoint_equivalence x y.
  Proof.
    use make_weq.
    - exact (adjequiv_in_E₂ x y).
    - use isweq_iso.
      + exact (adjequiv_in_E₂_inv x y).
      + intros l.
        use subtypePath.
        {
          intro.
          apply isaprop_left_adjoint_equivalence.
          apply E₁_univalent_2_1; assumption.
        }
        apply idpath.
      + intros l.
        use subtypePath.
        {
          intro.
          apply isaprop_left_adjoint_equivalence.
          apply sigma_is_univalent_2_1; assumption.
        }
        apply idpath.
  Defined.

  Definition idtoiso_2_0_alt_E₂
             (x y : E₂)
             (HC : is_univalent_2 C)
             (HD₁ : disp_univalent_2 D₁)
             (HD₂ : disp_univalent_2 D₂)
    : x = y ≃ adjoint_equivalence x y.
  Proof.
    refine ((adjequiv_in_E₂_weq x y (pr2 HC) (pr2 HD₁) (pr2 HD₂))
              ∘ (idtoiso_2_0 _ _ ,, _)
              ∘ path_E₂_to_path_E₁_weq x y)%weq.
    apply E₁_univalent_2_0.
    - exact (pr1 HC).
    - exact (pr1 HD₁).
    - exact (pr1 HD₂).
  Defined.

  Definition sigma_is_univalent_2_0
             (HC : is_univalent_2 C)
             (HD₁ : disp_univalent_2 D₁)
             (HD₂ : disp_univalent_2 D₂)
    : is_univalent_2_0 E₂.
  Proof.
    intros x y.
    use weqhomot.
    - exact (idtoiso_2_0_alt_E₂ x y HC HD₁ HD₂).
    - intros p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_left_adjoint_equivalence.
        apply sigma_is_univalent_2_1.
        - exact (pr2 HC).
        - exact (pr2 HD₁).
        - exact (pr2 HD₂).
      }
      reflexivity.
  Defined.

  Definition sigma_is_univalent_2
             (HC : is_univalent_2 C)
             (HD₁ : disp_univalent_2 D₁)
             (HD₂ : disp_univalent_2 D₂)
    : is_univalent_2 E₂.
  Proof.
    split.
    - apply sigma_is_univalent_2_0; assumption.
    - apply sigma_is_univalent_2_1.
      * exact (pr2 HC).
      * exact (pr2 HD₁).
      * exact (pr2 HD₂).
  Defined.
End SigmaTotalUnivalent.

Definition help_disp_left_adjoint_axioms
           {C : bicat}
           (D : disp_bicat C)
           (HD : disp_2cells_isaprop D)
           {x y : C}
           {f : x --> y}
           (Af : left_adjoint f)
           {xx : D x} {yy : D y}
           {ff : xx -->[ f ] yy}
           {Aff : disp_left_adjoint_data Af ff}
  : disp_left_adjoint_axioms Af Aff.
Proof.
  split ; apply HD.
Qed.

Definition transportf_subtypePath
            {A : UU}
            {P : A → UU}
            (Pprop : ∏ (a : A), isaprop (P a))
            {C : total2 P → UU}
            (x : A) (P₁ P₂ : P x)
            (y : C (x,,P₂))
  : transportf
      (λ (z : total2 P), C z)
      (!(@subtypePath A P Pprop (x ,, P₁) (x ,, P₂) (idpath x)))
      y
    =
    transportf
      (λ (p : P x), C (x,, p))
      (!(pr1 (Pprop x P₁ P₂)))
      y.
Proof.
  cbn.
  induction (Pprop x P₁ P₂) as [p q].
  induction p.
  apply idpath.
Defined.

Section SigmaDisplayedUnivalent.
  Context {C : bicat}
          {D₁ : disp_bicat C}
          (D₂ : disp_bicat (total_bicat D₁)).

  Variable (HC : is_univalent_2 C)
           (HD₁ : disp_2cells_isaprop D₁)
           (HD₂ : disp_2cells_isaprop D₂)
           (HD₁_2_1 : disp_univalent_2_1 D₁)
           (HD₂_2_1 : disp_univalent_2_1 D₂).

  Definition pair_disp_invertible_to_sigma_disp_invertible
             {x y : C}
             {f : C ⟦ x, y ⟧}
             {xx : (sigma_bicat C D₁ D₂) x}
             {yy : (sigma_bicat C D₁ D₂) y}
             {ff1 : pr1 xx -->[ f] pr1 yy}
             (ff2 : pr2 xx -->[ f,, ff1] pr2 yy)
             {gg1 : pr1 xx -->[ f] pr1 yy}
             (gg2 : pr2 xx -->[ f,, gg1] pr2 yy)
    : (∑ (p : disp_invertible_2cell
                (id2_invertible_2cell f)
                ff1 gg1),
       disp_invertible_2cell
         (iso_in_E_weq _ _ (id2_invertible_2cell f ,, p))
         ff2 gg2)
      →
      @disp_invertible_2cell
        C (sigma_prebicat C D₁ D₂) _ _ _ _ _ _
        (id2_invertible_2cell f) (ff1,, ff2) (gg1,, gg2).
  Proof.
    intros p.
    use tpair.
    - exact (pr11 p ,, pr12 p).
    - simpl.
      simple refine (_ ,, (_ ,, _)).
      + exact (disp_inv_cell (pr1 p) ,, disp_inv_cell (pr2 p)).
      + apply disp_2cells_isaprop_sigma ; assumption.
      + apply disp_2cells_isaprop_sigma ; assumption.
  Defined.

  Definition disp_locally_groupoid_sigma
             (LG₁ : disp_locally_groupoid D₁)
             (LG₂ : disp_locally_groupoid D₂)
    : disp_locally_groupoid (sigma_bicat C D₁ D₂).
  Proof.
    use make_disp_locally_groupoid_univalent_2_1.
    - intros a b f aa bb ff gg xx.
      pose (p₁ := pr1 xx ,, LG₁ _ _ _ _ _ _ _ _ _ (pr1 xx) : disp_invertible_2cell _ _ _).
      pose (pr2 xx) as m.
      cbn in m.
      pose (p₂ := pr2 xx ,, LG₂
                      (a ,, pr1 aa) (b ,, pr1 bb)
                      (f ,, pr1 ff) (f ,, pr1 gg)
                      (iso_in_E_weq _ _ (id2_invertible_2cell f ,, p₁))
                      (pr2 aa) (pr2 bb)
                      (pr2 ff) (pr2 gg) m).
      exact (pr2 (pair_disp_invertible_to_sigma_disp_invertible _ _ (p₁ ,, p₂))).
    - exact (pr2 HC).
  Defined.

  Definition sigma_disp_invertible_to_pair_disp_invertible
             {x y : C}
             {f : C ⟦ x, y ⟧}
             {xx : (sigma_bicat C D₁ D₂) x}
             {yy : (sigma_bicat C D₁ D₂) y}
             {ff1 : pr1 xx -->[ f] pr1 yy}
             (ff2 : pr2 xx -->[ f,, ff1] pr2 yy)
             {gg1 : pr1 xx -->[ f] pr1 yy}
             (gg2 : pr2 xx -->[ f,, gg1] pr2 yy)
    : @disp_invertible_2cell
        C (sigma_prebicat C D₁ D₂) _ _ _ _ _ _
        (id2_invertible_2cell f) (ff1,, ff2) (gg1,, gg2)
      →
      (∑ (p : disp_invertible_2cell
                (id2_invertible_2cell f)
                ff1 gg1),
       disp_invertible_2cell
         (iso_in_E_weq _ _ (id2_invertible_2cell f ,, p))
         ff2 gg2).
  Proof.
    intros p.
    use tpair.
    - use tpair.
      + exact (pr11 p).
      + simple refine (_ ,, (_ ,, _)).
        * exact (pr1 (disp_inv_cell p)).
        * apply HD₁.
        * apply HD₁.
    - use tpair.
      + exact (pr21 p).
      + simple refine (_ ,, (_ ,, _)).
        * exact (pr2 (disp_inv_cell p)).
        * apply HD₂.
        * apply HD₂.
  Defined.

  Definition pair_disp_invertible_to_sigma_disp_invertible_weq
             {x y : C}
             {f : C ⟦ x, y ⟧}
             {xx : (sigma_bicat C D₁ D₂) x}
             {yy : (sigma_bicat C D₁ D₂) y}
             {ff1 : pr1 xx -->[ f] pr1 yy}
             (ff2 : pr2 xx -->[ f,, ff1] pr2 yy)
             {gg1 : pr1 xx -->[ f] pr1 yy}
             (gg2 : pr2 xx -->[ f,, gg1] pr2 yy)
    : (∑ (p : disp_invertible_2cell
                (id2_invertible_2cell f)
                ff1 gg1),
       disp_invertible_2cell
         (iso_in_E_weq _ _ (id2_invertible_2cell f ,, p))
         ff2 gg2)
        ≃ @disp_invertible_2cell
        C (sigma_prebicat C D₁ D₂) _ _ _ _ _ _
        (id2_invertible_2cell f) (ff1,, ff2) (gg1,, gg2).
  Proof.
    use make_weq.
    - apply pair_disp_invertible_to_sigma_disp_invertible.
    - use isweq_iso.
      + apply sigma_disp_invertible_to_pair_disp_invertible.
      + intro p.
        induction p as [p1 p2].
        use total2_paths_b.
        * use subtypePath.
          { intro ; apply isaprop_is_disp_invertible_2cell. }
          apply idpath.
        * use subtypePath.
          { intro ; apply isaprop_is_disp_invertible_2cell. }
          apply HD₂.
      + intro p.
        use subtypePath.
        { intro
          ; apply (@isaprop_is_disp_invertible_2cell C (sigma_bicat C D₁ D₂)). }
        apply idpath.
  Defined.

  Definition sigma_disp_univalent_2_1_with_props
    : disp_univalent_2_1 (sigma_bicat _ _ D₂).
  Proof.
    apply fiberwise_local_univalent_is_univalent_2_1.
    intros x y f xx yy ff gg.
    use weqhomot.
    - cbn.
      refine (_ ∘ total2_paths_equiv _ _ _)%weq.
      refine (pair_disp_invertible_to_sigma_disp_invertible_weq _ _ ∘ _)%weq.
      induction ff as [ff1 ff2] ; induction gg as [gg1 gg2].
      refine (weqtotal2
                (make_weq
                   _
                   (HD₁_2_1 _ _ _ _ (idpath _) _ _ ff1 gg1))
                _).
      intro p ; cbn in p.
      induction p.
      exact (make_weq
               _
               (HD₂_2_1 _ _ _ _ (idpath _) _ _ ff2 gg2)).
    - intros p.
      cbn in p.
      induction p.
      use subtypePath.
      { intro ; apply isaprop_is_disp_invertible_2cell. }
      apply idpath.
  Defined.

  Opaque adjoint_equivalence_total_disp_weq.

  Variable (LG₁ : disp_locally_groupoid D₁)
           (LG₂ : disp_locally_groupoid D₂).

  Definition pair_disp_adjequiv_to_sigma_disp_adjequiv
             {x : C}
             (xx : (sigma_bicat C D₁ D₂) x)
             (yy : (sigma_bicat C D₁ D₂) x)
    : (∑ (p : disp_adjoint_equivalence
                (internal_adjoint_equivalence_identity x)
                (pr1 xx) (pr1 yy)),
       disp_adjoint_equivalence
         (invmap (adjoint_equivalence_total_disp_weq (pr1 xx) (pr1 yy))
                 (internal_adjoint_equivalence_identity x ,, p))
         (pr2 xx) (pr2 yy))
      →
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy.
  Proof.
    intros p.
    simple refine (_ ,, ((_ ,, (_ ,, _)) ,, _ ,, (_ ,, _))).
    - exact (pr11 p ,, pr12 p).
    - exact (pr112 (pr1 p) ,, pr112 (pr2 p)).
    - exact (pr1 (pr212 (pr1 p)) ,, pr1 (pr212 (pr2 p))).
    - exact (pr2 (pr212 (pr1 p)) ,, pr2 (pr212 (pr2 p))).
    - apply help_disp_left_adjoint_axioms.
      apply disp_2cells_isaprop_sigma ; assumption.
    - apply disp_locally_groupoid_sigma ; assumption.
    - apply disp_locally_groupoid_sigma ; assumption.
  Defined.

  Definition pair_disp_left_adjoint_equivalence_sigma
             {x : C}
             {xx : (sigma_bicat C D₁ D₂) x}
             {yy : (sigma_bicat C D₁ D₂) x}
             {ff : xx -->[ identity _ ] yy}
             (Hff₁ : disp_left_adjoint_equivalence
                       (internal_adjoint_equivalence_identity x)
                       (pr1 ff))
             (Hff₂ : disp_left_adjoint_equivalence
                       (invmap
                          (adjoint_equivalence_total_disp_weq
                             (pr1 xx) (pr1 yy))
                          (internal_adjoint_equivalence_identity x ,, pr1 ff ,, Hff₁))
                       (pr2 ff))
    : disp_left_adjoint_equivalence
        (internal_adjoint_equivalence_identity x)
        ff.
  Proof.
    exact (pair_disp_adjequiv_to_sigma_disp_adjequiv
             xx yy
             ((pr1 ff ,, Hff₁)
               ,,
               (pr2 ff ,, Hff₂))).
  Defined.

  Definition pair_disp_adjequiv_to_sigma_disp_adjequiv_inv_pr1
             {x : C}
             (xx : (sigma_bicat C D₁ D₂) x)
             (yy : (sigma_bicat C D₁ D₂) x)
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy
      →
      disp_adjoint_equivalence
        (internal_adjoint_equivalence_identity x)
        (pr1 xx) (pr1 yy).
  Proof.
    intro p.
    simple refine (pr11 p ,, ((_ ,, (_ ,, _)) ,, _ ,, (_ ,, _))).
    - exact (pr1 (pr112 p)).
    - exact (pr11 (pr212 p)).
    - exact (pr12 (pr212 p)).
    - apply help_disp_left_adjoint_axioms.
      exact HD₁.
    - apply LG₁.
    - apply LG₁.
  Defined.

  Definition pair_disp_adjequiv_to_sigma_disp_adjequiv_inv_pr2
             {x : C}
             (xx : (sigma_bicat C D₁ D₂) x)
             (yy : (sigma_bicat C D₁ D₂) x)
    : ∏ (p : disp_adjoint_equivalence
               (internal_adjoint_equivalence_identity x) xx yy),
      disp_adjoint_equivalence
        (invmap
           (adjoint_equivalence_total_disp_weq (pr1 xx) (pr1 yy))
           (internal_adjoint_equivalence_identity
              x,,
              pair_disp_adjequiv_to_sigma_disp_adjequiv_inv_pr1 xx yy p))
        (pr2 xx) (pr2 yy).
  Proof.
    intro p.
    simple refine (pr21 p ,,
                        ((pr2 (pr112 p) ,, (pr21 (pr212 p) ,, pr22 (pr212 p)))
                           ,, _ ,, (_ ,, _))).
    - apply help_disp_left_adjoint_axioms.
      exact HD₂.
    - apply LG₂.
    - apply LG₂.
  Defined.

  Definition pair_disp_adjequiv_to_sigma_disp_adjequiv_inv
             {x : C}
             (xx : (sigma_bicat C D₁ D₂) x)
             (yy : (sigma_bicat C D₁ D₂) x)
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy
      →
      (∑ (p : disp_adjoint_equivalence
                (internal_adjoint_equivalence_identity x)
                (pr1 xx) (pr1 yy)),
       disp_adjoint_equivalence
         (invmap (adjoint_equivalence_total_disp_weq (pr1 xx) (pr1 yy))
                 (internal_adjoint_equivalence_identity x ,, p))
         (pr2 xx) (pr2 yy)).
  Proof.
    intros p.
    simple refine (_ ,, _).
    - exact (pair_disp_adjequiv_to_sigma_disp_adjequiv_inv_pr1 xx yy p).
    - exact (pair_disp_adjequiv_to_sigma_disp_adjequiv_inv_pr2 xx yy p).
  Defined.

  Definition pair_disp_adjequiv_to_sigma_disp_adjequiv_weq_help
             {x : C}
             (xx : (sigma_bicat C D₁ D₂) x)
             (yy : (sigma_bicat C D₁ D₂) x)
    : homot
        ((pair_disp_adjequiv_to_sigma_disp_adjequiv_inv xx yy)
           ∘ pair_disp_adjequiv_to_sigma_disp_adjequiv xx yy)%functions
        (idfun _).
  Proof.
    intro p.
    induction p as [p1 p2].
    use total2_paths_b.
    - use subtypePath.
      {
        intro.
        apply isaprop_disp_left_adjoint_equivalence
        ; [ exact (pr2 HC) | exact HD₁_2_1 ].
      }
      apply idpath.
    - use subtypePath.
      {
        intro.
        apply isaprop_disp_left_adjoint_equivalence
        ; [ apply total_is_univalent_2_1 ; [ exact (pr2 HC) | exact HD₁_2_1 ]
          | exact HD₂_2_1 ].
      }
      unfold transportb.
      refine (!(_ @ _)).
      {
        apply (@pr1_transportf
                 _
                 (λ z : disp_adjoint_equivalence
                          (internal_adjoint_equivalence_identity x)
                          (pr1 xx) (pr1 yy),
                        pr2 xx
                            -->[invmap (adjoint_equivalence_total_disp_weq (pr1 xx) (pr1 yy))
                                       (internal_adjoint_equivalence_identity x,, z)]
                            pr2 yy)).
      }
      etrans.
      {
        exact (@transportf_subtypePath
                (pr1 xx -->[ internal_adjoint_equivalence_identity x ] pr1 yy)
                (λ z, disp_left_adjoint_equivalence
                        (internal_adjoint_equivalence_identity x) z)
                (λ z, isaprop_disp_left_adjoint_equivalence
                        (internal_adjoint_equivalence_identity x) z
                        (pr2 HC) HD₁_2_1)
                (λ z, pr2 xx
                          -->[ invmap (adjoint_equivalence_total_disp_weq
                                         (pr1 xx) (pr1 yy))
                                      (internal_adjoint_equivalence_identity x,, z)
                             ]
                          pr2 yy)
                (pr1 p1)
                (pr1 (pair_disp_adjequiv_to_sigma_disp_adjequiv_inv
                        xx yy
                        (pair_disp_adjequiv_to_sigma_disp_adjequiv xx yy (p1,, p2))))
                (pr2 p1)
                (pr1 p2)).
      }
      match goal with
      | [ |- transportf _?p _ = _ ] => induction p
      end.
      apply idpath.
  Qed.

  Definition pair_disp_adjequiv_to_sigma_disp_adjequiv_weq
             {x : C}
             (xx : (sigma_bicat C D₁ D₂) x)
             (yy : (sigma_bicat C D₁ D₂) x)
    : (∑ (p : disp_adjoint_equivalence
                (internal_adjoint_equivalence_identity x)
                (pr1 xx) (pr1 yy)),
       disp_adjoint_equivalence
         (invmap (adjoint_equivalence_total_disp_weq (pr1 xx) (pr1 yy))
                 (internal_adjoint_equivalence_identity x ,, p))
         (pr2 xx) (pr2 yy))
      ≃
      disp_adjoint_equivalence (internal_adjoint_equivalence_identity x) xx yy.
  Proof.
    use make_weq.
    - exact (pair_disp_adjequiv_to_sigma_disp_adjequiv xx yy).
    - use isweq_iso.
      + exact (pair_disp_adjequiv_to_sigma_disp_adjequiv_inv xx yy).
      + exact (pair_disp_adjequiv_to_sigma_disp_adjequiv_weq_help xx yy).
      + intros p.
        use subtypePath.
        { intro ; apply isaprop_disp_left_adjoint_equivalence
          ; [ exact (pr2 HC) | exact sigma_disp_univalent_2_1_with_props ].
        }
        apply idpath.
  Defined.

  Definition disp_adjequiv_sigma_help
             (x : C)
             (xx1 : D₁ x)
             (xx2 yy2 : D₂ (x,, xx1))
    : disp_adjoint_equivalence
        (@internal_adjoint_equivalence_identity (total_bicat D₁) (x,, xx1))
        xx2 yy2
      →
      disp_adjoint_equivalence
        (invmap (adjoint_equivalence_total_disp_weq xx1 xx1)
                ((internal_adjoint_equivalence_identity x)
                   ,,disp_identity_adjoint_equivalence xx1)) xx2
        yy2.
  Proof.
    intros p.
    simple refine (pr1 p ,, ((pr112 p ,,
                                    (pr1 (pr212 p) ,, pr2 (pr212 p)))
                               ,, _ ,, (_ ,, _))).
    - abstract
        (apply help_disp_left_adjoint_axioms ;
         apply HD₂).
    - abstract (apply LG₂).
    - abstract (apply LG₂).
  Defined.

  Definition disp_adjequiv_sigma_help_inv
             (x : C)
             (xx1 : D₁ x)
             (xx2 yy2 : D₂ (x,, xx1))
    : disp_adjoint_equivalence
        (invmap (adjoint_equivalence_total_disp_weq xx1 xx1)
                ((internal_adjoint_equivalence_identity x)
                   ,,disp_identity_adjoint_equivalence xx1)) xx2
        yy2
      →
      disp_adjoint_equivalence
        (@internal_adjoint_equivalence_identity (total_bicat D₁) (x,, xx1))
        xx2 yy2.
  Proof.
    intros p.
    simple refine (pr1 p ,, ((pr112 p ,,
                                    (pr1 (pr212 p) ,, pr2 (pr212 p)))
                               ,, _ ,, (_ ,, _))).
    - abstract
        (apply help_disp_left_adjoint_axioms ;
         apply HD₂).
    - abstract (apply LG₂).
    - abstract (apply LG₂).
  Defined.

  Definition disp_adjequiv_sigma_help_weq
             (x : C)
             (xx1 : D₁ x)
             (xx2 yy2 : D₂ (x,, xx1))
    : disp_adjoint_equivalence
        (@internal_adjoint_equivalence_identity (total_bicat D₁) (x,, xx1))
        xx2 yy2
      ≃
      disp_adjoint_equivalence
        (invmap (adjoint_equivalence_total_disp_weq xx1 xx1)
                ((internal_adjoint_equivalence_identity x)
                   ,,disp_identity_adjoint_equivalence xx1)) xx2
        yy2.
  Proof.
    use make_weq.
    - exact (disp_adjequiv_sigma_help x xx1 xx2 yy2).
    - use isweq_iso.
      + exact (disp_adjequiv_sigma_help_inv x xx1 xx2 yy2).
      + intros p.
        use subtypePath.
        { intro ; apply isaprop_disp_left_adjoint_equivalence.
          + apply total_is_univalent_2_1.
            * exact (pr2 HC).
            * exact HD₁_2_1.
          + exact HD₂_2_1.
        }
        apply idpath.
      + intros p.
        use subtypePath.
        { intro ; apply isaprop_disp_left_adjoint_equivalence.
          + apply total_is_univalent_2_1.
            * exact (pr2 HC).
            * exact HD₁_2_1.
          + exact HD₂_2_1.
        }
        apply idpath.
  Defined.

  Definition sigma_idtoiso_2_0_alt
             (HD₁_2_0 : disp_univalent_2_0 D₁)
             (HD₂_2_0 : disp_univalent_2_0 D₂)
             {x : C}
             (xx yy : (sigma_bicat C D₁ D₂) x)
    : xx = yy ≃ disp_adjoint_equivalence (idtoiso_2_0 x x (idpath x)) xx yy.
  Proof.
    refine (_ ∘ total2_paths_equiv _ _ _)%weq.
    refine (pair_disp_adjequiv_to_sigma_disp_adjequiv_weq xx yy ∘ _)%weq.
    refine (weqtotal2
              (make_weq
                 _
                 (HD₁_2_0 x x (idpath _) (pr1 xx) (pr1 yy)))
              _)%weq.
    induction xx as [xx1 xx2].
    induction yy as [yy1 yy2].
    intro p ; cbn in p.
    induction p.
    unfold transportf ; simpl.
    refine (_ ∘ make_weq
              _
              (HD₂_2_0 _ _ (idpath (x ,, xx1)) xx2 yy2))%weq.
    exact (disp_adjequiv_sigma_help_weq x xx1 xx2 yy2).
  Defined.

  Definition sigma_disp_univalent_2_0_with_props
             (HD₁_2_0 : disp_univalent_2_0 D₁)
             (HD₂_2_0 : disp_univalent_2_0 D₂)
    : disp_univalent_2_0 (sigma_bicat _ _ D₂).
  Proof.
    apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros x xx yy.
    use weqhomot.
    - exact (sigma_idtoiso_2_0_alt HD₁_2_0 HD₂_2_0 xx yy).
    - intros p.
      cbn in p.
      induction p.
      use subtypePath.
      { intro ; apply isaprop_disp_left_adjoint_equivalence.
        + exact (pr2 HC).
        + apply sigma_disp_univalent_2_1_with_props ; assumption.
      }
      apply idpath.
  Defined.

  Definition sigma_disp_univalent_2_with_props
             (HD₁_2 : disp_univalent_2 D₁)
             (HD₂_2 : disp_univalent_2 D₂)
    : disp_univalent_2 (sigma_bicat _ _ D₂).
  Proof.
    split.
    - apply sigma_disp_univalent_2_0_with_props.
      + apply HD₁_2.
      + apply HD₂_2.
    - apply sigma_disp_univalent_2_1_with_props.
  Defined.
End SigmaDisplayedUnivalent.

Lemma disp_2cells_of_sigma_iscontr
  {B : bicat} {D : disp_bicat B} {E : disp_bicat (total_bicat D)}
  (D_contr : disp_2cells_iscontr D) (E_contr : disp_2cells_iscontr E)
  : disp_2cells_iscontr (sigma_bicat _ _ E).
Proof.
  intro ; intros.
  use iscontraprop1.
  - apply isaproptotal2.
    { intro ; apply isapropifcontr, E_contr. }
    intro ; intros.
    use proofirrelevance.
    apply isapropifcontr.
    apply D_contr.
  - use tpair.
    + apply D_contr.
    + apply E_contr.
Qed.
