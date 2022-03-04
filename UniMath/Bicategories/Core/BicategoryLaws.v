Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Local Open Scope bicategory_scope.
Local Open Scope cat.

Section laws.
  Context {C : bicat}.

  Lemma triangle_r
             {X Y Z : C}
             (g : C⟦Y,Z⟧)
             (f : C⟦X,Y⟧)
    : lunitor g ⋆⋆ id₂ f = lassociator f (id₁ Y) g • (id₂ g ⋆⋆ runitor f).
  Proof.
    cbn.
    apply pathsinv0.
    unfold hcomp.
    etrans.
    { apply maponpaths.
      etrans. { apply maponpaths.
                apply lwhisker_id2. }
              apply id2_right. }
    etrans. apply runitor_rwhisker.
    apply pathsinv0.
    etrans. { apply maponpaths_2. apply id2_rwhisker. }
            apply id2_left.
  Qed.

  Lemma interchange
             {X Y Z : C}
             {f₁ g₁ h₁ : C⟦Y,Z⟧}
             {f₂ g₂ h₂ : C⟦X,Y⟧}
             (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
             (ε₁ : g₁ ==> h₁) (ε₂ : g₂ ==> h₂)
    : (η₁ • ε₁) ⋆⋆ (η₂ • ε₂) = (η₁ ⋆⋆ η₂) • (ε₁ ⋆⋆ ε₂).
  Proof.
    apply hcomp_vcomp.
  Qed.

  Lemma rinvunitor_natural
             {X Y : C}
             {f g : C⟦X, Y⟧}
             (η : f ==> g)
    :  η • rinvunitor g =  rinvunitor f • (id₂ (id₁ Y) ⋆⋆ η).
  Proof.
    use (vcomp_rcancel (runitor _ )).
    { apply is_invertible_2cell_runitor. }
    rewrite vassocl.
    rewrite rinvunitor_runitor.
    use (vcomp_lcancel (runitor _ )).
    { apply is_invertible_2cell_runitor. }
    repeat rewrite vassocr.
    rewrite runitor_rinvunitor.
    rewrite id2_left, id2_right.
    apply (! runitor_natural _ _ _ _ _ ).
  Qed.

  Lemma linvunitor_natural
             {X Y : C}
             {f g : C⟦X, Y⟧}
             (η : f ==> g)
    :  η • linvunitor g = linvunitor f • (η ⋆⋆ id₂ (id₁ X)).
  Proof.
    use (vcomp_rcancel (lunitor _ )).
    { apply is_invertible_2cell_lunitor. }
    rewrite vassocl.
    rewrite linvunitor_lunitor.
    use (vcomp_lcancel (lunitor _ )).
    { apply is_invertible_2cell_lunitor. }
    repeat rewrite vassocr.
    rewrite lunitor_linvunitor.
    rewrite id2_left, id2_right.
    apply (! lunitor_natural _ _ _ _ _ ).
  Qed.

  Lemma lwhisker_hcomp
             {X Y Z : C}
             {f g : C⟦Y,Z⟧}
             (h : C⟦X, Y⟧)
             (α : f ==> g)
    : h ◃ α = id₂ h ⋆ α.
  Proof.
    apply pathsinv0. apply hcomp_identity_left.
  Qed.

  Lemma rwhisker_hcomp
             {X Y Z : C}
             {f g : C⟦X,Y⟧}
             (h : C⟦Y,Z⟧)
             (α : f ==> g)
    : α ▹ h = α ⋆ id₂ h.
  Proof.
    apply pathsinv0. apply hcomp_identity_right.
  Qed.

  Lemma inverse_pentagon
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    :  rassociator (g ∘ f) h k • rassociator f g (k ∘ h)
      =
      (rassociator f g h ⋆ id₂ k) • ((rassociator f (h ∘ g) k) • (id₂ f ⋆ rassociator g h k)).
  Proof.
    use inv_cell_eq.
    - is_iso.
    - is_iso.
    - cbn. rewrite <- !vassocr. apply pentagon.
  Qed.

  Lemma inverse_pentagon_2
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : (lassociator f g h ⋆ id2 k) • rassociator (g ∘ f) h k
      =
       rassociator f (h ∘ g) k • ((f ◃ rassociator g h k) • lassociator f g (k ∘ h)).
  Proof.
    rewrite <- !inverse_of_assoc.
    use vcomp_move_R_Mp.
    {
      is_iso.
    }
    rewrite <- vassocr.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    rewrite <- vassocr.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    symmetry.
    pose (pentagon k h g f) as p.
    unfold hcomp in p.
    rewrite id2_rwhisker in p.
    rewrite id2_left in p.
    exact p.
  Qed.

  Lemma inverse_pentagon_3
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : (id₂ k ⋆⋆ lassociator f g h) • (rassociator (g ∘ f) h k • rassociator f g (k ∘ h))
      =
      rassociator f (h ∘ g) k • rassociator g h k ⋆⋆ id₂ f.
  Proof.
    use vcomp_move_R_pM.
    {
      is_iso.
    }
    cbn.
    apply inverse_pentagon.
  Qed.

  Lemma inverse_pentagon_4
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : rassociator f g (k ∘ h) • (lassociator g h k ⋆⋆ id₂ f)
      =
      lassociator (g ∘ f) h k • ((id₂ k ⋆⋆ rassociator f g h) • rassociator f (h ∘ g) k).
  Proof.
    rewrite <- !inverse_of_assoc.
    use vcomp_move_R_pM.
    {
      is_iso.
    }
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vassocr.
    symmetry ; apply pentagon.
  Qed.

  Lemma inverse_pentagon_5
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : (rassociator g h k ⋆⋆ id₂ f) • lassociator f g (k ∘ h)
      =
      lassociator f (h ∘ g) k • ((id₂ k ⋆⋆ lassociator f g h) • rassociator (g ∘ f) h k).
  Proof.
    rewrite <- !inverse_of_assoc.
    use vcomp_move_R_pM.
    {
      is_iso.
    }
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vassocr.
    apply pentagon.
  Qed.

  Lemma inverse_pentagon_6
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : (id₂ k ⋆⋆ rassociator f g h) • rassociator f (h ∘ g) k
      =
      rassociator (g ∘ f) h k • (rassociator f g (k ∘ h) • (lassociator g h k ⋆⋆ id₂ f)).
  Proof.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    cbn.
    symmetry.
    rewrite <- !vassocr.
    apply inverse_pentagon.
  Qed.

  Lemma pentagon_2
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : lassociator g h k ⋆⋆ id₂ f • lassociator f (h ∘ g) k
      =
      lassociator f g (k ∘ h) • (lassociator (g ∘ f) h k • id₂ k ⋆⋆ rassociator f g h).
  Proof.
    rewrite <- !inverse_of_assoc.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vassocr.
    symmetry ; apply pentagon.
  Qed.

  Lemma triangle_r_inv
             {X Y Z : C}
             (g : C ⟦ Y, Z ⟧) (f : C ⟦ X, Y ⟧)
    : linvunitor g ⋆⋆ id₂ f
      =
      id₂ g ⋆⋆ rinvunitor f • rassociator _ _ _.
  Proof.
    use inv_cell_eq.
    - is_iso.
    - is_iso.
    - cbn. apply triangle_r.
  Qed.

  Lemma triangle_l
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : rassociator _ _ _ • lunitor g ⋆⋆ id₂ f = id₂ g ⋆⋆ runitor f.
  Proof.
    rewrite triangle_r.
    rewrite vassocr.
    rewrite <- inverse_of_assoc.
    rewrite vcomp_linv.
    rewrite id2_left.
    apply idpath.
  Qed.

  Lemma whisker_l_hcomp
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦W,X⟧)
             (α : k₁ ==> k₂)
    : (g ∘ f ◅ α) • lassociator _ _ _ =  lassociator _ _ _ • (g ◅ (f ◅ α)).
  Proof.
    symmetry.
    apply rwhisker_rwhisker.
  Qed.

  Lemma whisker_r_hcomp
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦Z,W⟧)
             (α : k₁ ==> k₂)
    : (α ▻ g ∘ f) • rassociator _ _ _  =  rassociator _ _ _ • ((α ▻ g) ▻ f).
  Proof.
    use vcomp_move_R_Mp.
    {
      is_iso.
    }
    cbn.
    rewrite <- vassocr.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    cbn.
    symmetry.
    apply @lwhisker_lwhisker.
  Qed.

  Lemma whisker_l_natural
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦X,Y⟧)
             (α : k₁ ==> k₂)
    :  α • (linvunitor k₂ • (k₂ ◅ η))  =  linvunitor k₁ • ((k₁ ◅ η) • (α ▻ f)).
  Proof.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite !vassocr.
    rewrite linvunitor_natural.
    rewrite <- !vassocr.
    apply maponpaths.
    rewrite rwhisker_hcomp.
    rewrite <- !interchange.
    rewrite !id2_right, !id2_left.
    apply idpath.
  Qed.

  Lemma whisker_r_natural
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦Y,X⟧)
             (α : k₁ ==> k₂)
    :  α • (rinvunitor k₂ • (η ▻ k₂))  = rinvunitor k₁ • ((η ▻ k₁) • (f ◅ α)).
  Proof.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite !vassocr.
    rewrite rinvunitor_natural.
    rewrite <- !vassocr.
    apply maponpaths.
    rewrite lwhisker_hcomp.
    rewrite <- !interchange.
    rewrite !id2_right, !id2_left.
    apply idpath.
  Qed.

  Lemma whisker_l_iso_id₁
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦Y,X⟧)
             (α : k₁ ==> k₂)
             (inv_η : is_invertible_2cell η)
    : α = rinvunitor k₁ • ((η ▻ k₁) • ((f ◅ α) • ((inv_η^-1 ▻ k₂) • runitor k₂))).
  Proof.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vassocr.
    exact (whisker_r_natural η k₁ k₂ α).
  Qed.

  Lemma whisker_r_iso_id₁
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦X,Y⟧)
             (α : k₁ ==> k₂)
             (inv_η : is_invertible_2cell η)
    : α = linvunitor k₁ • ((k₁ ◅ η) • ((α ▻ f) • ((k₂ ◅ inv_η^-1) • lunitor k₂))).
  Proof.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vassocr.
    exact (whisker_l_natural η k₁ k₂ α).
  Qed.

  Lemma whisker_l_eq
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦W,X⟧)
             (α β : k₁ ==> k₂)
    : f ◅ α = f ◅ β -> (g ∘ f) ◅ α = (g ∘ f) ◅ β.
  Proof.
    intros Hαβ.
    rewrite !rwhisker_hcomp.
    rewrite !rwhisker_hcomp in Hαβ.
    rewrite <- !hcomp_identity.
    apply (vcomp_rcancel (lassociator _ _ _)).
    {
      is_iso.
    }
    rewrite !hcomp_lassoc.
    rewrite Hαβ.
    apply idpath.
  Qed.

  Lemma whisker_r_eq
             {W X Y Z : C}
             {f : C⟦Y,Z⟧} {g : C⟦X,Y⟧}
             (k₁ k₂ : C⟦Z,W⟧)
             (α β : k₁ ==> k₂)
    : α ▻ f = β ▻ f -> α ▻ (f ∘ g) = β ▻ (f ∘ g).
  Proof.
    intros Hαβ.
    rewrite !lwhisker_hcomp.
    rewrite !lwhisker_hcomp in Hαβ.
    rewrite <- !hcomp_identity.
    apply (vcomp_lcancel (lassociator _ _ _)).
    {
      is_iso.
    }
    rewrite <- !hcomp_lassoc.
    rewrite Hαβ.
    apply idpath.
  Qed.

  Lemma left_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (runitor g) ▻ f =  lassociator f g (id₁ Z) • runitor (g ∘ f).
  Proof.
    rewrite <- runitor_triangle.
    unfold assoc.
    rewrite vassocr.
    rewrite lassociator_rassociator.
    rewrite id2_left.
    apply idpath.
  Qed.

  Lemma left_unit_inv_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (rinvunitor g) ▻ f = rinvunitor (g ∘ f) • rassociator _ _ _.
  Proof.
    rewrite <- rinvunitor_triangle.
    rewrite <- vassocr.
    rewrite lassociator_rassociator.
    rewrite id2_right.
    apply idpath.
  Qed.

  Lemma lunitor_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : lunitor (g ∘ f) = lassociator (id₁ X) f g • (g ◅ (lunitor f)).
  Proof.
    symmetry.
    apply lunitor_triangle.
  Qed.


  Lemma linvunitor_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : linvunitor (g ∘ f) = (g ◅ (linvunitor f)) • rassociator (id₁ X) f g.
  Proof.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    cbn.
    use vcomp_move_R_Mp.
    {
      is_iso.
    }
    cbn. rewrite <- lunitor_triangle.
    rewrite vassocr.
    rewrite rassociator_lassociator.
    rewrite id2_left.
    apply idpath.
  Qed.

  Lemma lunitor_id_is_left_unit_id
             (X : C)
    : lunitor (id₁ X) = runitor (id₁ X).
  Proof.
    apply lunitor_runitor_identity.
  Qed.


  Lemma lunitor_V_id_is_left_unit_V_id
             (X : C)
    : linvunitor (id₁ X) = rinvunitor (id₁ X).
  Proof.
    use inv_cell_eq.
    - is_iso.
    - is_iso.
    - cbn. apply lunitor_runitor_identity.
  Qed.

  Lemma left_unit_inv_assoc₂
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : rinvunitor (g ∘ f) = (rinvunitor g ▻ f) • lassociator f g (id₁ Z).
  Proof.
    rewrite left_unit_inv_assoc.
    rewrite <- !vassocr.
    rewrite rassociator_lassociator.
    rewrite id2_right.
    apply idpath.
  Qed.

  Lemma triangle_l_inv
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    :  (linvunitor g ⋆⋆ id₂ f) • lassociator f (id₁ Y) g = id₂ g ⋆⋆ rinvunitor f.
  Proof.
    use inv_cell_eq.
    - is_iso.
    - is_iso.
    - cbn. apply triangle_l.
  Qed.

End laws.
