
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of precategory of pointed endofunctors
-    Forgetful functor to precategory of endofunctors


************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Local Open Scope cat.

Section def_ptd.

Variable C : precategory.
Hypothesis hs : has_homsets C.

Definition ptd_obj : UU := ∑ F : [C, C, hs], [C, C, hs]⟦functor_identity_as_ob C hs, F⟧.

Coercion functor_from_ptd_obj (F : ptd_obj) : [C, C, hs] := pr1 F.

Definition ptd_pt (F : ptd_obj) : [C, C, hs]⟦functor_identity_as_ob C hs, F⟧ := pr2 F.

Definition is_ptd_mor {F G : ptd_obj}(α: [C, C, hs]⟦F, G⟧) : UU := ptd_pt F · α = ptd_pt G.

Definition ptd_mor (F G : ptd_obj) : UU :=
  ∑ α : [C, C, hs]⟦F, G⟧, is_ptd_mor α.

Coercion nat_trans_from_ptd_mor {F G : ptd_obj} (a : ptd_mor F G) : [C, C, hs]⟦F, G⟧ := pr1 a.

Lemma eq_ptd_mor {F G : ptd_obj} (a b : ptd_mor F G)
  : a = b ≃ (a : [C, C, hs]⟦F, G⟧) = b.
Proof.
  apply subtypeInjectivity.
  intro α.
  apply functor_category_has_homsets.
Defined.

Definition ptd_mor_commutes {F G : ptd_obj} (α : ptd_mor F G)
  : ptd_pt F  · α  = ptd_pt G.
Proof.
  exact (pr2 α).
Qed.

Definition ptd_mor_commutes_pointwise {F G : ptd_obj} (α : ptd_mor F G)
  : ∏ c : C, pr1 (ptd_pt F) c · (pr1 (pr1 α)) c = pr1 (ptd_pt G) c.
Proof.
  intro.
  assert (commutes := pr2 α).
  hnf in commutes.
  apply (maponpaths pr1) in commutes.
  apply toforallpaths in commutes.
  apply commutes.
Qed.

Definition ptd_id (F : ptd_obj) : ptd_mor F F.
Proof.
  exists (nat_trans_id _ ).
  apply id_right.
Defined.

Definition ptd_comp {F F' F'' : ptd_obj} (α : ptd_mor F F') (α' : ptd_mor F' F'')
  : ptd_mor F F''.
Proof.
  exists (α · α').
  hnf.
  rewrite assoc.
  rewrite (ptd_mor_commutes α).
  apply (ptd_mor_commutes α').
Defined.

Definition ptd_ob_mor : precategory_ob_mor := ptd_obj ,, ptd_mor.

Definition ptd_precategory_data : precategory_data := ptd_ob_mor ,, ptd_id,, @ptd_comp.

Lemma is_precategory_ptd : is_precategory ptd_precategory_data.
Proof.
  repeat split; simpl; intros; apply (invmap (eq_ptd_mor _ _ )).
  - apply id_left.
  - apply id_right.
  - apply assoc.
  - apply assoc'.
Qed.

Definition precategory_Ptd : precategory := tpair _ _ is_precategory_ptd.

Definition id_Ptd : precategory_Ptd.
Proof.
  exists (functor_identity _).
  exact (nat_trans_id _ ).
Defined.

Lemma eq_ptd_mor_precat {F G : precategory_Ptd} (a b : F --> G)
  : a = b ≃ (a : ptd_mor F G) = b.
  use tpair.
  - intro H. exact H.
  - apply idisweq.
Defined.

(** Forgetful functor to functor category *)

Definition ptd_forget_data : functor_data precategory_Ptd [C, C, hs].
Proof.
  exists (λ a, pr1 a).
  exact (λ a b f, pr1 f).
Defined.

Lemma is_functor_ptd_forget : is_functor ptd_forget_data.
Proof.
  split; intros; red; intros; apply idpath.
Qed.

Definition functor_ptd_forget : functor _ _ := tpair _ _ is_functor_ptd_forget.

End def_ptd.
