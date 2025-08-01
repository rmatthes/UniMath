(**

Obtain the lambda calculus and a substitution monad on Set from the signature { [0,0], [1] }.


Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.

Local Open Scope cat.

Section Lam.

(** A lot of notations and preliminary definitions *)

Local Infix "::" := (@cons nat).
Local Notation "[]" := (@nil nat) (at level 0, format "[]").
Local Notation "'HSET2'":= [HSET, HSET].
Local Notation "'Id'" := (functor_identity _).
Local Notation "F * G" := (H HSET HSET HSET BinProductsHSET F G).
(* Local Notation "F + G" := (BinSumOfSignatures.H _ _ _ _ _ _ BinCoproductsHSET F G). *)
Local Notation "'_' 'o' 'option'" :=
  (ℓ (option_functor BinCoproductsHSET TerminalHSET)) (at level 10).


Local Definition BinProductsHSET2 : BinProducts HSET2.
Proof.
apply (BinProducts_functor_precat _ _ BinProductsHSET).
Defined.

Local Notation "x ⊗ y" := (BinProductObject _ (BinProductsHSET2 x y)).
Let precomp_option X := (pre_composition_functor _ _ HSET
                          (option_functor BinCoproductsHSET TerminalHSET) X).
Local Notation "X + 1" := (precomp_option X) (at level 50).
Local Notation "'1'" := (functor_identity HSET).


(** * The lambda calculus from a binding signature *)

(** The signature of the lambda calculus: { [0,0], [1] } *)
Definition LamSig : BindingSig :=
  make_BindingSig isasetbool (λ b, if b then 0 :: 0 :: [] else 1 :: [])%nat.

(** The signature with strength for the lambda calculus *)
Definition LamSignature : Signature HSET _ _ :=
  BindingSigToSignatureHSET LamSig.

Let Id_H := Id_H _ BinCoproductsHSET.

Definition LamFunctor : functor HSET2 HSET2 := Id_H LamSignature.

Lemma lambdaFunctor_Initial : Initial (FunctorAlg LamFunctor).
Proof.
apply (SignatureInitialAlgebraHSET (Presignature_Signature LamSignature)), is_omega_cocont_BindingSigToSignatureHSET.
Defined.

Definition LamMonad : Monad HSET := BindingSigToMonadHSET LamSig.

Definition LC : HSET2 :=
  alg_carrier _ (InitialObject lambdaFunctor_Initial).

Let LC_mor : HSET2⟦LamFunctor LC,LC⟧ :=
  alg_map _ (InitialObject lambdaFunctor_Initial).

Let LC_alg : algebra_ob LamFunctor :=
  InitialObject lambdaFunctor_Initial.

Definition var_map : HSET2⟦1,LC⟧ := η LC_alg.

Definition app_map : HSET2⟦LC ⊗ LC,LC⟧ :=
  CoproductIn bool HSET2 (Coproducts_functor_precat _ _ _ _ _) true · τ LC_alg.

Definition lam_map : HSET2⟦LC + 1,LC⟧ :=
  CoproductIn bool HSET2 (Coproducts_functor_precat _ _ _ _ _) false · τ LC_alg.

Definition make_lambdaAlgebra X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) :
  algebra_ob LamFunctor.
Proof.
  apply (tpair _ X).
  use (BinCoproductArrow _ fvar).
  use CoproductArrow.
  intro b; induction b.
  - apply fapp.
  - apply flam.
Defined.

Definition foldr_map X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) :
  algebra_mor _ LC_alg (make_lambdaAlgebra X fvar fapp flam).
Proof.
  apply (InitialArrow lambdaFunctor_Initial (make_lambdaAlgebra X fvar fapp flam)).
Defined.

Lemma foldr_var X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) :
  var_map · foldr_map X fvar fapp flam = fvar.
Proof.
  assert (F := maponpaths (λ x, BinCoproductIn1 (BinCoproducts_functor_precat _ _ _ _ _) · x)
                 (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
  rewrite assoc in F.
  eapply pathscomp0; [apply F|].
  rewrite assoc.
  eapply pathscomp0; [eapply cancel_postcomposition, BinCoproductOfArrowsIn1|].
  rewrite <- assoc.
  eapply pathscomp0; [eapply maponpaths, BinCoproductIn1Commutes|].
  apply id_left.
Defined.

(* Lemma foldr_var_pt X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) (A : HSET) (x : pr1 A) : *)
(*   pr1 (pr1 (foldr_map X fvar fapp flam)) A (pr1 var_map A x) = pr1 fvar A x. *)
(* Proof. *)
(* set (H := (toforallpaths _ _ _ (nat_trans_eq_pointwise (foldr_var X fvar fapp flam) A) x)). *)
(* (* now rewrite foldr_var. *) *)
(* (* Arguments foldr_map : simpl never. *) *)
(* (* Arguments alg_carrier : simpl never. *) *)
(* (* Arguments var_map : simpl never. *) *)
(* cbn in *. *)
(* apply H. *)
(* Qed. *)

Lemma foldr_app X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) :
  app_map · foldr_map X fvar fapp flam =
  # (pr1 (Id * Id)) (foldr_map X fvar fapp flam) · fapp.
Proof.
  assert (F := maponpaths (λ x, CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) true ·
                                                BinCoproductIn2 (BinCoproducts_functor_precat
                                                                     _ _ _ _ _) · x)
                 (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
  rewrite assoc in F.
  unfold app_map, τ, tau2_from_alg.
  rewrite assoc.
  etrans; [apply F|].
  rewrite assoc.
  etrans.
  { eapply cancel_postcomposition.
    rewrite <- assoc.
    eapply maponpaths, BinCoproductOfArrowsIn2. }
  rewrite assoc.
  etrans.
  { eapply @cancel_postcomposition. eapply @cancel_postcomposition.
    apply (CoproductOfArrowsIn _ _ (Coproducts_functor_precat _ _ _
               _ (λ i, pr1 (Arity_to_Signature BinProductsHSET
      BinCoproductsHSET TerminalHSET (BindingSigMap LamSig i)) `LC_alg))). }
  rewrite <- assoc.
  etrans; [eapply maponpaths, BinCoproductIn2Commutes|].
  rewrite <- assoc.
  etrans; eapply maponpaths.
  - exact (CoproductInCommutes _ _ _ _ _ _ true).
  - apply idpath.
Defined.

Lemma foldr_lam X (fvar : HSET2⟦1,X⟧) (fapp : HSET2⟦X ⊗ X,X⟧) (flam : HSET2⟦X + 1,X⟧) :
  lam_map · foldr_map X fvar fapp flam =
  # (pr1 (_ o option)) (foldr_map X fvar fapp flam) · flam.
Proof.
  assert (F := maponpaths (λ x, CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ _) false ·
                                                BinCoproductIn2 (BinCoproducts_functor_precat
                                                                     _ _ _ _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
  rewrite assoc in F.
  unfold lam_map, τ, tau2_from_alg.
  rewrite assoc.
  etrans; [apply F|].
  rewrite assoc.
  etrans.
  { eapply cancel_postcomposition.
    rewrite <- assoc.
    eapply maponpaths, BinCoproductOfArrowsIn2. }
  rewrite assoc.
  etrans.
  { eapply @cancel_postcomposition, @cancel_postcomposition.
    apply (CoproductOfArrowsIn _ _ (Coproducts_functor_precat _ _ _
            _ (λ i, pr1 (Arity_to_Signature BinProductsHSET
                           BinCoproductsHSET TerminalHSET (BindingSigMap LamSig i)) `LC_alg))). }
  rewrite <- assoc.
  etrans.
  { eapply maponpaths, BinCoproductIn2Commutes. }
  rewrite <- assoc.
  etrans; eapply maponpaths.
  - exact (CoproductInCommutes _ _ _ _ _ _ false).
  - apply idpath.
Defined.


Local Notation "'1'" := (TerminalHSET).
Local Notation "a ⊕ b" := (BinCoproductObject (BinCoproductsHSET a b)).
Local Notation "x ⊛ y" := (BinProductObject _ (BinProductsHSET x y)) (at level 60).

(** This makes cbn not unfold things too much below *)
Arguments LamMonad : simpl never.
Arguments BinCoproductObject : simpl never.

Definition substLam (X : HSET) : HSET⟦LamMonad (1 ⊕ X) ⊛ LamMonad X, LamMonad X⟧.
Proof.
intro H.
set (f := monadSubst LamMonad BinCoproductsHSET TerminalHSET X).
set (g := λ (_ : unit), pr2 H).
cbn in H, f, g.
apply (f g (pr1 H)).
Defined.

End Lam.
