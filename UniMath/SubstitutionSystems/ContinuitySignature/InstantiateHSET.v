Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Require Import UniMath.SubstitutionSystems.ContinuitySignature.GeneralLemmas.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.ContinuityOfMultiSortedSigToFunctor.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.MultiSortedSignatureFunctorEquivalence.

Local Open Scope cat.

Section CoproductsIndexedOverHPropCommutesWithBinproductsInSET.

  Definition propcoproducts_commute_binproductsHSET
    : propcoproducts_commute_binproducts HSET BinProductsHSET (λ p, CoproductsHSET p (isasetaprop (pr2 p))).
  Proof.
    intros p x y.
    use make_is_z_isomorphism.
    - intros [ix iy].
      exists (pr1 ix).
      exact (pr2 ix,,pr2 iy).
    - split.
      + apply funextsec ; intro ixy.
        use total2_paths_f ; apply idpath.
      + apply funextsec ; intros [ix iy].
        use total2_paths_f.
        * apply idpath.
        * use total2_paths_f.
          -- apply (pr2 p).
          -- cbn.
             induction (pr1 (pr2 p (pr1 ix) (pr1 iy))).
             rewrite idpath_transportf.
             apply idpath.
  Defined.

End CoproductsIndexedOverHPropCommutesWithBinproductsInSET.

Section OmegaLimitsCommutingWithCoproductsHSET.

  Definition HSET_ω_limits : Lims_of_shape conat_graph HSET.
  Proof.
    intro coch.
    apply LimConeHSET.
  Defined.

  Lemma test {I : HSET} (ind : pr1 I → cochain SET)
        (f : pr111 (limit_of_coproduct SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind))
    : ∏ n : nat, pr1 (pr1 f n) = pr1 (pr1 f 0).
  Proof.
    induction f as [f p].
    assert (q0 : ∏ n : nat, S n = n + 1).
    { exact (λ n, ! natpluscomm n 1). }

    assert (q : ∏ n : nat, pr1 (f (n+1)) = pr1 (f n)).
    { exact (λ n, base_paths _ _ (p (n+1) n (q0 n))). }

    assert (q' : ∏ n : nat, pr1 (f (S n)) = pr1 (f n)).
    {
      intro n.
      refine (_ @ q n).
      apply (maponpaths (λ z, pr1 (f z))).
      exact (q0 n).
    }

    intro n.
    induction n.
    - apply idpath.
    - exact (q' n @ IHn).
  Defined.

  Local Lemma TODO_JOKER (A : UU) : A. Proof. Admitted.
  Definition I_coproduct_distribute_over_omega_limit_HSET_inverse
             {I : HSET} (ind : pr1 I → cochain SET)
    :  SET ⟦ pr11 (limit_of_coproduct SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind),
             pr11 (coproduct_of_limit SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind) ⟧.
  Proof.
    intros [f p].
    exists (pr1 (f 0)).
    exists (λ n, transportf (λ u, pr1 (dob (ind u) n)) ((test ind (f,,p) n)) (pr2 (f n))).
    intros n m h.

    etrans.
    2: {
      apply maponpaths.
      exact (fiber_paths (p n m h)).
    }

    rewrite transport_f_f.
    cbn.

    set (q := base_paths (pr1 (f n),, pr2 (ind (pr1 (f n))) n m h (pr2 (f n))) (f m) (p n m h) @
                         test ind (f,, p) m).
    set (q' := test ind (f,,p) n).

    assert (q0 : q = q').
    { apply (pr2 I). }
    etrans.
    2: {
      apply maponpaths_2.
      exact (! q0).
    }

    unfold q'.
    clear q0 q' q.
    apply TODO_JOKER.
  Defined.

  Definition I_coproduct_distribute_over_omega_limits_HSET (I : HSET)
    : ω_limits_distribute_over_I_coproducts HSET I HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)).
  Proof.
    intro ind.
    use make_is_z_isomorphism.
    - exact (I_coproduct_distribute_over_omega_limit_HSET_inverse ind).
    - split.
      + apply funextsec ; intros [i [f p]].
        use total2_paths_f.
        { apply idpath. }
        use total2_paths_f.
        2: {
          repeat (apply funextsec ; intro).
          apply (pr2 (dob (ind (pr1 (identity (pr11 (coproduct_of_limit SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind)) _))) _)).
        }

        rewrite idpath_transportf.
        repeat (apply funextsec ; intro).
        apply (transportf_set ((λ u : pr1 I, pr1 (dob (ind u) x)))).
        apply (pr2 I).
      + apply funextsec ; intros [f p].
        use total2_paths_f.
        * apply funextsec ; intro n.
          use total2_paths_f.
          { exact (! test ind (f,,p) n). }
          cbn.
          etrans.
          1: apply (transport_f_f (λ x : pr1 I, pr1 (pr1 (ind x) n))).
          etrans.
          1: apply maponpaths_2, pathsinv0r.
          apply (idpath_transportf (λ x : pr1 I, pr1 (pr1 (ind x) n))).
        * repeat (apply funextsec ; intro).
          apply ( dob (coproduct_n_cochain SET (CoproductsHSET (pr1 I) (pr2 I)) ind) _).
  Defined.

End OmegaLimitsCommutingWithCoproductsHSET.

Lemma is_omega_cont_MultiSortedSigToFunctor_HSET
       (sort : UU) (Hsort_set : isaset sort)
      (M : MultiSortedSig sort)
  : is_omega_cont (MultiSortedSigToFunctor sort (hlevelntosn 2 _ Hsort_set) HSET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET M).
Proof.
  use is_omega_cont_MultiSortedSigToFunctor.
  - exact InitialHSET.
  - exact ProductsHSET.
  - exact HSET_ω_limits.
  - exact propcoproducts_commute_binproductsHSET.
  - exact I_coproduct_distribute_over_omega_limits_HSET.
Defined.