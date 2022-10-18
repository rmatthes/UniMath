(** ** Refinement of M-types

    M-types can be refined to satisfy the right definitional equalities.
    This idea is from Felix Rech's Bachelor's thesis, and Felix
    Rech also developed together with Luis Scoccola a first formalization
    in UniMath as project work of the UniMath 2017 school. The present
    formalization was obtained as project work of the UniMath 2019 school
    and is heavily inspired by that former formalization.

    Author: Dominik Kirst (@dominik-kirst) and Ralph Matthes (@rmatthes)

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Induction.FunctorCoalgebras_legacy.
Require Import UniMath.CategoryTheory.categories.Type.Core.

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.
Require Import UniMath.Induction.M.Uniqueness.

(**
    The construction is called a refinement: as input we take any final coalgebra
    for the respective polynomial functor describing an M-type  (hence, with the
    provable coiteration rule), the output is the refined final coalgebra with the
    equational rule of coiteration holding definitionally: Lemma [corec_computation]
    is proved merely by [idpath]. Of course, both coalgebras are equal - provably
    (Lemma [coalgebras_eq]).
*)
Section Refinement.

  Local Open Scope cat.
  Local Open Scope functions.

  Context (A : UU).
  Context (B : A → UU).
  Let F := polynomial_functor A B : type_precat ⟶ type_precat.

  Context (M0 : coalgebra F).
  Local Definition carrierM0 : type_precat := coalgebra_ob F M0.
  Local Definition destrM0 : type_precat ⟦ carrierM0, F carrierM0 ⟧
    := coalgebra_mor F M0.

  Context (finalM0 : is_final M0).
  Local Definition coitM0 (C : coalgebra F) :
    type_precat ⟦ coalgebra_ob F C, carrierM0 ⟧ := (pr11 (finalM0 C)).

  (** Refinement of the final coalgebra to computable elements *)
  Definition carrierM : UU := ∑ m0 : carrierM0,
        ∃ (C : coalgebra F) (c : coalgebra_ob F C), coitM0 C c = m0.

  (** Definition of the coiterator *)
  Definition coitM (C : coalgebra F) (c : coalgebra_ob F C) : carrierM.
  Proof.
    exists (coitM0 C c). apply hinhpr. exists C, c. apply idpath.
  Defined.

  (** Definition of a proposition we factor the computation through *)
  Local Definition P (m0 : carrierM0) :=
    ∑ af : F carrierM, destrM0 m0 = # F pr1 af.

  (** in order to show [P] to be a proposition, a not obviously equivalent
    formulation is given for which it is easy to show [isaprop] *)
  Local Definition P' (m0 : carrierM0) :=
    ∑ ap : ∑ a : A, pr1 (destrM0 m0) = a,
                 ∏ (b : B (pr1 ap)),
                 ∑ mp : ∑ m0' : carrierM0,
                                transportf (λ a, B a  -> carrierM0)
                                           (pr2 ap)
                                           (pr2 (destrM0 m0)) b =
                                m0',
                                ∃ C c, coitM0 C c = pr1 mp.

  (** the easy auxiliary lemma *)
  Local Lemma P'_isaprop m0 : isaprop (P' m0).
  Proof.
    apply isofhleveltotal2.
    - apply isofhlevelcontr.
      apply iscontrcoconusfromt.
    - intro ap; induction ap as [a p].
      apply impred; intros b.
      apply isofhleveltotal2.
      + apply isofhlevelcontr.
        apply iscontrcoconusfromt.
      + intro mp; induction mp as [m0' q].
        apply isapropishinh.
  Defined.

  (** the crucial lemma *)
  Local Lemma P_isaprop (m0 : carrierM0) : isaprop (P m0).
  Proof.
    use (@isofhlevelweqb _ _ (P' m0) _ (P'_isaprop m0)).
    simple refine (weqcomp (weqtotal2asstor _ _) _).
    simple refine (weqcomp _ (invweq (weqtotal2asstor _ _))).
    apply weqfibtototal; intro a.
    intermediate_weq (
        ∑ f : B a  → carrierM,
              ∑ p : pr1 (destrM0 m0) = a,
                    transportf
                      (λ a, B a -> carrierM0)
                      p
                      (pr2 (destrM0 m0)) =
                    pr1 ∘ f).
    {
      apply weqfibtototal; intro f.
      apply total2_paths_equiv.
    }
    intermediate_weq (∑ p : pr1 (destrM0 m0) = a,
                            ∑ f : B a → carrierM,
                                  transportf
                                    (λ a, B a → carrierM0)
                                    p
                                    (pr2 (destrM0 m0)) =
                                  pr1 ∘ f).
    { apply weqtotal2comm. }
    apply weqfibtototal; intro p.
    intermediate_weq (∑ fg : ∑ f : B a -> carrierM0,
                                   ∏ b, ∃ C c, coitM0 C c = f b,
                        transportf
                          (λ a, B a -> carrierM0)
                          p
                          (pr2 (destrM0 m0)) =
                        pr1 fg).
    { use weqbandf.
      - apply weqfuntototaltototal.
      - cbn.
        intro f.
        apply idweq.
    }
    intermediate_weq (∑ f : B a  → carrierM0,
                            ∑ _ : ∏ b, ∃ C c, coitM0 C c = f b,
                        transportf
                          (λ a, B a  → carrierM0)
                          p
                          (pr2 (destrM0 m0)) =
                        f).
    { apply weqtotal2asstor. }
    intermediate_weq (∑ f : B a → carrierM0,
                            ∑ _ : ∏ b, ∃ C c, coitM0 C c = f b,
                        ∏ b, transportf
                               (λ a, B a → carrierM0)
                               p
                               (pr2 (destrM0 m0)) b =
                             f b).
    { apply weqfibtototal; intro f.
      apply weqfibtototal; intros _.
      apply weqtoforallpaths.
    }
    intermediate_weq (∑ f : B a → carrierM0,
                            ∏ b, ∑ _ : ∃ C c, coitM0 C c = f b,
                        transportf
                          (λ a, B a  → carrierM0)
                          p
                          (pr2 (destrM0 m0)) b =
                        f b).
    { apply weqfibtototal; intro f.
      apply invweq.
      apply weqforalltototal.
    }
    intermediate_weq (∏ b, ∑ m0' : carrierM0,
                                   ∑ _ : ∃ C c, coitM0 C c = m0',
                        transportf
                          (λ a, B a -> carrierM0)
                          p
                          (pr2 (destrM0 m0)) b =
                        m0').
    { apply invweq.
      apply weqforalltototal.
    }
    apply weqonsecfibers; intro b.
    intermediate_weq (∑ m0' : carrierM0,
                              ∑ _ : transportf
                                      (λ a, B a -> carrierM0)
                                      p
                                      (pr2 (destrM0 m0)) b =
                                    m0',
                                    ∃ C c, coitM0 C c = m0').
    {
      apply weqfibtototal; intro m0'.
      apply weqdirprodcomm.
    }
    intermediate_weq (∑ mp : ∑ m0', transportf (λ a, B a → carrierM0) p
                                               (pr2 (destrM0 m0)) b = m0',
                             ∃ C c, coitM0 C c = pr1 mp).
    {
      apply invweq.
      apply weqtotal2asstor.
    }
    use weqbandf.
    - apply weqfibtototal; intro m0'.
      apply idweq.
    - cbn. intro mp.
      apply idweq.
  Defined.

  (** Now the destructor of M can be defined *)
  Local Definition destrM' (m : carrierM) : P (pr1 m).
  Proof.
    induction m as [m0 H]. apply (squash_to_prop H); try apply P_isaprop.
    intros [C [c H1]].
    refine ((# F (coitM C) ∘ (pr2 C)) c,, _). cbn [pr1]. clear H.
    assert (H : is_coalgebra_homo F (coitM0 C)).
    { unfold coitM0 in H1. unfold coitM0.
      destruct (finalM0 C) as [[G H] H']. apply H. }
    apply toforallpaths in H.
    apply pathsinv0.
    intermediate_path (destrM0 (coitM0 C c)).
    - apply H.
    - apply maponpaths. assumption.
  Defined.

  Definition destrM (m : carrierM) : F carrierM :=
    pr1 (destrM' m).

  Definition M : coalgebra F := (carrierM,, destrM).

  (** The destructor satisfies the coiteration equation definitionally *)
  Lemma coit_computation C c : destrM (coitM C c) = # F (coitM C) (pr2 C c).
  Proof.
    apply idpath.
  Defined.

  (** The two carriers are equal *)
  Lemma eq_coitM0 (m0 : coalgebra_ob F M0) : coitM0 M0 m0 = m0.
  Proof.
    unfold coitM0.
    induction finalM0 as [[G H1] H2]. cbn.
    specialize (H2 (coalgebra_homo_id F M0)).
    change (pr1 (G,, H1) m0 = pr1 (coalgebra_homo_id F M0) m0).
    apply (maponpaths (fun X => pr1 X m0)).
    apply pathsinv0.
    assumption.
  Defined.

  Definition injectM0 (m0 : coalgebra_ob F M0) : ∃ C c, coitM0 C c = m0.
  Proof.
    apply hinhpr. exists M0, m0. apply eq_coitM0.
  Defined.

  Lemma carriers_weq :
    carrierM ≃ carrierM0.
  Proof.
    apply (weq_iso pr1 (λ m0, m0 ,, injectM0 m0)).
    - intros [m H]. cbn. apply maponpaths, ishinh_irrel.
    - intros x. cbn. apply idpath.
  Defined.

  Lemma carriers_eq :
    carrierM = carrierM0.
  Proof.
    apply weqtopaths, carriers_weq.
  Defined. (** needs to be transparent *)

  (** The two coalgebras are equal *)
  Local Lemma eq1 (m0 : carrierM0) :
    transportf (λ X, X → F X) carriers_eq destrM m0
    = transportf (λ X, F X) carriers_eq (destrM (transportf (λ X, X) (!carriers_eq) m0)).
  Proof.
    destruct carriers_eq. apply idpath.
  Defined.

  Local Lemma eq2 (m0 : carrierM0) :
    transportf (λ X, X) (!carriers_eq) m0 = m0,, injectM0 m0.
  Proof.
    apply (transportf_pathsinv0' (idfun UU) carriers_eq).
    unfold carriers_eq. rewrite weqpath_transport. apply idpath.
  Defined.

  Local Lemma eq3 m0 :
    destrM (m0,, injectM0 m0) = pr1 (destrM0 m0),, coitM M0 ∘ pr2 (destrM0 m0).
  Proof.
    apply idpath.
  Defined.

  Lemma coalgebras_eq :
    M = M0.
  Proof.
    use total2_paths_f; try apply carriers_eq.
    apply funextfun. intro m0.
    rewrite eq1. rewrite eq2. rewrite eq3.
    cbn. unfold polynomial_functor_obj.
    rewrite transportf_total2_const.
    use total2_paths_f; try apply idpath.
    cbn. apply funextsec. intros b. rewrite <- helper_A.
    unfold carriers_eq. rewrite weqpath_transport.
    cbn. rewrite eq_coitM0. apply idpath.
  Defined.

  (** Thus M is final *)
  Lemma finalM : is_final M.
  Proof.
    rewrite coalgebras_eq. apply finalM0.
  Defined.

End Refinement.
