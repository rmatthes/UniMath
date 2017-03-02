(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.UnivalenceAxiom.
Local Open Scope poset.

Definition WellOrderedSet := ∑ (X:hSet) (R:hrel X), isWellOrder R.

Definition WellOrderedSet_to_OrderedSet (X:WellOrderedSet) : OrderedSet.
Proof.
  unfold WellOrderedSet in X.
  unfold isWellOrder in X.
  unfold isTotalOrder in X.
  use tpair.
  - use tpair.
    + exact (pr1 X).
    + simpl. use tpair.
      * exact (pr1 (pr2 X)).
      * simpl. exact (pr1 (pr1 (pr2 (pr2 X)))).
  - simpl. exact (pr2 (pr1 (pr2 (pr2 X)))).
Defined.

Coercion WellOrderedSet_to_OrderedSet : WellOrderedSet >-> OrderedSet.

Definition isClosedSubposet {W:Poset} (Y X:hsubtype W) : hProp.
Proof.
  exists (
      (∏ x:W, Y x -> X x)
        ×
        (∏ (x y:W), Y y -> X x -> x ≤ y -> Y x)).
  apply isapropdirprod.
  - apply impred; intro y; apply impred; intro h. apply propproperty.
  - apply impred; intro x; apply impred; intro y; apply impred; intro k;
      apply impred; intro h; apply impred; intro le.
    apply propproperty.
Defined.
