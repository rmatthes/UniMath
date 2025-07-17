(** * Limits in the precategory of types

Author: Langston Barrett (@siddharthist), Feb 2018
*)

(** ** Contents:

  - Terminal object ([TerminalType])
  - Binary products ([BinProductsType])
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.

Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Categories.
Require Import UniMath.Induction.M.CategoryTheory_legacy.Core.Functors.

Require Import UniMath.Induction.M.CategoryTheory_legacy.limits.terminal.
Require Import UniMath.Induction.M.CategoryTheory_legacy.limits.binproducts.

Require Import UniMath.Induction.M.CategoryTheory_legacy.categories.Type.Core.

(** ** Terminal object ([TerminalType]) *)

(** The [unit] type is a terminal object for the precategory of types. *)
Lemma TerminalType : Terminal type_precat.
Proof.
  apply (make_Terminal (unit : ob type_precat)).
  exact iscontrfuntounit.
Defined.

(** ** Binary products ([BinProductsType]) *)

(** The precategory of types has binary products. *)
Lemma BinProductsType : BinProducts type_precat.
Proof.
  intros X Y.
  use tpair.
  - exact ((X × Y),, dirprod_pr1,, dirprod_pr2).
  - apply isBinProduct'_to_isBinProduct.
    intro; apply (weqfuntoprodtoprod _ X Y).
Defined.