(**************************************************************************************************

  Algebraic Theories

  These objects are known by many names: algebraic theories, abstract clones, cartesian operads
  and Lawvere theories. This file defines them and gives constructors, accessors and related
  definitions and lemmas.

  Contents
  1. The definition of algebraic theories [algebraic_theory]
  2. Some useful properties and definitions

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.Combinatorics.Tuples.

Declare Scope algebraic_theories.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The definition of algebraic theories *)

Definition algebraic_theory_data : UU := algebraic_theory_data_cat.

Definition algebraic_theory_data_to_function
  (T : algebraic_theory_data)
  : nat → hSet
  := pr1 T.

Coercion algebraic_theory_data_to_function : algebraic_theory_data >-> Funclass.

Definition var
  {T : algebraic_theory_data}
  {n : nat}
  (i : stn n)
  : var_ax T n i
  := pr12 T n i.

Definition subst
  {T : algebraic_theory_data}
  {m n : nat}
  (f : T m)
  (g : stn m → T n)
  : subst_ax T m n f g
  := pr22 T m n f g.

Notation "f • g" :=
  (subst f g)
  (at level 35) : algebraic_theories.

Definition algebraic_theory : UU := algebraic_theory_cat.

#[reversible] Coercion algebraic_theory_to_algebraic_theory_data (T : algebraic_theory)
  : algebraic_theory_data
  := pr1 T.

Definition make_algebraic_theory_data
  (T : nat → hSet)
  (var : ∏ n i, var_ax T n i)
  (subst : ∏ m n f g, subst_ax T m n f g)
  : algebraic_theory_data
  := T ,, var ,, subst.

Definition make_is_algebraic_theory
  (T : algebraic_theory_data)
  (H1 : ∏ l m n f_l f_m f_n, subst_subst_ax T l m n f_l f_m f_n)
  (H2 : ∏ m n i f, var_subst_ax T m n i f)
  (H3 : ∏ n f, subst_var_ax T n f)
  : is_algebraic_theory T
  := H1 ,, H2 ,, H3.

Definition make_algebraic_theory
  (T : algebraic_theory_data)
  (H : is_algebraic_theory T)
  : algebraic_theory
  := T ,, H.

Definition subst_subst
  (T : algebraic_theory)
  {l m n : nat}
  (f_l : T l)
  (f_m : stn l → T m)
  (f_n : stn m → T n)
  : subst_subst_ax (T : algebraic_theory_data) l m n f_l f_m f_n
  := pr12 T l m n f_l f_m f_n.

Definition var_subst
  (T : algebraic_theory)
  {m n : nat}
  (i : stn m)
  (f : stn m → T n)
  : var_subst_ax (T : algebraic_theory_data) m n i f
  := pr122 T m n i f.

Definition subst_var
  (T : algebraic_theory)
  {n : nat}
  (f : T n)
  : subst_var_ax (T : algebraic_theory_data) n f
  := pr222 T n f.

(** * 2. Some useful properties and definitions *)

Definition lift_constant {T : algebraic_theory_data} (n : nat) (f : (T 0 : hSet))
  : (T n : hSet)
  := f • (weqvecfun _ vnil).
