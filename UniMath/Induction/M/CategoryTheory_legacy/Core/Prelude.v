(** * Prelude for category theory *)

(** This re-exports modules that are very frequently needed when doing any kind of
    category theory. This is a matter of taste, but supported empirically by the
    number of files in this package that import these modules individually.
*)

Require Export UniMath.Induction.M.CategoryTheory_legacy.Core.Categories.
Require Export UniMath.Induction.M.CategoryTheory_legacy.Core.Functors.
Require Export UniMath.Induction.M.CategoryTheory_legacy.Core.Isos.
Require Export UniMath.Induction.M.CategoryTheory_legacy.Core.NaturalTransformations.
Require Export UniMath.Induction.M.CategoryTheory_legacy.Core.Univalence.