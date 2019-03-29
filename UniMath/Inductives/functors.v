Require Export UniMath.Foundations.PartA.


Definition Fam (I : UU) :=
  I -> UU.

Definition Mapi {I : UU} (A B : Fam I) :=
  ∏ i, A i -> B i.
Infix "->i" := Mapi (at level 99).

Definition idmapi {I : UU} (A : Fam I) :=
  λ (i : I) (a : A i), a.

Definition compi {I : UU} {A B C : Fam I}
           (f : B ->i C)
           (g : A ->i B) :=
  λ i a, f i (g i a).
Infix "∘i" := compi (at level 49).

Definition WEqi {I : UU} (A B : Fam I) : UU :=
  ∏ i, A i ≃ B i.
Infix "≃i" := WEqi (at level 80).
Definition weqcompi {I : UU} {A B C : Fam I}
           (f : A ≃i B) (g : B ≃i C) :
  A ≃i C :=
  λ i, weqcomp (f i) (g i).
Definition invweqi {I : UU} {A B : Fam I} (f : A ≃i B) : B ≃i A :=
  λ i, invweq (f i).



Definition prefunctor (I J : UU) : UU :=
  ∑ F : Fam I -> Fam J,
        ∏ A B : Fam I, (A ->i B) -> F A ->i F B.

Definition on_objects {I J : UU} (F : prefunctor I J) : Fam I -> Fam J :=
  pr1 F.
Notation "F .0" :=
  (on_objects F) (at level 45, right associativity) : functor_scope.

Definition on_maps {I J : UU} (F : prefunctor I J) {A B : Fam I} (f : A ->i B) :
  on_objects F A ->i on_objects F B :=
  pr2 F _ _ f.
Notation "F .1" :=
  (on_maps F) (at level 45, right associativity) : functor_scope.

Open Scope functor_scope.

(* properties of functor *)
Definition id_to_id {I J : UU} (F : prefunctor I J) : UU :=
  ∏ A : Fam I,
        F.1 (idmapi A) = (idmapi (F.0 A)).

Definition comp_to_comp {I J : UU} (F : prefunctor I J) : UU :=
  ∏ A B C : Fam I,
  ∏ f : A ->i B,
  ∏ g : B ->i C,
        F.1 (g ∘i f) = (F.1 g) ∘i (F.1 f).

Definition is_functor {I J : UU} (F : prefunctor I J) :=
  (id_to_id F) ×
  (comp_to_comp F).

Definition functor (I J : UU) : UU :=
  ∑ F : prefunctor I J,
        is_functor F.

Definition build_functor {I J : UU}
           (on_objects : Fam I -> Fam J)
           (on_maps : ∏ A B : Fam I, A ->i B -> on_objects A ->i on_objects B)
           (id_to_id : ∏ A, on_maps A A (idmapi _) = idmapi _)
           (comp_to_comp : ∏ A B C (f : A ->i B) (g : B ->i C),
                           on_maps _ _ (g ∘i f) = on_maps _ _ g ∘i on_maps _ _ f) :
  functor I J :=
  (on_objects,,
    on_maps),,
  id_to_id,,
  comp_to_comp.

Coercion functor_to_prefunctor {I J : UU} (F : functor I J) : prefunctor I J :=
  pr1 F.

(* projections of properties *)
Definition functor_id_to_id {I J : UU} (F : functor I J) :
  ∏ A : Fam I, F.1 (idmapi _) = (idmapi _) :=
  pr1 (pr2 F).

Definition functor_comp_to_comp {I J : UU} (F : functor I J) :
  ∏ A B C : Fam I,
  ∏ f : A ->i B,
  ∏ g : B ->i C,
        F.1 (g ∘i f) = (F.1 g) ∘i (F.1 f) :=
  pr2 (pr2 F).
