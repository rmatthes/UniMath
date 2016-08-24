(** needs impredicative Set *)

(** author: Ralph Matthes, CNRS & IRIT UPS Toulouse *)
(** This is based on companion material to the article "Verification of
    programs on truly nested datatypes in intensional type theory", 
    presented at the workshop MSFP 2006.*) 
(** It has been tested with Coq V8.5pl2 - coqide/coqtop/coqc -impredicative-set *)

(** Logic for Natural Mendler Iteration of Rank 2 *)
(** Natural is in the sense of category theory; the iterator yields
    polymorphic functions for whom one may establish naturality *)

(** We adopt an approach based on simultaneous induction-recursion
    that guarantees full naturality of the iteratively.
    The idea of its implementation in Coq is taken from Venanzio Capretta. *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.UnicodeNotations.


Set Implicit Arguments.

(** the universe *)
Notation k0 := UU.
(* taking a definition instead might sometimes not be optimal, as remarked by Benedikt *)

(** the type of all type transformations *)
Notation k1 := (k0 -> k0).
(* the parentheses are a suggestion by Benedikt *)

(** the type of all rank-2 type transformations *)
Notation k2 := (k1 -> k1).

(** polymorphic identity *)
Definition id : forall (A:k0), A -> A := fun A x => x.

(** composition *)
Definition comp (A B C:k0)(g:B -> C)(f:A -> B) : A -> C := fun x => g (f x).

Infix "o" := comp (at level 90).

(** refined notion of less than on type transformations *)
Definition less_k1 (X Y:k1) : UU := 
      forall (A B: k0), (A -> B) -> X A -> Y B.

Infix "<_k1"  := less_k1 (at level 60).

(** standard notion of less than on type transformations *)
Definition sub_k1 (X Y:k1) : UU :=
     forall (A:k0), X A -> Y A.

Infix "c_k1" := sub_k1 (at level 60).

Definition mon (X:k1) : UU := X <_k1 X.

Lemma monOk : forall X:k1, mon X = 
  forall (A B:k0), (A -> B) -> X A -> X B.
Proof.
  reflexivity.
Defined.



Definition ext (X Y:k1)(h: X <_k1 Y): UU :=
  forall (A B:k0)(f g: A -> B), 
        (forall (a:A), f a = g a) -> forall (r: X A), h _ _ f r = h _ _ g r.


Definition fct1 (X:k1)(m: mon X) : UU :=
  forall (A:k0)(x:X A), m _ _ (@id A) x = x.

 
Definition fct2 (X:k1)(m: mon X) : UU :=
 forall (A B C:k0)(f:A -> B)(g:B -> C)(x:X A), 
       m _ _ (g o f) x = m _ _ g (m _ _ f x).


(** pack up the good properties of the approximation *)
Record efct (X:k1) : UU := mkefct
  { m : mon X;
     e : ext m;
     f1 : fct1 m;
     f2 : fct2 m }.
(* will later be turned into a nested Sigma type *)

Definition pefct (F:k2) : UU :=
  forall (X:k1), efct X -> efct (F X).


(** natural transformations from (X,mX) to (Y,mY) *)
Definition NAT(X Y:k1)(j:X c_k1 Y)(mX:mon X)(mY:mon Y) : UU :=
  forall (A B:k0)(f:A -> B)(t:X A), j B (mX A B f t) = mY _ _ f (j A t).


Section LNMIt.

Section LNMItDef.
(*  This definition is already the justification "Main Theorem" and the
    construction of canonical elements "Theorem 4" of the paper. *)

Variable F:k2.

(** the only general requirement: F preserves extensional functors *)
Variable Fpefct : pefct F.

(** the type of the iterator, parameterized over the source constructor *)
Definition MItPretype (S:k1) : UU :=
  forall G : k1, (forall X : k1, X c_k1 G -> F X c_k1 G) -> S c_k1 G.

(** the following record used to be an inductive definition in the paper *)
(* in the paper, inE is called In^+, mu2E is called mu^+F *)
Definition mu2E (A: k0) : UU :=
  Σ (G : k1)(ef:efct G)(G':k1)(m':mon G')
          (it:MItPretype G')(j: G c_k1 G')(n:NAT j (m ef) m'), F G A.

Definition inE : forall (G:k1)(ef:efct G)(G':k1)(m':mon G')
          (it:MItPretype G')(j: G c_k1 G'), NAT j (m ef) m' ->
          F G c_k1 mu2E.
(** the intention is that we only want to use inE with G':=mu2,
     m':=mapmu2 and it:=MIt. *)
Proof.
  intros G ef G' m' it j n A t.
  exists G.
  exists ef.
  exists G'.
  exists m'.
  exists it.
  exists j.
  exists n.
  exact t.
Defined.

(** We historically did not want to have j as implicit argument due to eta-problems. *)
Implicit Arguments inE [G G' m' A].


(** we need accessors to the 8 components of the record since we do not want to use destruct **)
Definition mu2E_G (A:k0)(t: mu2E A): k1.
Proof.
  apply pr1 in t.
  exact t.
Defined.

Definition mu2E_ef (A:k0)(t: mu2E A): efct (mu2E_G t).
Proof.
  exact (pr1 (pr2 t)).
Defined.

Definition mu2E_G' (A:k0)(t: mu2E A): k1.
Proof.
  exact (pr1 (pr2 (pr2 t))).
Defined.

Definition mu2E_m' (A:k0)(t: mu2E A): mon (mu2E_G' t).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 t)))).
Defined.

Definition mu2E_it (A:k0)(t: mu2E A): MItPretype (mu2E_G' t).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 t))))).
Defined.

Definition mu2E_j (A:k0)(t: mu2E A): (mu2E_G t) c_k1 (mu2E_G' t).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 t)))))).
Defined.

Definition mu2E_n (A:k0)(t: mu2E A): NAT (mu2E_j t) (m (mu2E_ef t)) (mu2E_m' t).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 t))))))).
Defined.

Definition mu2E_t (A:k0)(t: mu2E A): F (mu2E_G t) A.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 t))))))).
Defined.


(* in the paper, mapmu2E is called map_{mu^+F} *)
Definition mapmu2E : mon mu2E.
Proof.
  intros A B f t.
  set (ef := mu2E_ef t).
  set (it := mu2E_it t).
  set (j := mu2E_j t).
  set (n := mu2E_n t).
  apply (inE(A:=B) ef it j n).
  set (t' := mu2E_t t).
  exact (m (Fpefct ef) f t').
Defined.

(* Print mapmu2E. *)

(** the preliminary iterator with source mu2E does not iterate at all *)
(* in the paper MItE is called MIt^+ *)
Definition MItE : MItPretype mu2E.
Proof.
  intros G' s A t.
  set (G := mu2E_G t).
  set (it := mu2E_it t).
  set (j := mu2E_j t).
  set (t' := mu2E_t t).
  exact (s G (fun A => (it G' s A) o (j A)) A t').
Defined.

Lemma MItEok : forall (G:k1)(s:forall X : k1, X c_k1 G -> F X c_k1 G)(A:k0)
  (X:k1)(ef:efct X)(G':k1)(m':mon G')(it:MItPretype G') 
   (j: X c_k1 G') n (t:F X A),
   MItE s (inE (m':=m') ef it j n t) = s X (fun A => (it G s A) o (j A)) A t.
Proof.
  reflexivity.
Defined.

(** single out the good elements of mu2E A *)
(* in the paper muEcheck is called chk_{mu^+F}, inEcheck is called Inchk *)
(* the following inductive definition will have to be justified by other means *)
Inductive mu2Echeck : forall (A:k0), mu2E A -> k0 :=
   inEcheck : forall (G:k1)(ef:efct G)(j: G c_k1 mu2E)(n: NAT j (m ef) mapmu2E),
       (forall (A:k0)(t:G A), mu2Echeck (j A t)) ->
     forall (A:k0)(t:F G A),
       mu2Echeck (inE ef MItE j n t).
(* Check mu2Echeck. *)
Implicit Arguments inEcheck [G A].
(* Check inEcheck. *)

Scheme mu2Echeck_indk0 := Minimality for mu2Echeck Sort Type. (* Type should be replaced by k0, but this is illegal *)

(* the induction principle that is mentioned right after the inductive definition in the paper *)
Check mu2Echeck_indk0 : forall P : forall A : k0, mu2E A -> k0,
       (forall (G : k1) (ef : efct G) (j : G c_k1 mu2E)
          (n : NAT j (m ef) mapmu2E),
        (forall (A : k0) (t : G A), mu2Echeck (j A t)) ->
        (forall (A : k0) (t : G A), P A (j A t)) ->
        forall (A : k0) (t : F G A),
        P A
          (inE ef MItE j n t)) ->
       forall (A : k0) (r : mu2E A), mu2Echeck r -> P A r.


Definition mu2Echeck_p (A:k0)(r:mu2E A) : hProp := ∥mu2Echeck r∥.

(* in the paper, mu2 is called mu F *)
Definition mu2 (A:k0) : k0 := total2 (fun (r:mu2E A) =>  mu2Echeck_p r).

(* in the paper, mu2cons is called cons *)
Definition mu2cons (A:k0)(r:mu2E A)(p:mu2Echeck_p r) : mu2 A :=
  tpair (fun r : mu2E A => mu2Echeck_p r) r p.
Implicit Arguments mu2cons [A].

(* in the paper, mapmu2 is called map_{mu F} *)
(** a non-iterative definition of the monotonicity witness *)
Definition mapmu2 : mon mu2.
Proof.
  intros A B f r.
  set (r' := pr1 r).
  set (H := pr2 r).
  eexists (mapmu2E f r').
(* STOPS HERE - HOW TO USE PROPOSITIONALLY TRUNCATED ELEMENTS?
  destruct H. (* inversion on mu2Echeck to be removed later *)
  simpl.
  apply inEcheck.
  assumption.
Defined.
*)
Admitted.


Definition pi1 : mu2 c_k1 mu2E.
Proof.
  intros A r.
  exact (pr1 r).
Defined.

(** benefit from propositional truncation *)
Lemma mu2pirr : forall (A:k0)(r1 r2:mu2 A), pi1 r1 = pi1 r2 -> r1 = r2.
Proof.
  intros A r1 r2 H.
  apply subtypeEquality.
  red.
  intro t.
  unfold mu2Echeck_p.
  apply isapropishinh.
  assumption.
Defined.


Definition MIt : MItPretype mu2.
Proof.
  intros G s A r.
  exact (MItE s (pi1 r)).
Defined.
(** This has been very easy since mu2 is only the source type 
      of the transformation. Therefore, we did not even need destruct r.
      Had we used it nevertheless, we would have encountered problems
      with eta. *)


Lemma pi2 : forall(A:k0)(r:mu2 A), mu2Echeck_p (pi1 r).
Proof.
  intros.
  exact (pr2 r).
Defined.

(** first projection commutes with the maps *)
Lemma pi1mapmu2 : forall (A B:k0)(f:A->B)(r:mu2 A),
  pi1 (mapmu2 f r) = mapmu2E f (pi1 r).
Proof.
(*
  reflexivity. (* does this use eta expansion for pairs? *)
Defined.
*)
Admitted.

(** the type of the future datatype constructor In *)
Definition InType : UU := 
    forall (G:k1)(ef:efct G)(j: G c_k1 mu2), NAT j (m ef) mapmu2 ->
        F G c_k1 mu2.

Definition pi1' (G:k1)(j: G c_k1 mu2): G c_k1 mu2E.
Proof.
  intros A H.
  exact (pi1 (j A H)).
Defined.

Lemma pi1'pNAT : forall (G:k1)(m:mon G)(j: G c_k1 mu2),
  NAT j m mapmu2 -> NAT (pi1' j) m mapmu2E.
Proof.
  intros G m j n A B f t.
  unfold pi1'.
  rewrite n.
  apply pi1mapmu2.
Defined.

Lemma pi2' : forall(G:k1)(j: G c_k1 mu2)(A:k0)(t: G A),
             mu2Echeck_p (pi1' j A t).
Proof.
  intros.
  exact (pi2 (j A t)).
Defined.

(* replay the explicit definition in interactive mode *)
Definition hinhfun_inter { X Y : UU } ( f : X -> Y ) : ∥ X ∥ -> ∥ Y ∥ .
Proof.
  intro isx.
  intros P yp.
  apply isx.
  intro x.
  apply yp.
  apply f.
  exact x.
Defined.

(* a tentative extension of [hinhfun_inter] *)
Definition hinhfun_extended {G:k1}{ X: forall (A:k0)(t:G A), UU } { Y : UU }( f : (forall (A:k0)(t:G A), X A t) -> Y ) : (forall (A:k0)(t:G A), ∥X A t∥) -> ∥ Y ∥ .
Proof.
  intro isx.
  intros P yp. (* I do not see anything to pursue the proof in structural ways *)
Admitted.

(** in is reserved for Coq, so the datatype constructor will be In *)
Definition In : InType.
Proof.
  intros G ef j n A t.
  eexists (inE(A:=A)(m':=mapmu2E) ef MItE (pi1' j) (fun A B f t => pi1'pNAT n f t) t).
  unfold pi1'.
  change   (fun (A0 : k0) (H : G A0) => pi1 (j A0 H)) with
  (fun A0 H => (fun A0 H => pi1 (j A0 H)) A0 H).
  apply (hinhfun_extended (X:= fun (A:k0)(t: G A) => mu2Echeck (pi1' j A t))). (* using the very doubtful previous lemma *)
  intro Hyp.
  apply inEcheck.
  exact Hyp.
  exact (pi2' j).
Defined.


(* currently deactivated
(** the iterative behaviour of map comes from the definition of In *)
Lemma mapmu2Red : forall (A:k0)(G:k1)(ef:efct G)(j: G c_k1 mu2)
    (n: NAT j (m ef) mapmu2)(t: F G A)(B:Set)(f:A->B), 
             mapmu2 f (In ef n t) = In ef n (m (Fpefct ef) f t).
Proof.
  reflexivity.
Defined.

Lemma MItRed : forall (G : k1)
  (s : forall X : k1, X c_k1 G -> F X c_k1 G)(X : k1)(ef:efct X)(j: X c_k1 mu2)
      (n: NAT j (m ef) mapmu2)(A:Set)(t:F X A),
     MIt s (In ef n t) = s X (fun A => (MIt s (A:=A)) o (j A)) A t.
Proof.
  reflexivity.
Defined.
*)

(** our desired induction principle, first just as a proposition *)
Definition mu2IndType : Prop :=
  forall P : (forall A : k0, mu2 A -> Prop),
       (forall (X : k1)(ef:efct X)(j : X c_k1 mu2)(n: NAT j (m ef) mapmu2),
          (forall (A : k0) (x : X A), P A (j A x)) ->
        forall (A:k0)(t : F X A), P A (In ef n t)) ->
    forall (A : k0) (r : mu2 A), P A r.

(* this is the more refined induction principle that is used at the end of
   the proof of Theorem 3 in the paper *)
Scheme mu2EcheckInd := Induction for mu2Echeck Sort Type. (* ought to be k0, but this is illegal *)
Check mu2EcheckInd : 
      forall P : forall (A : k0) (t : mu2E A), mu2Echeck t -> Type,
       (forall (G : k1) (ef : efct G) (j : G c_k1 mu2E)
          (n : NAT j (m ef) mapmu2E)
          (p : forall (A : k0) (t : G A), mu2Echeck (j A t)),
        (forall (A : k0) (t : G A), P A (j A t) (p A t)) ->
        forall (A : k0) (t : F G A),
        P A
          (inE ef MItE j n t)
          (inEcheck ef j n p t)) ->
       forall (A : k0) (t : mu2E A) (p : mu2Echeck t), P A t p.


(* END OF PROPER WORK ON THE FILE *)

(*
Definition proof_irrelevance := forall (A:Prop) (a1 a2:A), a1 = a2.

(** this is the only axiom we need *)
Axiom pirr :  proof_irrelevance.
(* should not be needed any longer *)

(** the consequence we typically use *)
Lemma mu2pirr : forall (A:k0)(r1 r2:mu2 A), pi1 r1 = pi1 r2 -> r1 = r2.
Proof.
  intros A r1 r2 H.
  destruct r1 as [r1' H1].
  destruct r2 as [r2' H2].
  simpl in H.
  generalize H1 H2; clear H1 H2.
  destruct H.
  intros.
  rewrite (pirr H1 H2).
  reflexivity.
Qed.
(* will fall away *)
*)

(** uniqueness of identity proofs from library Eqdep *)
Axiom UIP : forall (U:Type) (x y:U) (p1 p2:x = y), p1 = p2.

(** UIP implies uniqueness of naturality proofs *)
Lemma UNP0 : forall(X Y:k1)(j:X c_k1 Y)(mX:mon X)(mY:mon Y)
    (n1 n2: NAT j mX mY)(A B : k0) (f : A -> B) (t : X A),
    n1 A B f t = n2 A B f t.
Proof.
  intros.
  apply UIP.
Qed.

(*
(** uniqueness of naturality proofs is trivially a consequence of proof irrelevance *)
Lemma UNP : forall(X Y:k1)(j:X c_k1 Y)(mX:mon X)(mY:mon Y)
    (n1 n2: NAT j mX mY), n1 = n2.
Proof.
  intros.
  apply pirr.
Qed.
*)

(* this is the justification of muFInd in the paper *)
Lemma mu2Ind : mu2IndType.
Proof.
  intros P s A r.
  set (r' := pr1 r).
  set (H := pr2 r).
  assert (P A (tpair (fun r: mu2E A => mu2Echeck r) r' H)).  (* DOES NOT TYPECHECK *)
Focus 2.
  (* now we are missing eta expansion for pairs but should come along with proof irrelevance *)
Unfocus.
  change (P A (tpair (fun r : mu2E A => mu2Echeck r) r' H)) with 
  (P A (mu2cons r' H)).
  induction H using mu2EcheckInd.
  set (j':=fun (A : k0) (t : G A) => mu2cons(j A t)(m0 A t)).
  change (forall (A : k0) (t : G A),
     P A (mu2cons (j A t) (m0 A t)))
  with (forall (A : k0) (t : G A), P A (j' A t)) in H.
  assert (n1 : NAT (Y:=mu2) j' (m ef) mapmu2).
  red.
  clear A r t r'.
  intros.
  assert (pi1n1 : pi1 (j' B (m ef f t)) =  pi1 (mapmu2 f (j' A t))).
  simpl.
  apply n.
(** using pi1n1: *)
  exact (mu2pirr _ _ pi1n1).
(** using n1: *)
  assert (p : P A (In ef n1 t)).
  exact (s G ef j' n1 H A t).
(** using p: *)
  assert (pi1In : inE ef MItE j n t 
                  = pi1 (In ef n1 t)).
  simpl.
  apply (f_equal (fun x : NAT j (m ef) mapmu2E
                               => inE ef MItE _ x t)).
  apply UNP. (** equates n and pi1'pNAT n1 *)
(** using pi1In: *)
  simpl.
  apply (eq_ind _ (fun r => P A r) p).
  apply mu2pirr.
  rewrite <- pi1In.
  reflexivity.
Qed.

Print mu2Ind.

(* these constitute parts of the proof of Theorem 4 *)

Lemma mapmu2Id: fct1 mapmu2.
Proof.
  red.
  apply (mu2Ind (fun A r => mapmu2 (id(A:=A)) r = r)).
  intros.
  clear H (* the IH *).
  rewrite mapmu2Red.
  apply (f_equal (fun x=> In (A:=A) ef n x)).
  apply (f1 (Fpefct ef) _ t).
Qed.


Lemma mapmu2Ext : ext mapmu2.
Proof.
  red.
  intros.
  generalize H; clear H.
  generalize f g; clear f g.
  generalize B; clear B.
  generalize A r; clear A r.
  apply (mu2Ind (fun A r => forall (B : Set) (f g : A -> B),
       (forall a : A, f a = g a) -> mapmu2 f r = mapmu2 g r)).
  intros.
  clear H (* the IH *).
  do 2 rewrite mapmu2Red.
  apply (f_equal (fun x=> In (A:=B) ef n x)).
  apply (e (Fpefct ef)); assumption.
Qed.

Lemma mapmu2Comp : fct2 mapmu2.
Proof.
  red.
  intros A B C f g r.
  generalize f g; clear f g.
  generalize B C; clear B C.
  generalize A r; clear A r.
  apply (mu2Ind (fun A r => forall  (B C : Set) (f : A -> B) (g : B -> C),
     mapmu2 (g o f) r = mapmu2 g (mapmu2 f r))).
  intros.
  clear H (* the IH *).
  do 3 rewrite mapmu2Red.
  apply (f_equal (fun x=>In (A:=C) ef n x)).
  apply (f2 (Fpefct ef)); assumption.
Qed.

Lemma mapmu2efct : efct mu2.
Proof.
  eapply mkefct.
  eexact mapmu2Ext.
  exact mapmu2Id.
  exact mapmu2Comp.
Defined.


(** the standard constructors for mu2 use mu2 as its own approximation *)

Definition InCan : F mu2 c_k1 mu2 :=
  fun A t => In mapmu2efct
                  (j:= fun _ x => x)(fun _ _ _ _ => refl_equal _) t.

(** the interactive way: *)
Definition InCan_inter : F mu2 c_k1 mu2.
Proof.
  intros.
  apply (In mapmu2efct (j:= fun _ x => x)).
  red.
  intros.
  reflexivity.
Defined.



(** the behaviour for canonical elements *)
Lemma MItRedCan : forall (G:k1)(s:forall X:k1, X c_k1 G ->
   F X c_k1 G)(A:Set)(t:F mu2 A),
   MIt s (InCan t) = s _ (MIt s) _ t.
Proof.
  reflexivity.
Qed.

Lemma mapmu2RedCan : forall (A:Set)(B:Set)(f:A->B)(t: F mu2 A),
             mapmu2 f (InCan t) =InCan(m (Fpefct mapmu2efct) f t).
Proof.
  reflexivity.
Qed.


(* now to Theorem 2 of the paper - formally, one should prove it for an
   abstract presentation of LNMIt instead of our definition within CIC
   with proof irrelevance *)

(* this here is a more general formulation of the extensionality property
   required in Theorem 2 in the paper; it is equivalent to that one in
   the situation we study *)
Definition polyExtsub (X1 X2 Y1 Y2:k1)(t: X1 c_k1 X2 -> Y1 c_k1 Y2) : Prop :=
  forall(f g: X1 c_k1 X2)(A:Set)(y: Y1 A), 
        (forall (A:Set)(x: X1 A), f A x = g A x) -> t f A y = t g A y.


(** MItRed already characterizes MIt s under an extensionality assumption
       for s: *)
Lemma MItUni: forall (G : k1)(s : forall X : k1, X c_k1 G -> F X c_k1 G)
       (aux: mu2 c_k1 G),
       (forall (X:k1), polyExtsub(s X)) ->
       (forall (A : Set)(X : k1)(ef: efct X)(j: X c_k1 mu2)(n:NAT j (m ef) mapmu2)(t:F X A),
     aux A (In ef n t) = s X (fun A => (aux A) o (j A)) A t) ->
      forall (A:Set)(r: mu2 A), aux A r = MIt s r.
Proof.
  intros G s aux sExt H.
  apply (mu2Ind (fun A r =>
   aux A r = MIt s r)).
  intros X ef j n IH A t.
  rewrite H.
  rewrite MItRed.
  apply sExt.
  clear A t.
  intros.
  unfold comp.
  apply IH.
Qed.

Section MIt.

(* now to Theorem 1 of the paper *)

Variable G:k1.
Variable s: forall X : k1, X c_k1 G -> F X c_k1 G.
Variable mG: mon G.
Variable smGpNAT : forall (X:k1)(h: X c_k1 G)(ef: efct X), 
    NAT h (m ef) mG -> NAT (s h) (m (Fpefct ef)) mG.

Lemma MItNAT : NAT (MIt s) mapmu2 mG.
Proof.
  red.
  intros A B f r.
  generalize B f; clear B f.
  generalize A r; clear A r.
  apply (mu2Ind (fun A r => forall (B : Set) (f : A -> B),
   MIt s (mapmu2 f r) = mG f (MIt s r))).
  intros X ef j n IH A t B f.
  rewrite mapmu2Red.
  do 2 rewrite MItRed.
  set (aux := fun A : Set => MIt s (A:=A) o j A).
  apply smGpNAT; try assumption.
  clear A t B f.
  red.
  intros.
  unfold aux.
  unfold comp.
  rewrite n.
  apply IH.
Qed.

End MIt.

End LNMItDef.

Section Bsh3.

(* Here comes just a minimal example: Bsh3 is seen as an instance, but
   nothing is programmed with it. In fact, the real example has been
   suppressed since it uses general results that are not explained in the
   paper and which, together with the example, make another 1200 lines. *)

Definition BshF3 : k2 :=
   fun X A => (unit + A * (X (X (X A))))%type.

Definition mon2 (F:k2) : Set :=
   forall (X Y:k1), X <_k1 Y -> F X <_k1 F Y.

Definition bshf3 : mon2 BshF3.
Proof.
  do 2 red.
  intros X Y h A B f r.
  elim r.
  intro.
  red. 
  exact (inl _ a).
  intros [a r'].
  red.
  apply inr.
  split.
  exact (f a).
  apply (h (X(X A))).
  apply (h (X A)).
  apply h.
  assumption.
  assumption.
Defined.


Definition bshf3_ : forall (X:k1)(m:mon X), mon (BshF3 X).
Proof.
  intros.
  exact (bshf3 m0).
Defined.


Definition bshf3pefct : pefct BshF3.
Proof.
  red.
  intros X ef.
  apply (mkefct (m:=bshf3_(m ef))).
(** extensionality *)
  red.
  intros.
  destruct r.
  reflexivity.
  destruct p.
  simpl.
  rewrite H.
  apply (f_equal (fun x:X(X(X B)) => inr unit (g a, x))).
  apply (e ef).
  intro.
  apply (e ef).
  intro.
  apply (e ef).
  assumption.
(** first functor law *)
  red.
  intros.
  unfold bshf3_.
  unfold bshf3.
  destruct x.
  reflexivity.
  destruct p.
  simpl.
  apply (f_equal (fun x : X(X(X A))=> inr unit (a, x))).
  replace (m ef (m ef (m ef (id (A:=A)))) x ) with
   ( m ef (id (A:= X(X A))) x).
Focus 2.
  apply (e ef).
  intro.
  replace (m ef (m ef (id (A:=A))) a0)
    with (m ef (id (A:=X A) )a0).
  rewrite (f1 ef).
  reflexivity.
  apply (e ef).
  intro.
  rewrite (f1 ef).
  reflexivity.
(**  back *)
  apply (f1 ef).
(** second functor law *)
  red.
  intros.
  destruct x.
  reflexivity.
  destruct p.
  simpl.
  unfold comp at 1.
  apply (f_equal (fun x:X(X(X C)) => inr unit (g(f a), x))).
  rewrite <- (f2 ef).
  apply (e ef).
  intro.
  unfold comp at 2.
  rewrite <- (f2 ef).
  apply (e ef).
  intro.
  rewrite (f2 ef).
  reflexivity.
Defined.

Definition Bsh3 := mu2 bshf3pefct.

Definition bnil3 : forall (A:Set), Bsh3 A:=
   fun A => InCan bshf3pefct _ (inl _ tt).

Definition bcons3 : forall (A:Set), A -> Bsh3(Bsh3(Bsh3 A)) -> Bsh3 A :=
  fun A a b => InCan bshf3pefct _ (inr _ (a,b)).

Definition mapBsh3 := mapmu2 (Fpefct:=bshf3pefct).

(** we now get the expected behaviour for mapBsh3 *)

Lemma mapBsh3Nil : forall (A B:Set)(f:A -> B),
    mapBsh3 f (bnil3 _)  = bnil3 _.
Proof.
  reflexivity.
Qed.


Lemma mapBsh3Cons : forall (A B:Set)(f:A -> B)(a:A)(b:Bsh3(Bsh3(Bsh3 A))),
    mapBsh3 f (bcons3 a b) = bcons3 (f a) (mapBsh3 (mapBsh3 (mapBsh3 f)) b).
Proof.
  reflexivity.
Qed.

End Bsh3.

End LNMIt.
