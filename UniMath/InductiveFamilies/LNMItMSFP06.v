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
  intros. (* why do we need this line? *)
  apply idpath.
Defined.


(*
Definition ext (X Y:k1)(h: X <_k1 Y): UU :=
  forall (A B:k0)(f g: A -> B), 
        (forall (a:A), f a = g a) -> forall (r: X A), h _ _ f r = h _ _ g r.
*)


Definition fct1 (X:k1)(m: mon X) : UU :=
  forall (A:k0)(x:X A), m _ _ (@id A) x = x.

Definition fct1_p (X:k1)(m: mon X) : UU :=
  forall (A:k0)(x:X A), ∥m _ _ (@id A) x = x∥.


Definition fct2 (X:k1)(m: mon X) : UU :=
 forall (A B C:k0)(f:A -> B)(g:B -> C)(x:X A),
       m _ _ (g o f) x = m _ _ g (m _ _ f x).

Definition fct2_p (X:k1)(m: mon X) : UU :=
 forall (A B C:k0)(f:A -> B)(g:B -> C)(x:X A),
                 ∥m _ _ (g o f) x = m _ _ g (m _ _ f x)∥.



(** pack up the good properties of the approximation *)
Record efct (X:k1) : UU := mkefct
  { m : mon X;
(*     e : ext m; *)
     f1 : fct1_p m;
     f2 : fct2_p m }.
(* will later be turned into a nested Sigma type *)

Definition pefct (F:k2) : UU :=
  forall (X:k1), efct X -> efct (F X).


(** natural transformations from (X,mX) to (Y,mY) *)
Definition NAT(X Y:k1)(j:X c_k1 Y)(mX:mon X)(mY:mon Y) : k0 :=
  forall (A B:k0)(f:A -> B)(t:X A), j B (mX A B f t) = mY _ _ f (j A t).

Definition NAT_p(X Y:k1)(j:X c_k1 Y)(mX:mon X)(mY:mon Y) : hProp := ∥NAT j mX mY∥.


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
          (it:MItPretype G')(j: G c_k1 G')(n:NAT_p j (m ef) m'), F G A.

Definition inE : forall (G:k1)(ef:efct G)(G':k1)(m':mon G')
          (it:MItPretype G')(j: G c_k1 G'), NAT_p j (m ef) m' ->
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

Definition mu2E_n (A:k0)(t: mu2E A): NAT_p (mu2E_j t) (m (mu2E_ef t)) (mu2E_m' t).
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
  intros.
  apply idpath.
Defined.

(** single out the good elements of mu2E A *)
(* in the paper muEcheck is called chk_{mu^+F}, inEcheck is called Inchk *)
(* the following elements of a non-strictly positive inductive definition will have to be justified by other means *)
Parameter mu2Echeck : forall (A:k0), mu2E A -> k0.

Parameter inEcheck : forall (G:k1)(ef:efct G)(j: G c_k1 mu2E)(n: NAT_p j (m ef) mapmu2E),
       (forall (A:k0)(t:G A), ishinh_UU (mu2Echeck (j A t))) ->
     forall (A:k0)(t:F G A),
       mu2Echeck (inE ef MItE j n t).
(* note that [ishinh_UU] appears freshly in this definition and is responsible for it being non-strictly positive *)
(* Check mu2Echeck. *)
Implicit Arguments inEcheck [G A].
(* Check inEcheck. *)

(* we obtained the induction scheme earlier in the following manner:
Scheme mu2Echeck_indk0 := Minimality for mu2Echeck Sort Type. (* Type should be replaced by k0, but this is illegal *)
*)

(* the induction principle that is mentioned right after the inductive definition in the paper - adapted to [ishinh_UU] *)
Parameter mu2Echeck_indk0 : forall P : forall A : k0, mu2E A -> k0,
       (forall (G : k1) (ef : efct G) (j : G c_k1 mu2E)
          (n : NAT_p j (m ef) mapmu2E),
        (forall (A : k0) (t : G A) (R: hProp), (mu2Echeck (j A t) -> P A (j A t) -> R) -> R) ->
        forall (A : k0) (t : F G A),
        P A
          (inE ef MItE j n t)) ->
       forall (A : k0) (r : mu2E A), mu2Echeck r -> P A r.

(* a computation rule - the main achievement is that the right-hand side has the same type as the left-hand side *)
Parameter mu2Echeck_indk0_comp : forall (P : forall A : k0, mu2E A -> k0)
  (s: forall (G : k1) (ef : efct G) (j : G c_k1 mu2E)
          (n : NAT_p j (m ef) mapmu2E),
        (forall (A : k0) (t : G A) (R: hProp), (mu2Echeck (j A t) -> P A (j A t) -> R) -> R) ->
        forall (A : k0) (t : F G A),
        P A
          (inE ef MItE j n t))
       (G:k1)(ef:efct G)(j: G c_k1 mu2E)(n: NAT_p j (m ef) mapmu2E)
       (rec: forall (A:k0)(t:G A), ishinh_UU (mu2Echeck (j A t)))(A:k0)(t:F G A),
   (mu2Echeck_indk0 P s (inEcheck ef j n rec t) : P A (inE ef MItE j n t)) = 
       s G ef j n
       (fun (A':k0)(t':G A')(R: hProp)(Hyp: mu2Echeck (j A' t') -> P A' (j A' t') -> R) =>
          rec A' t' R (fun z:mu2Echeck (j A' t') => Hyp z (mu2Echeck_indk0 P s z))) A t.
(* this is a slightly polished instance of the generic rule for primitive recursion for arbitrary positive inductive families *)


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
  simpl in H.
  apply (hinhfun (X := mu2Echeck r')).
Focus 2.
  assumption.
Unfocused.
  clear H.
  generalize r'.
  clear r r'.
  intros r Hyp.
  revert B f.
  revert Hyp.
  revert A r.
  apply (mu2Echeck_indk0 (fun (A:k0)(r:mu2E A) => forall (B : k0) (f : A → B), mu2Echeck (mapmu2E f r))).
  intros G ef j n IH A t B f.
  apply inEcheck.
  intros A' t' R Hyp.
  apply (IH A' t').
  intros H1 H2.
  apply Hyp.
  exact H1.
Defined.

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

Lemma mu2pirr_cor : forall (A:k0)(r:mu2 A), r = pi1 r,,pi2 r.
Proof.
  intros.
  apply mu2pirr.
  apply idpath.
Defined.

(** first projection commutes with the maps *)
Lemma pi1mapmu2 : forall (A B:k0)(f:A->B)(r:mu2 A),
  pi1 (mapmu2 f r) = mapmu2E f (pi1 r).
Proof.
  intros.
  apply idpath. (* does this use eta expansion for pairs? *)
Defined.

(** the type of the future datatype constructor In *)
Definition InType : UU := 
    forall (G:k1)(ef:efct G)(j: G c_k1 mu2), NAT_p j (m ef) mapmu2 ->
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

Lemma pi1'pNAT_p : forall (G:k1)(m:mon G)(j: G c_k1 mu2),
  NAT_p j m mapmu2 -> NAT_p (pi1' j) m mapmu2E.
Proof.
  intros G m' j.
  apply hinhfun.
  apply pi1'pNAT.
Defined.

Lemma pi2' : forall(G:k1)(j: G c_k1 mu2)(A:k0)(t: G A),
             mu2Echeck_p (pi1' j A t).
Proof.
  intros.
  exact (pi2 (j A t)).
Defined.


(* an aside on prop. truncation *)
Definition hinh_univ_elim {G:k1}{ X: forall (A:k0)(t:G A), UU }: ∥ forall (A:k0)(t:G A), X A t∥ -> forall (A:k0)(t:G A), ∥X A t∥.
Proof.
  intros Hyp A t P xp.
  apply Hyp.
  intro Hyp1.
  apply xp.
  apply Hyp1.
Defined.
(* no hope for the other direction: see Lemma 3.8.5 in the HoTT book (fst ed. 2013) *)

(* what I would have liked to prove before incorporating truncation into the definition of inEcheck
Definition hinhfun_extended {G:k1}{ X: forall (A:k0)(t:G A), UU } { Y : UU }( f : (forall (A:k0)(t:G A), X A t) -> Y ) : (forall (A:k0)(t:G A), ∥X A t∥) -> ∥ Y ∥ .
Proof.
  intro isx.
  intros P yp. (* I do not see anything to pursue the proof in structural ways *)
*)

(** in is reserved for Coq, so the datatype constructor will be In *)
Definition In : InType.
Proof.
  intros G ef j n A t.
  eexists (inE(A:=A)(m':=mapmu2E) ef MItE (pi1' j) (pi1'pNAT_p n) t).
  unfold pi1'.
  change   (fun (A0 : k0) (H : G A0) => pi1 (j A0 H)) with
  (fun A0 H => (fun A0 H => pi1 (j A0 H)) A0 H).
  apply hinhpr.
  apply inEcheck.
  exact (pi2' j).
Defined.


(** the iterative behaviour of map comes from the definition of In *)
Lemma mapmu2Red : forall (A:k0)(G:k1)(ef:efct G)(j: G c_k1 mu2)
    (n: NAT_p j (m ef) mapmu2)(t: F G A)(B:k0)(f:A->B), 
             mapmu2 f (In ef n t) = In ef n (m (Fpefct ef) f t).
Proof.
(* we would have liked the following proof that worked in the MSFP'06 formulation: 
  reflexivity.
*)
  intros A G ef j n t B f.
  apply mu2pirr.
  apply idpath.
Defined.


Lemma MItRed : forall (G : k1)
  (s : forall X : k1, X c_k1 G -> F X c_k1 G)(X : k1)(ef:efct X)(j: X c_k1 mu2)
      (n: NAT_p j (m ef) mapmu2)(A:k0)(t:F X A),
     MIt s (In ef n t) = s X (fun A => (MIt s (A:=A)) o (j A)) A t.
Proof.
  intros.
  apply idpath.
Defined.


(** our desired induction principle, now into [hProp] *)
Definition mu2IndType : k0 :=
  forall P : (forall A : k0, mu2 A -> hProp),
       (forall (X : k1)(ef:efct X)(j : X c_k1 mu2)(n: NAT_p j (m ef) mapmu2),
          (forall (A : k0) (x : X A), P A (j A x)) ->
        forall (A:k0)(t : F X A), P A (In ef n t)) ->
    forall (A : k0) (r : mu2 A), P A r.

(* now comes the more refined induction principle that is used at the end of
   the proof of Theorem 3 in the paper *)
(* we obtained the induction scheme earlier in the following manner:
Scheme mu2EcheckInd := Induction for mu2Echeck Sort Type. (* ought to be k0, but this is illegal *)
*)
Parameter mu2EcheckInd : 
      forall P : forall (A : k0) (t : mu2E A), mu2Echeck t -> k0,
       (forall (G : k1) (ef : efct G) (j : G c_k1 mu2E)
          (n : NAT_p j (m ef) mapmu2E)
          (p : forall (A : k0) (t : G A), ishinh_UU (mu2Echeck (j A t))),
(*
        (forall (A : k0) (t : G A), P A (j A t) (p A t)) ->
*)
          (forall (A : k0) (t : G A) (R: hProp), (forall p:mu2Echeck (j A t), P A (j A t) p -> R) -> R) ->

        forall (A : k0) (t : F G A),
        P A
          (inE ef MItE j n t)
          (inEcheck ef j n p t)) ->
       forall (A : k0) (t : mu2E A) (p : mu2Echeck t), P A t p.
(* the principle has been edited by hand and may not be justified *)


(** uniqueness of naturality proofs *)
Lemma UNP : forall(X Y:k1)(j:X c_k1 Y)(mX:mon X)(mY:mon Y)
    (n1 n2: NAT_p j mX mY), n1 = n2.
Proof.
  intros.
  assert (H : isaprop (NAT_p j mX mY)).
  apply isapropishinh.
  apply H.
Defined.

(* a dependent version of hinhuniv (called induction principle in Exercise 3.17 in the HoTT book (fst ed. 2013) - according to p.147 l.7 "not especially useful" *)
Lemma hinhuniv_dep: forall (X:k0)(P:∥ X∥->hProp), (forall x:X, P(hinhpr x)) -> forall x:∥ X∥, P x.
Proof.
  intros X P Hyp x.
  apply hinhunivcor1.
  intros R xp.
  apply x.
  intro x'.
  assert (Hyp_inst := Hyp x').
  apply xp.
  assert (H: x = hinhpr x').
  apply isapropishinh.
  rewrite H.
  exact Hyp_inst.
Defined.

(* [hinhuniv] from the library is indeed a special instance of the dependent version *)
Corollary hinhuniv_cor { X : UU } { P : hProp } ( f : X -> P ) ( wit : ∥ X ∥ ) : P.
Proof.
  apply (hinhuniv_dep (fun x:∥ X∥ => P)).
  assumption.
  assumption.
Defined.

(* this is the justification of muFInd in the paper *)
Lemma mu2Ind : mu2IndType.
Proof.
  intros P s A r.
  set (r' := pi1 r).
  set (H := pi2 r).
  rewrite (mu2pirr_cor r).
  change (P A (mu2cons r' H)).
  assert (new: forall (r':mu2E A)(H: mu2Echeck_p r'), P A (mu2cons r' H)).
  (* is there no quicker way to deconnect r' and H from r? *)
Focus 2.
  apply new.
Unfocused.
  clear r r' H.
  revert A.
(* the idea is now that since P lives in hProp, it does not matter that H is only in the truncation *)
  assert (new: forall (A : k0) (r' : mu2E A) (H0 : mu2Echeck r'), P A (mu2cons r' (hinhpr H0))).
Focus 2.
  intros A r'.
  apply hinhuniv_dep.
  intros H1.
  exact (new A r' H1).
Unfocused.
  apply (mu2EcheckInd (fun (A:k0)(r':mu2E A)(H0: mu2Echeck r') => P A (mu2cons r' (hinhpr H0)))).
  intros G ef j n p rec A t.
  set (j':=fun (A : k0) (t : G A) => mu2cons(j A t)(p A t)).
  assert (n1 : NAT_p (Y:=mu2) j' (m ef) mapmu2).
  - apply (hinhfun (X:=NAT j (m ef) mapmu2E)).
    + intros n_NAT.
      red. 
      clear A t. 
      intros.
      apply mu2pirr.
      simpl.
      apply n_NAT.
    + exact n.
  - set (s_inst := s G ef j' n1).
    assert (Hyp : forall (A:k0)(x:G A), P A (j' A x)).
    + intros A' x.
      apply (rec A' x).
      intros p0 H.
      assert (Heq : j' A' x = mu2cons (j A' x) (hinhpr p0)).
      * apply mu2pirr.
        apply idpath.
      * rewrite Heq.
        exact H.
    + set (s_inst2 := s_inst Hyp A t).
      assert (Heq: mu2cons (inE ef MItE j n t) (hinhpr (inEcheck ef j n p t)) = In ef n1 t).
      * apply mu2pirr.
        simpl.
        (* assert (Heq1: j = pi1' j').
        --  apply idpath. *)
        assert (Heqn: n = pi1'pNAT_p n1).
        -- apply UNP.
        -- rewrite Heqn.
           apply idpath.
      * rewrite Heq.
        exact s_inst2.
Defined.

(* Search (∥ _∥). *)


(* these constitute parts of the proof of Theorem 4 *)

Lemma mapmu2Id: fct1_p mapmu2.
Proof.
  red.
  apply (mu2Ind (fun A r => ∥mapmu2 (id(A:=A)) r = r∥)).
  intros G ef j n H A t.
  clear H (* the IH *).
  set (f1_inst := f1 (Fpefct ef) A (x:=t)).
  apply (hinhfun (X:=m (Fpefct ef) (id (A:=A)) t = t)).
Focus 2.
  exact f1_inst.
Unfocused.
  intro f1_inst_eq.
  rewrite mapmu2Red.
  rewrite f1_inst_eq.
  apply idpath.
Defined.

(*
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
*)

Lemma mapmu2Comp : fct2_p mapmu2.
Proof.
  red.
  intros A B C f g r.
  generalize f g; clear f g.
  generalize B C; clear B C.
  generalize A r; clear A r.
  apply (mu2Ind (fun A r => ∀(B C : k0) (f : A -> B) (g : B -> C),
       ∥mapmu2 (g o f) r = mapmu2 g (mapmu2 f r)∥)).
  intros G ef j n H A t B C f g.
  clear H (* the IH *).
  do 3 rewrite mapmu2Red.
  set (f2_inst := f2 (Fpefct ef) f g t).
  apply (hinhfun (X:=m (Fpefct ef) (g o f) t = m (Fpefct ef) g (m (Fpefct ef) f t))).
Focus 2.
  exact f2_inst.
Unfocused.
  intro f2_inst_eq.
  rewrite f2_inst_eq.
  apply idpath.
Defined.

Lemma mapmu2efct : efct mu2.
Proof.
  eapply mkefct.
(*  eexact mapmu2Ext. *)
  exact mapmu2Id.
  exact mapmu2Comp.
Defined.

(** the standard constructors for mu2 use mu2 as its own approximation *)

Definition InCan : F mu2 c_k1 mu2.
Proof.
  intros.
  apply (In mapmu2efct (j:= fun _ x => x)).
  apply hinhpr.
  red; intros.
  apply idpath.
Defined.


(** the behaviour for canonical elements *)
Lemma MItRedCan : forall (G:k1)(s:forall X:k1, X c_k1 G ->
   F X c_k1 G)(A:UU)(t:F mu2 A),
   MIt s (InCan t) = s _ (MIt s) _ t.
Proof.
  intros.
  apply idpath.
Qed.

Lemma mapmu2RedCan : forall (A B:UU)(f:A->B)(t: F mu2 A),
             mapmu2 f (InCan t) = InCan(m (Fpefct mapmu2efct) f t).
Proof.
  intros.
  unfold InCan at 1.
  rewrite mapmu2Red.
  apply idpath.
Qed.


(* now to Theorem 2 of the paper - formally, one should prove it for an
   abstract presentation of LNMIt instead of our definition within CIC
   with proof irrelevance *)

(* this here is a more general formulation of the extensionality property
   required in Theorem 2 in the paper; it is equivalent to that one in
   the situation we study; beware: now with questionable truncations *)

Definition polyExtsub (X1 X2 Y1 Y2:k1)(t: X1 c_k1 X2 -> Y1 c_k1 Y2) : UU :=
  forall(f g: X1 c_k1 X2)(A:UU)(y: Y1 A), 
        (forall (A:UU)(x: X1 A), ∥f A x = g A x∥) -> ∥t f A y = t g A y∥.

(** MItRed already characterizes MIt s under an extensionality assumption
       for s: *)
Lemma MItUni: forall (G : k1)(s : forall X : k1, X c_k1 G -> F X c_k1 G)
       (aux: mu2 c_k1 G),
       (forall (X:k1), polyExtsub(s X)) ->
       (forall (A : UU)(X : k1)(ef: efct X)(j: X c_k1 mu2)(n:NAT_p j (m ef) mapmu2)(t:F X A),
     aux A (In ef n t) = s X (fun A => (aux A) o (j A)) A t) ->
      forall (A:UU)(r: mu2 A), ∥aux A r = MIt s r∥.
Proof.
  intros G s aux sExt H.
  apply (mu2Ind (fun A r => ∥aux A r = MIt s r∥)).
  intros X ef j n IH A t.
  rewrite H.
  rewrite MItRed.
  apply sExt.
  clear A t.
  intros.
  unfold comp.
  apply IH.
Defined.

Section MIt.

(* now to Theorem 1 of the paper *)

Variable G:k1.
Variable s: forall X : k1, X c_k1 G -> F X c_k1 G.
Variable mG: mon G.

Definition NAT_p_weak (X Y:k1)(j:X c_k1 Y)(mX:mon X)(mY:mon Y) : k0 :=
  forall (A B:k0)(f:A -> B)(t:X A), ∥j B (mX A B f t) = mY _ _ f (j A t)∥.

Variable smGpNAT : forall (X:k1)(h: X c_k1 G)(ef: efct X), 
    NAT_p_weak h (m ef) mG -> NAT_p_weak (s h) (m (Fpefct ef)) mG.

Lemma MItNAT : NAT_p_weak (MIt s) mapmu2 mG.
Proof.
  red.
  intros A B f r.
  generalize B f; clear B f.
  generalize A r; clear A r.
  apply (mu2Ind (fun A r => ∀ (B : UU) (f : A -> B),
     ∥MIt s (mapmu2 f r) = mG f (MIt s r)∥ )).
  intros X ef j n IH A t B f.
  rewrite mapmu2Red.
  do 2 rewrite MItRed.
  set (aux := fun A : UU => MIt s (A:=A) o j A).
  apply smGpNAT; try assumption.
  clear A t B f.
  red.
  intros.
  unfold aux.
  unfold comp.
  revert n.
  apply hinhuniv.
  intro n_eq.
  rewrite n_eq.
  apply IH.
Defined.

End MIt.

End LNMItDef.

Section Bsh3.

(* Here comes just a minimal example: Bsh3 is seen as an instance, but
   nothing is programmed with it. In fact, the real example has been
   suppressed since it uses general results that are not explained in the
   paper and which, together with the example, make another 1200 lines. *)

Definition BshF3 : k2 :=
   fun X A => coprod unit (A * (X (X (X A)))).

Definition mon2 (F:k2) : UU :=
   forall (X Y:k1), X <_k1 Y -> F X <_k1 F Y.

Definition bshf3 : mon2 BshF3.
Proof.
  do 2 red.
  intros X Y h A B f r.
  elim r.
  intro a.
  red.
  exact (inl a).
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

(* END OF PROPER WORK ON THE FILE *)


Definition bshf3pefct : pefct BshF3.
Proof.
  red.
  intros X ef.
  apply (mkefct (m:=bshf3_(m ef))).
(*
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
*)
(** first functor law *)
  red.
  intros.
  unfold bshf3_.
  unfold bshf3.
  destruct x.
  apply hinhpr.
  apply idpath.
  destruct p.
  destruct ef as [m f1 f2].
  simpl.
  apply (hinhfun (X:=fct1 m)).
  + intros f1_eq.
    unfold id at 1.
    assert (eq1 : m (X (X A)) (X (X A)) (m (X A) (X A) (m A A (id (A:=A)))) x = m _ _ (id (A:= X(X A))) x).
    Focus 2.
    rewrite eq1.
    rewrite f1_eq.
    apply idpath.

    assert (eq2 : m (X A) (X A) (m A A (id (A:=A))) = id (A:=X (X A))).
    Focus 2.
    rewrite eq2.
    apply idpath.

    apply funextfun.
    clear a x.
    intros x.
    assert (eq3 : m A A (id (A:=A)) = id (A:=X A)).
    - apply funextfun.
      clear x.
      intro x.
      apply f1_eq.
    - rewrite eq3.
      apply f1_eq.
(* we now ought to prove ∥ fct1 m ∥ !! *)
Admitted.

(*
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
*)

Definition Bsh3 := mu2 BshF3 (* bshf3pefct *).

Definition bnil3 : forall (A:UU), Bsh3 A:=
   fun A => InCan bshf3pefct _ (inl tt).

Definition bcons3 : forall (A:UU), A -> Bsh3(Bsh3(Bsh3 A)) -> Bsh3 A :=
  fun A a b => InCan bshf3pefct _ (inr (a,b)).

Definition mapBsh3 := mapmu2 bshf3pefct.

(** we now get the expected behaviour for mapBsh3 *)

Lemma mapBsh3Nil : forall (A B:UU)(f:A -> B),
    mapBsh3 f (bnil3 _)  = bnil3 _.
Proof.
  intros.
  unfold bnil3.
  unfold mapBsh3.
  rewrite mapmu2RedCan.
  (* we are missing the definition of bshf3pefct *)
Abort.


Lemma mapBsh3Cons : forall (A B:UU)(f:A -> B)(a:A)(b:Bsh3(Bsh3(Bsh3 A))),
    mapBsh3 f (bcons3 a b) = bcons3 (f a) (mapBsh3 (mapBsh3 (mapBsh3 f)) b).
Proof.
  (* we are missing the definition of bshf3pefct *)
Abort.


End Bsh3.

End LNMIt.
