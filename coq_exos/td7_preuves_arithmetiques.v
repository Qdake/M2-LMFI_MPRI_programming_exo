Module Exos.

Lemma add_0_l : forall n, 0 + n = n.
Proof.
  intro. simpl. exact eq_refl. (* reflexivity*)  
  (* eq_refl: forall {A : Type} {x : A}, x = x  *)
Qed. 
(* simp marche parceque la definition de + est inductive en premier argument *)
Lemma add_succ_l : forall n m, S n + m = S (n + m).
Proof.
  intros n m. simpl. reflexivity. (* apply exact eq_refl. *)
Qed.

Require Import Nat Arith.

Search "add_ind".
(*
Lemma try_add_0_r : forall n, n + 0 = n.
Proof.
  intro n. (*reflexivity. (* sa ne marche pas *)*)
  Abort.
*)

Lemma add_0_r : forall n, n + 0 = n.
Proof.
  induction n.
  - reflexivity.
  - rewrite add_succ_l. rewrite IHn. reflexivity.
Qed.

Lemma add_0_r_prof : forall n, n + 0 = n.
Proof.
  simpl. (*nothing, internally n+... = ... match n with ... *)
  destruct n.
  - simpl. reflexivity.
  - simpl. f_equal. (* back to the initial statement, for n-1. *)
  Abort.
Lemma add_0_r_prof : forall n, n + 0 = n.
Proof.
  simpl. (*nothing, internally n+... = ... match n with ... *)
  induction n.
  - simpl. reflexivity.
  - simpl. f_equal. (* with induction n instead of destruct n,
                       now we have an extra IHn induction hypothesis *)
    apply IHn.
Qed.

(* conseil, prof : induction as soon as possible *)
(* conseil, prof : induction;simpl.*)
Lemma add_succ_r : forall n m, n + S m = S (n + m).
Proof.
  intros n m.
  induction n.
  - apply add_0_l.
  - rewrite add_succ_l. rewrite add_succ_l.
    rewrite IHn. reflexivity.
Qed.

Lemma add_succ_r_prof : forall n m, n + S m = S (n + m).
Proof.
  induction n;simpl.
  - reflexivity.
  - intros. 
    f_equal. (* or "rewrite IHn" instead of the f_equal *)
    apply IHn. 
Qed.

Print nat_ind.
Lemma add_assoc : forall n m p, (n + m) + p = n + (m + p).
Proof. 
  intros n m p. induction m.
  - simpl. rewrite add_0_r. apply eq_refl.
  - rewrite add_succ_l. rewrite add_succ_r in *.
    rewrite (add_succ_r n (m + p)). rewrite (add_succ_l (n + m) p).
    rewrite <- IHm.
    reflexivity.
Qed.

(* rewrite H1 H2*)
Lemma add_comm : forall n m, n + m = m + n.
Proof.
  induction n;simpl.
  - intro. rewrite add_0_r. reflexivity.
  - intro. rewrite add_succ_r. f_equal. apply IHn.
Qed.


(* Exercice 2 *)
Lemma mul_0_l : forall n, 0 * n = 0.
Proof.
  induction n;simpl;reflexivity.
Qed.

Lemma mul_succ_l : forall n m, S n * m = m + n * m.
Proof.
  induction n;simpl;reflexivity.
Qed.

Lemma mul_0_r : forall n, n * 0 = 0.
Proof.
  induction n;simpl. 
  - reflexivity.
  - exact IHn.
Qed.

(* rewrite H at k      kieme occurrence *)
Lemma mul_succ_r_prof : forall n m, n * S m = n + n * m.
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - f_equal. rewrite IHn at 1. 
Admitted.
(*  rewrite ?foo       rewrite as many as possible*)
Lemma mul_succ_r : forall n m, n * S m = n + n * m.
Proof.
  induction m;simpl.
  - rewrite mul_0_r,add_0_r. induction n.
    +  simpl. reflexivity.
    +  simpl. rewrite IHn. reflexivity.
  - induction n;simpl. 
    + reflexivity.
    + f_equal.
Admitted.

Lemma mul_distr : forall n m p, (n + m) * p = n * p + m * p.
Admitted.

Lemma mul_assoc_prof: forall n m p, (n * m) * p = n * (m * p).
Proof.
  induction n ; simpl ; intros.
  - reflexivity.
  - rewrite mul_distr. f_equal. apply IHn.
Qed.

Lemma mul_comm : forall n m, n * m = m * n.
Proof.
  (* just as for add, induction n is also ok here *)
  induction m ; simpl.   
  - apply mul_0_r.
  - rewrite mul_succ_r. rewrite IHm. reflexivity.
Qed.

(* extra exos *)
(*defining new tactics is possible by using the tactic language *)
Ltac induct n := induction n; simpl; intros.




Definition le (n m : nat) := exists p, n + p = m.
Infix "<=" := le : alt_le_scope. (* define a new scope.*)
Open Scope alt_le_scope.
Print Peano.le.
(*Inductive
le (n : nat) : nat -> Prop :=
    le_n : n <= n
  | le_S : forall m : nat,
           n <= m -> n <= S m*)

Lemma le_refl : forall n, n <= n.
Proof.
  intro. unfold "<=". (* unfold le *)
  exists 0. rewrite add_0_r. reflexivity.
Qed.

(*!!!! rewrite H <> rewrite <- H *)
Lemma le_trans_prof : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  unfold le.
  intros n m p (q,Hq) (r,Hr). (* (q,Hq) for introducing and then destructing *)
  exists (q+r). rewrite <- add_assoc.
  rewrite Hq, Hr. reflexivity.
Qed.
Lemma letrans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p. unfold "<=" in *. 
  intros H1 H2.
  destruct H1. destruct H2.
  exists (x+x0). rewrite <- add_assoc.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma add_more_0_prof : forall n m, n+m = n -> m = 0.
Admitted.

Lemma add_0_left_0 : forall n m, n + m = 0 -> n = 0.
  induction n ; simpl ;intros; auto.
Admitted.

Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
Proof.
  unfold le.
  intros n m (q,Hq) (r,Hr).
  rewrite <- Hq in Hr.
  rewrite add_assoc in Hr.
  assert (q+r = 0).
  { apply (add_more_0_prof n). assumption. }
  assert (q = 0).

Admitted.
(* Bonus proofs :*)

Lemma le_total : forall n m, n <= m \/ m <= n.
Proof.
  induction n;simpl;intros;unfold le.
  - left. exists m. simpl. reflexivity.
  - left.
Admitted.

Lemma le_succ : forall n m, n <= m -> n <= S m.
Admitted.

Print Peano.le. (* The one of Coq*)

Lemma le_equiv_prof : forall n m, n <= m <-> le n m.
Proof.
  split.
  -intros H; induction H. (*induction on a inductive proof !*)
Admitted.

End Exos.

Module cours2.
(*Unset Printing Notations.
Print test.
*)
(* logical constants : True *)
Print True.
Check I.
Lemma obvious : True.
Proof.
  constructor.    (* chercher dans l'ensemble des constructeur *)
  (*exact I.*)
  (* trivial *)
  Show Proof.
Qed.

Lemma attempt : True -> True.
Proof.
  intros H.
  destruct H.
  Show Proof. (* True is never used apart proofs in drinker lemma*)
  exact I.
Qed.

Print False.
Inductive FalseBis : Prop := .
(* def de False: 
  Inductive False : Prop := . *)
Print False_rect.
  (* elimination of False : a match with no branches providing anything you want *)

Lemma false_elim : False -> 0 = 1.
Proof.
  intro H.
  destruct H.
  (*apply False_ind.
  assumption.*)
  Show Proof.
Qed.


(* Negation : ~A shortcut A -> False *)
 
(* Connectors : /\ and \/ *)
Print prod.  (* or * in the type_scope *)
Check (0,1).

Print and.

Print and.
Inductive and (A B : Prop) : Prop := 
  conj : A -> B -> and A B.
Print and_ind.

(* and is inversible *)
Lemma conj_intro : True /\ True.
Proof.
  split.
  Show Proof.
  trivial.
  trivial.
Qed.

Lemma conj_intro_2 : True /\ True.
Proof.
  constructor.
  Show Proof.
  trivial.
  trivial.
Qed.

Lemma conj_sum (A B : Prop) : A /\ B -> B /\ A.
Proof.
  intros H.
  destruct H. Show Proof.
  auto. Show Proof.
Qed.

(* disjonction : two constructors ! *)
Print or.
Check or.
Check or_introl. (* forall A B : Prop, A -> A \/ B *)
Check or_intror. (* forall A B : Prop, A -> A \/ B *)
Fail Check or_rect.  (* no elimination on Type :
                        usually, no proofs can influence a program *)
(* the Prop world normally doesn't impact the program world
    : proofs can be eliminated only to build proofs.*)

Fail Definition evade (p : True \/ True ) : bool :=
  match p with
  | or_introl _ => true
  | or_intror _ => false
  end. (* Refused *)

Check or_ind. 
Print or_ind. (* a match on the proof of (A\/B) *)

(* the "left" tactic : apply the or_introl constructor *)
(*      right                    or_intror    *)
(*      destruct  on a H: A\/B hypothesis : match H with ... *)
(* iff:    A <-> shortcut for (A -> B) /\ (B -> A) *)

Lemma or_sym A B : A\/B -> B\/A.
Proof.
  intros [a|b]. (* same as intro H. destruct H.*)
  constructor 2. assumption.
(*  constructor. trivial. (* bad luck : tactic constructor takes the first that fits *)*)
  constructor 1. assumption.
Qed.
(* exists *)  (* forall is primitif *)
                (* exists is an inductive type *)

About "/\".
Locate "/\".
Locate "exists".
Print ex.

(* exists x:A, P x <-----> ex A P *)
Inductive
ex_1 (A : Type) (P : A -> Prop): Prop :=
 ex_1_intro : forall (x : A) (p : P x),ex_1 A P.
Print and. (* similarity *)
(* Recall : Logical pair :
Inductive and (A B : Prop) : Prop :=
    conj : A -> B -> and A B.   *)

(* in fact, ex is same, with a dependency on B (which becomes P ... )
    ex is a dependent pair (sigma type)
    : it groups a witness x and a proof of the property of x

    introduce : tactics called "exists ... " : internally apply of ex_intro
                * instead of "eixsts" you can try econstructor 
    elimination : 

*)
Lemma test_ex : exists n:nat, n = n.
Proof.
  eexists. (* econstructor.*)
  reflexivity.
  Abort.  

(* eq *)
Print eq.  (* it's an inductive type *)
(* !! syntactic equality : only x is equal to x *)
(*Inductive eq_2 (A:Type)(x:A) : A->Prop := eq_refl : eq_2 A x x.*)
(* !!! constructor is the reflexivity rule.  tactic "reflexivity" *)

Lemma compute_equal : 2 + 2 = 4.
Proof.
  exact eq_refl. 
  (*simpl. (* no impact on the proof term *) *)
Qed.
Lemma example : 2 + 2 = 4.
Proof. (* in coq, most of the time we're modulo computation : 
          2 + 2 just the same as 4 *)
  simpl. (* force a computation *)
  reflexivity.
  Set Printing Implicit.
  Show Proof.
Qed.
(* different style *)
Require Import Arith.
Lemma example_with_peano : 2+2 = 4.
Proof.
   rewrite Nat.add_succ_l.
     rewrite Nat.add_succ_l.
   rewrite Nat.add_succ_r.
   rewrite Nat.add_succ_r.
   reflexivity.
Qed.
Print example_with_peano.
Print example.
(* ils sont differents: 
     PA: function logique ( symbole, axiome ).
     en coq : function est definie par fixpoint, est un programme, elle calcule *)
(* elimination eq *)
Check eq_ind.
(* The leibniz principle, or the rewrite principle :
  eq_ind : forall (A :Type)(x:A) (P:A->Prop),P x -> 
      forall y: A, x=y-> P y. *)
(*match on a equality is a form of rewrite
  the rewrite tactic proceed by a match on the equality *)
Lemma eq_sym A (x y : A) : x = y -> y = x.
Proof.
  intro H. destruct H. reflexivity.
Qed. 

(* nat and induction *)
Print nat.
Check nat_ind.
Print nat_ind.
Lemma test_induction : forall n:nat, n = n.
Proof.
  induction n.
  Abort.
(* sig and sumbol *)
Print sig.
Print sigT.
(*Inductive sig (A : Type) (P : A -> Prop)
  : Type :=
    exist : forall x : A,
            P x -> {x : A | P x}
*)

Print sumbool.



End cours2.
