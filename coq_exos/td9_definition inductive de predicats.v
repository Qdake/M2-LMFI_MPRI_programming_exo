Module cloture_reflexive_transitive.

Parameter T:Type.

(* cloture reflexive transitive,  version 1 *)
Inductive clos1 (R : T -> T -> Prop) : T -> T -> Prop :=
| cl1_base : forall x y, R x y -> clos1 R x y
| cl1_refl : forall x, clos1 R x x
| cl1_trans : forall x y z, clos1 R x y -> clos1 R y z -> clos1 R x z.

(*
Print clos1_ind.

(*clos1_ind = 
fun (R P : T -> T -> Prop)
  (f : forall x y : T, R x y -> P x y)   (inclusion)
  (f0 : forall x : T, P x x)             (reflexivite)
  (f1 : forall x y z : T,                 
        clos1 R x y ->
        P x y -> clos1 R y z -> P y z -> P x z) =>
fix F (t t0 : T) (c : clos1 R t t0) {struct c} :
    P t t0 :=
  match c in (clos1 _ t1 t2) return (P t1 t2) with
  | cl1_base _ x y y0 => f x y y0
  | cl1_refl _ x => f0 x
  | cl1_trans _ x y z c0 c1 =>
      f1 x y z c0 (F x y c0) c1 (F y z c1)
  end
     : forall R P : T -> T -> Prop,
       (forall x y : T, R x y -> P x y) ->
       (forall x : T, P x x) ->
       (forall x y z : T,
        clos1 R x y ->
        P x y -> clos1 R y z -> P y z -> P x z) ->
       forall t t0 : T, clos1 R t t0 -> P t t0

Arguments clos1_ind (_ _ _ _ _)%function_scope *)
*)

Definition symm (R : T -> T -> Prop) := forall x y : T, R x y -> R y x.

Theorem if_R_sym_then_closR : forall R : T -> T -> Prop, 
  symm R -> symm (clos1 R).
Proof.
  intros R H.
  unfold symm in *. intros x y H1.
  elim H1.  
  - intros x0 y0 H2. apply cl1_base. apply H. assumption.
  - apply cl1_refl.
  - intros x0 y0 z0 H2 H3 H4 H5.
    apply (cl1_trans R z0 y0 x0); assumption.
Qed.

Theorem closR_idempotente : forall R:T->T->Prop, forall x y:T,clos1 (clos1 R) x y -> clos1 R x y.
Proof.
  intros R x y H.
  elim H.
  - trivial.
  - apply cl1_refl.
  - intros x0 y0 z0 H1 H2 H3 H4.
    eapply cl1_trans.
    + exact H2.
    + exact H4.
Qed.

(* cloture reflexive transitive ,   version 2*)

Inductive clos2 (R:T->T->Prop):T->T->Prop :=
| cl2_refl : forall x, clos2 R x x
| cl2_next : forall x y z, clos2 R x y -> R y z -> clos2 R x z.
Print clos2_ind.
(* forall R P : T -> T -> Prop,
       (forall x : T, P x x) ->
       (forall x y z : T, clos2 R x y -> P x y -> R y z -> P x z) ->
       forall t t0 : T, clos2 R t t0 -> P t t0
*)

(* pour tout R, pour tous x y, si x R y alors x (clos2 R) y *)
Theorem R_imp_clos2R : forall R:T->T->Prop, forall x y, R x y -> clos2 R x y.
Proof.
  intros. 
  apply (cl2_next R x x y).
  - constructor.
  - assumption.
Qed.

(* pour tout R, pour tous x y, si x (clos2 R) y alors x (clos1 R) y *)
Theorem clos2_imp_clos1 : forall R:T->T->Prop, forall x y, clos2 R x y -> clos1 R x y.
Proof.
  intros R x y.
  intro H. 
(*
1 subgoal
R : T -> T -> Prop
x, y : T
H : clos2 R x y
______________________________________(1/1)
clos1 R x y
*)
  elim H. 
(*
2 subgoals
R : T -> T -> Prop
x, y : T
H : clos2 R x y
______________________________________(1/2)
forall x0 : T, clos1 R x0 x0
______________________________________(2/2)
forall x0 y0 z : T,
clos2 R x0 y0 -> clos1 R x0 y0 -> R y0 z -> clos1 R x0 z
*)
  - apply cl1_refl.
  - intros. apply (cl1_trans R x0 y0 z).
    + assumption.
    + apply (cl1_base R y0 z). assumption.
Qed.

Print clos2.
(*
Inductive clos2 (R : T -> T -> Prop) : T -> T -> Prop :=
    cl2_refl : forall x : T, clos2 R x x
  | cl2_next : forall x y z : T,
               clos2 R x y -> R y z -> clos2 R x z
*)
(* clos2 R est une relation transitive *)
Theorem clos2_trans : forall R:T->T->Prop, 
        forall x y z, clos2 R x y -> clos2 R y z -> clos2 R x z.
Proof.
  intros R x y z xRy yRz.
  case yRz.
  
  
Admitted.
 
    
(* clos1 R -> clos2 R *)
Theorem clos1_imp_clos2 : forall R:T->T->Prop, forall x y:T,
                          clos1 R x y -> clos2 R x y.
Proof.
  intros R x y H.
  elim H.
  - intros. apply (cl2_next R x0 x0 y0).
    + constructor.
    + assumption.
  - intros. constructor.
  - intros. apply (clos2_trans R x0 y0 z);assumption.
Qed.


(* cloture reflexive-transitive version 3*)



End cloture_reflexive_transitive.


Module cours.

Lemma not_true_eq_false : ~ (true = false).
Proof.
  discriminate.
  Undo 1.
  intro H. 
  change ((fun b:bool => match b with |true => True | false => False end) false).
  rewrite <- H.
  trivial.
Qed.

(* predicate even number*)
Inductive even : nat -> Prop := 
| o_even : even 0
| plus_2_even : forall n : nat, even n -> even (S (S n)).

Theorem sum_even : forall n p : nat, even n -> even p -> even (n+p).
Proof.
  intros n. elim n.
  - auto.
  - intros n' Hrec p Heven_Sn' Heven_p.
    (*dead-end*)
  Restart.
  intros n p Heven_n.
  elim Heven_n.
  - trivial.
  - intros x Heven_x Hrec Heven_p; simpl.
    apply plus_2_even; auto.
Qed.

(* tactique : inversion *)
Theorem not_1_even : not(even 1).
Proof.
  (* failed attempt *)
  Print even_ind.
  (*forall P : nat -> Prop,
       P 0 ->
       (forall n : nat, even n -> P n -> P (S (S n))) ->
       forall n : nat, even n -> P n*)
  intros H.
  Undo.
  unfold not.
  intros H.
  inversion H.
  Undo 4.
  intro H.
  (* on cherche a transforme le goal en P 1 ou P est un predicat *)
  generalize (refl_equal 1).
  pattern 1 at 2.
  (*(fun n : nat => n = 1 -> False) 1*)
  induction H.
  - discriminate.
  - discriminate.
Qed.

Theorem plus_2_even_inv : forall n:nat, even (S (S n)) -> even n.
Proof.
  intros n H.
  inversion H. assumption.
Qed.

Require Import Omega.

Theorem ex_8_29_livre : forall n:nat, n >= 8 -> exists x y:nat, 5 * x + 3 * y = n.
Proof.
  induction n.
  - intros. assert (False). unfold ">=" in *. 
    + omega.
    + apply False_ind. assumption.
  - intros. Abort.

(* tactique : tauto  ,  intuition tac*)
Lemma t1 : forall A B:Prop, A /\ B -> A .
Proof.
  intros A B.
  auto. 
  tauto.
Qed.

Open Scope Z.
Lemma t2 : forall x y : Z, x <= y -> not(x<=y) -> False.
Proof.
  tauto.
Qed.

Open Scope nat.
Lemma example_intuition : forall n p q:nat, n <= p \/ n <= q -> n <= p \/ n <= S q.
Proof.
  auto. (* unchanged*)
  auto with arith. (* unchanged*)
  intuition auto with arith. (* "intuition." for "intuition auto with *"*)
Qed.


(* sorted list*)
Inductive sorted (A:Set) (R:A->A->Prop) : list A -> Prop :=
| sorted0 : sorted A R nil
| sorted1 : forall x:A, sorted A R (cons x nil)
| sorted2 : forall x y : A, forall l : list A,
            R x y -> sorted A R (cons y l) -> sorted A R (cons x (cons y l)).
 
(* last elt*)
Inductive last {A:Set} : A -> list A -> Prop:=
| last_base : forall a : A, last a (cons a nil)
| last_rec : forall l:list A, forall a, last a l -> forall x:A, last a (cons x l).

Fixpoint last_fun {A:Set} (l:list A): option A :=
match l with
| nil => None
| cons x nil => Some x
| cons _ ((cons x l') as l'')  => last_fun l''
end.

(*
Lemma lemma_aux_1 : forall A:Set, forall a b : A, last a (cons b nil) -> a = b.
Proof.
  intros. simpl in H.
  Print last_ind.
*)
 
Axiom a1 : forall A:Set, forall x x0:A, Some x = Some x0 -> x = x0.

Lemma test_last_fun : forall A:Set, forall l : list A, forall a:A,
  last_fun l = Some a -> last a l.
Proof.
  intros A l.
  elim l.
  - simpl. discriminate.
  - intros. induction l0.
    + simpl in *. 
      assert (a=a0). (* !! *)
      apply a1. assumption.
      rewrite H1. exact (last_base a0).
    + simpl. apply last_rec.
Admitted.
(* pattern tactic *)
Print Nmult_plus_distr_l.
(*
fun n m p : N => N.mul_add_distr_l p n m
     : forall n m p : N, (p * (n + m))%N = (p * n + p * m)%N
*)
Lemma test_pattern : forall x:nat, x + x + x + x = 5 * x.
Proof.
  intro x. rewrite <- Nmult_plus_distr_l.

End cours. 

