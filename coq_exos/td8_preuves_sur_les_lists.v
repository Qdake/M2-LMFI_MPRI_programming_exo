Require Import List Arith.
Import ListNotations.
Set Implicit Arguments.

(*
(* definition des lists polymorphes dans la bibliotheque *)
Print list_ind.
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A-> list A.
*)



Print app.
(*
app = fun A : Type =>
fix app (l m : list A) {struct l} :
    list A :=
  match l with
  | [] => m
  | a :: l1 => a :: app l1 m
  end
     : forall A : Type,
       list A -> list A -> list A
*)

Lemma app_nil_l : forall A:Type, forall l:list A, nil ++ l = l.
Proof.
  intros A l. unfold app. reflexivity.
Qed.

Lemma app_nil_r : forall A:Type, forall l:list A, l ++ nil = l.
Proof.
  unfold app;induction l;simpl;intros.
  - reflexivity.
  - rewrite <- IHl at 2. reflexivity.
Qed.

Lemma app_assoc : forall A:Type, forall l1 l2 l3:list A, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  induction l2 ; simpl ; intros. 
  - (* a = b avec a = l1 ++ []  et b = l1 
       P(x) : x ++ l3 = l1 ++ l3   
       on a P(a), rewrite -> app_nil_r nous donne P(b), i.e. P(l1)  *)
    rewrite -> app_nil_r.  (* -> for "left to right" rewritting
                                 donc P(a) est la partie à gauche *)
                            (* <- for "right to left" rewritting *)
    Undo 1. (* undo k.  to undo k steps *)   
    rewrite <- (app_nil_r l1) at 2.   (* at k pour k-ieme occurrence *)                        
    reflexivity.

  - induction l1;simpl;intros.
    + reflexivity.
    + f_equal. apply IHl1.
   Abort.


Fixpoint eq_list {A:Type} (l1 l2:list A) : Prop :=
match l1,l2 with
| [],[] => True
| _::_,[] | [],_::_ => False
| _::l1, _::l2 => eq_list l1 l2
end.
Infix "=" := eq_list : alt_eq_list_scope. (* define a new scope.*)

Open Scope alt_eq_list_scope.


Lemma app_assoc_aux : forall A:Type, forall l1 l2, forall x:A, 
                      (x :: l1) ++ l2 = x :: (l1 ++ l2).
Proof.
    induction l1;intros.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma app_assoc : forall A:Type, forall l1 l2 l3:list A, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  induction l1;intros.
  - simpl. reflexivity.
  - rewrite app_assoc_aux. rewrite app_assoc_aux. rewrite app_assoc_aux.
    f_equal. apply IHl1.
Qed.



(* longueur de la list *)
Definition length {A:Type} : list A -> nat :=
  fix length l :=
  match l with
  | [] => 0
  | _::l' => S (length l')
  end.

Lemma length_app_x : forall {A:Type} (l:list A) (x:A), length (x::l) = S (length l).
  induction l;intros.
  - simpl. reflexivity.
  - unfold length. reflexivity.
Qed.

Theorem length_split : forall {A:Type},forall l1 l2 : list A, 
      length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1;simpl;intros.
  - reflexivity.
  - rewrite IHl1. reflexivity.
Qed.

(* Retournement *)
Fixpoint rev_append {A:Type} (l1 l2:list A) :=
  match l1 with 
  |[] => l2
  |x::l1' => rev_append l1' (x::l2)
  end.

Definition rev {A:Type} (l:list A):= 
    rev_append l [].




Lemma rev_append_x_l: forall A:Type, forall l1 l2:list A, forall x:A, rev_append (x::l1) l2 = rev_append l1 (x::l2).
Proof.
  induction l1;simpl;intros.
  - reflexivity.
  - reflexivity.
Qed.

Lemma append_nil_l : forall {A:Type}, forall l:list A, [] ++ l = l.
Proof.
  reflexivity.
Qed.

Lemma length_rev_append_split : forall {A:Type}, forall l1 l2:list A, length(rev_append l1 l2) = length l1 + length l2.
Proof.
  induction l1;simpl;intros.
  - reflexivity.
  - rewrite IHl1. rewrite length_app_x. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma length_rev_append_x_l : forall {A:Type}, forall l:list A, forall x:A, length (rev_append l [x]) = length (rev_append l []) + 1.
Proof.
  induction l;simpl;intros.
  - reflexivity.
  - rewrite length_rev_append_split. rewrite length_rev_append_split. simpl. rewrite <- Nat.add_assoc. reflexivity.
Qed.

Theorem length_invariant_rev : forall A : Type, forall l : list A,length (rev l) = length l.
Proof.
  intros A l.
  case l. 
  - simpl. reflexivity.
  - unfold rev in *.
    case rev_append.
  (*  1 :  length (rev []) = length []
      2 :  forall (a : A) (l0 : list A),
            length (rev (a :: l0)) = length (a :: l0) *)
  induction l;intros.
  - simpl. reflexivity.
  - unfold rev in *. rewrite rev_append_x_l. 
    rewrite length_rev_append_x_l. rewrite IHl. rewrite length_app_x.
    rewrite Nat.add_comm. reflexivity.
Qed.


Theorem length_invariant_rev : forall A : Type, forall l : list A,length (rev l) = length l.
Proof.
  induction l;intros.
  - simpl. reflexivity.
  - unfold rev in *. rewrite rev_append_x_l. 
    rewrite length_rev_append_x_l. rewrite IHl. rewrite length_app_x.
    rewrite Nat.add_comm. reflexivity.
Qed.




