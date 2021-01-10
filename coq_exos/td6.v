Lemma and_commut :
  forall A B : Prop, A/\B <-> B/\A.
Proof.
  intros;split.
  -intro. destruct H. split. assumption. assumption.
  -intro. destruct H. split. assumption. assumption.
Qed.

(* ex 1*)
Section ex_1.

Variables A B C : Prop.

Lemma E1F1 : A -> A.
Proof.
  intro. assumption.
Qed.
Lemma E1F1_2 : A -> A.
Proof.
  exact (fun (a : A) => a).
Qed.

Lemma E1F2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros H1 H2 a.
  apply H2. apply H1.
  assumption.
Qed.

Lemma E1F2_2 : (A -> B) -> (B -> C) -> A -> C.
Proof. 
  exact (fun (x : A->B) (y : B->C) (a : A) => y (x a)).
Qed.

Lemma E1F3 : A /\ B <-> B /\ A.
Proof.
  split.
  -intro. destruct H. split. assumption. assumption.
  -intro. destruct H. split. assumption. assumption.
Qed.

Lemma E1F3_2 : A /\ B <-> B /\ A.
Proof.
  exact (and_commut A B).
Qed.

Lemma E1F4 : A \/ B <-> B \/ A.
Proof.
  split.
  -intro. destruct H. right;assumption. left;assumption.
  -intro. destruct H. right;assumption. left;assumption.
Qed.

(* comment utiliser des lemmes fonctions pour demontrer ce lemma *)
Lemma E1F4_2 : A \/ B <-> B \/ A.
Admitted.
 
Lemma E1F5 : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split.
  -intro H. destruct H. destruct H. split. assumption. split. assumption. assumption.
  -intro H. destruct H. destruct H0. split. split. assumption. assumption. assumption.
Qed.

Lemma E1F6 : (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split.
  -intro H. destruct H. destruct H. left;assumption. right;left;assumption. right;right;assumption.
  -intro H. destruct H. left;left;assumption. destruct H. left;right;assumption. right;assumption.
Qed.

Lemma E1F7 : A -> ~~A.
Proof.
  intro H. intro H0. destruct H0. assumption.
Qed.

Lemma E1F8 : (A -> B) -> ~B -> ~A.
Proof.
  intros H H1.
  intro.
  apply H1.
  apply H.
  assumption.
Qed.

Lemma E1F9 : ~~(A \/ ~A).
Proof.
  intro.
  apply H.
  right.
  intro.
  destruct  H.
  left.
  assumption.
Qed.

End ex_1.


(*Ex 2*)
Section ex_2.

Variable X Y : Set.
Variable A B : X -> Prop.
Variables R : X -> Y -> Prop.

Lemma E2F1 : (forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x).
Proof.
  split. 
  -intro H. split. 
  --intro x. assert (A x /\ B x) as H1. exact (H x). destruct H1. assumption.
  --intro x. assert (A x /\ B x) as H1. exact (H x). destruct H1. assumption.
  -intro H. destruct H. intro x. split. exact (H x). exact (H0 x).
Qed.

Lemma E2F2 : (exists x, A x \/ B x) <-> (exists x, A x) \/ (exists x, B x).
Proof.
  split.
  -intro H. destruct H. destruct H.
  --left. exists x. assumption.
  --right. exists x. assumption.
  -intro H. destruct H; destruct H.
  --exists x. left. assumption.
  --exists x. right. assumption.
Qed.

Lemma E2F3 : (exists y, forall x, R x y) -> forall x, exists y, R x y.
Proof.
  intros H.
  intro x. 
  destruct H.
  exists x0.
  exact (H x).
Qed.







