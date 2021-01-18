Section Ex_1.
Parameter E : Type.
Parameter R : E -> E -> Prop.
Axiom refl : forall x : E, R x x.
Axiom trans : forall x y z : E, R x y -> R y z -> R x z.
Axiom antisym : forall x y : E, R x y -> R y x -> x = y.

Definition smallest (x0 : E) := forall x : E, R x0 x.
Definition minimal (x0 : E) := forall x : E, R x x0 -> x = x0.
Print smallest.

Lemma E1Q1 :
  forall x x', smallest x -> smallest x' -> x = x'.
Proof.
  intros x x' Hx Hx'.
  unfold smallest in *. 
  apply antisym.  (* apply un axiom *) 
  apply Hx.
  apply Hx'.
Qed.

Search False.
Print False.
Print False_ind.

Lemma E1Q2 : 
  forall x, smallest x -> minimal x.
Proof.
  intros x Hx.
  unfold smallest in *. unfold minimal.
  intros x' Hx'.
  apply antisym.
  apply Hx'.
  apply Hx.
Qed.
  

Lemma E1Q3 : 
  forall x x', smallest x -> minimal x' -> x= x'.
Proof.
  intros x x' Hx Hx'.
  unfold minimal in Hx'. unfold smallest in *.
  apply Hx'.
  apply Hx.
Qed.
End Ex_1.

(* Exercice 2 : Drinker lemma*)
Search "False".
Module Ex_2.
Parameter E : Type.
 
Parameter Drinker : E -> Prop.
Parameter InTheRoom : E -> Prop.
(* Classical logic here : *)
Axiom not_not_elim : forall A : Prop, ~~A -> A.
Lemma tiers_exclus : forall A : Prop, A \/ ~A.
Proof.
  intro a.
  cut (~~(a\/~a)).
  -intro H. apply (not_not_elim (a\/~a)). assumption.
  -intro H. apply H. right. intro H0. apply H. left. assumption.
Qed.

Lemma drink : (exists x, InTheRoom x) -> (exists x : E, (Drinker x -> forall y:E, Drinker y)).
Proof.
  assert ((exists x, InTheRoom x) \/~(exists x, InTheRoom x)).
  (* assertion: la chambre est soit vide, soit non vide *)
  - exact (tiers_exclus (exists x:E, InTheRoom x)).
  - intro H0.
    (* supposons que la chambre ne soit pas vide *)
    apply (not_not_elim (exists x : E, (Drinker x -> forall y:E, Drinker y))).
    (* la conclusion est obtenue par l'elimination d'une double negation. *)
    intro H1. elim H1. destruct H0 as (a,H0). exists a. intro H2. intro b.
    cut (~~ Drinker b).
    + exact (not_not_elim (Drinker b)).
    + intros H3. elim H1. 
      exists b. intro H4. Search "False". apply (False_ind (forall y:E,Drinker y)).
      apply H3. assumption.
Qed.

End Ex_2.

Module Ex_3.

Parameter E : Type.

(* subset *)
Definition subset (A : E -> Prop) (B : E -> Prop) := forall x : E, A x -> B x.
Print subset.

Lemma subset_refl : forall (A : E -> Prop), subset A A.
Proof.
  intro. unfold subset. intro. intro. assumption.
Qed.

Lemma subset_trans : forall (A B C : E -> Prop), subset A B /\ subset B C -> subset A C.
Proof.
  intros A B C. intro H. destruct H.
  unfold subset in *.
  intro x. intro. apply (H0 x). apply (H x). assumption.
Qed.

Definition eq (A B : E -> Prop) := forall e : E, A e <-> B e.
Print eq.

Lemma subset_antisym : forall (A B : E -> Prop), subset A B /\ subset B A -> eq A B.
Proof.
  intros A B . intro H. destruct H. unfold subset in *.
  unfold eq. intro e. split.
  - exact (H e).
  - exact (H0 e).
Qed.

(* union *)
Definition union (A B: E -> Prop) : E -> Prop := fun e : E => A e \/ B e.
Print union.

Lemma union_asso : forall (A B C : E -> Prop), eq (union (union A B) C) (union A (union B C)).
Proof.
  intros A B C.
  unfold eq. intro e. split. 
  - unfold union in *. intro H1. destruct H1 as [H2|H3]. destruct H2 as [H4|H5].
    + left. assumption. 
    + right. left. assumption.
    + right. right. assumption.
  - unfold union in *. intro H6. destruct H6 as [H7|H8].
    + left. left. assumption.
    + destruct H8 as [H9|H10].
    ++ left. right. assumption.
    ++ right. assumption.
Qed.

Lemma union_comm : forall (A B : E -> Prop), eq (union A B) (union B A).
Proof.
  intros A B. unfold eq. intro e. unfold union in *. split.
  - intro H1. destruct H1 as [H2|H3]. 
   + right. assumption.
   + left. assumption.
  - intro H2. destruct H2 as [H4|H5].
   + right. assumption.
   + left. assumption.
Qed.

Lemma union_idem : forall (A : E -> Prop), eq (union A A) A.
Proof.
  intro A. unfold eq. unfold union. intro e. split.
  - intro H1. destruct H1;assumption.
  - intro H2. left. assumption.
Qed.


(* intersection *)
Definition intersec (A B: E -> Prop) : E -> Prop := fun e : E => A e /\ B e.
Print intersec.

Lemma intersec_asso : forall (A B C : E -> Prop), eq (intersec (intersec A B) C) (intersec A (intersec B C)).
Proof.
  intros A B C.
  unfold eq. intro e. split. 
  - unfold intersec in *. intro H1. destruct H1 as (H2,H3). destruct H2 as (H4,H5).
    + split. 
    ++ assumption.
    ++ split; assumption. 
  - unfold intersec in *. intro H6. destruct H6 as (H7,H8).
    + split. destruct H8. split;assumption. destruct H8. assumption.
Qed.

Lemma intersec_comm : forall (A B : E -> Prop), eq (intersec A B) (intersec B A).
Proof.
  intros A B. unfold eq. intro e. unfold intersec in *. split.
  - intro H1. destruct H1 as (H2,H3). split;assumption.
  - intro H2. destruct H2 as (H4,H5). split;assumption.
Qed.

Lemma intersec_idem : forall (A : E -> Prop), eq (intersec A A) A.
Proof.
  intro A. unfold eq. unfold intersec. intro e. split.
  - intro H1. destruct H1;assumption.
  - intro H2. split;assumption.
Qed.

(* distributivity 
                   union wrt to intersection*)
Lemma dist_union_wrt_intersec : forall (A B C : E -> Prop), eq (union A (intersec B C)) (intersec (union A B) (union A C)).
Proof.
  intros A B C. unfold eq. intro e. unfold union. unfold intersec. split.
  - intro H1. split.
   + destruct H1 as [H2|H3].
    ++ left. assumption.
    ++ destruct H3. right. assumption.
   + destruct H1 as [H2|H3].
    ++ left. assumption.
    ++ destruct H3. right. assumption.
  - intro H1. destruct H1 as (H2,H3). destruct H2 as [H4|H5].
   + left. assumption.
   + destruct H3 as [H6|H7]. left. assumption. right. split;assumption.
Qed.
(* distributivity  
                    intersection  wrt union*)
Lemma dist_intersec_wrt_union : forall (A B C : E -> Prop), eq (intersec A (union B C)) (union (intersec A B) (intersec A C)).
Proof.
  intros A B C. unfold eq. intro e. unfold union. unfold intersec. split.
  - intro H1. destruct H1 as (H2,H3). destruct H3 as [H4|H5].
  + left. split;assumption.
  + right. split;assumption.
  - intro H2. destruct H2 as [H3|H4]. destruct H3. split.
  ++ assumption.
  ++ left. assumption.
  ++ split. 
  +++ destruct H4. assumption.
  +++ right. destruct H4. assumption. 
Qed.
