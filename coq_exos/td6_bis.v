Section Ex_1.
Parameter E : Type.
Parameter R : E -> E -> Prop.
Axiom refl : forall x : E, R x x.
Axiom trans : forall x y z : E, R x y -> R y z -> R x z.
Axiom antisym : forall x y : E, R x y -> R y x -> x = y.

Definition smallest (x0 : E) := forall x : E, R x0 x.
Definition minimal (x0 : E) := forall x : E, R x x0 -> x = x0.

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
  - exact (tiers_exclus (exists x:E, InTheRoom x)).
  - intro H0. apply (not_not_elim (exists x : E, (Drinker x -> forall y:E, Drinker y))).
    intro H1. elim H1. destruct H0 as (a,H0). exists a. intro H2. intro b.
    cut (~~ Drinker b).
    + exact (not_not_elim (Drinker b)).
    + intros H3. elim H1. 
      exists b. intro H4. Search "False". apply (False_ind (forall y:E,Drinker y)).
      apply H3. assumption.
Qed.



