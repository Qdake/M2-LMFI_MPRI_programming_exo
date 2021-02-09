Module exos.

Require Import List.
Import ListNotations.

Inductive alpha := M | I | U.

Definition word := list alpha.

Inductive lang : word -> Prop :=
| axiom : lang [M;I]
| rule1 x : lang (x ++ [I]) -> lang (x ++ [I;U])
| rule2 x : lang ([M] ++ x) -> lang ([M] ++ x ++ x)
| rule3 x y : lang (x ++ [I;I;I] ++ y) -> lang (x ++ [U] ++ y)
| rule4 x y : lang (x ++ [U;U] ++ y) -> lang (x ++ y).

(* harder to prove *)
Theorem ex_1_1 : forall m:word, 
  lang m -> exists m', m = M :: m'.
Proof.
  intros m H. 
  induction H.
  - exists [I]. reflexivity.
  - destruct IHlang as (w,Hw).
    admit. (* not too hard until now*)
  - admit.
  - (* many details *) admit.
  - (* hard *) Abort.

(* harder to prove *)
Theorem starts_with_M_ter w : lang w -> exists v, w = M :: v.
Proof.
  intros H.
  Admitted.

Theorem ex_1_2 w :
  lang w -> match w with
  | M :: _ => True
  | _ => False
  end.
Proof.
  induction 1.
  - constructor.
  - destruct x; simpl in *; auto.
  - simpl. constructor.
  - destruct x; simpl in *; auto.
  - destruct x; simpl in *; auto. destruct IHlang.
Qed.

(* simplifier *)
Theorem ex_1_2_bis w :
  lang w -> match w with
  | lettre :: _ => lettre = M
  | _ => False
  end.
Proof.
  induction 1.
  - constructor.
  - destruct x; simpl in *; auto.
  - simpl; reflexivity.
  - destruct x; simpl in *. discriminate. auto.
  - destruct x; simpl in *. discriminate. auto.
Qed.

(*
Ternary arithmetic
We will now show that all the words of this language have a number of occurrences of the letter I that cannot be a multiple of 3. For that, we formalize first a little bit of ternary arithmetic (i.e. counting modulo 3, i.e. Z/3Z). We start with the following definition:
Inductive Z3 := Z0 | Z1 | Z2.

Define first the functions succ:Z3->Z3 and add:Z3->Z3->Z3 which implement the successor and addition modulo 3. Add then a notation for add via Infix "+" := add.
Show that add is commutative and associative and that Z0 is neutral for add.
Show that for all z:Z3, we have z<>Z0 -> z+z <> Z0.
Define a function occurI3 : word -> Z3 that for any word w:word computes the number of occurrences of the letter I modulo 3 in w.
Show that for all words v and w we have occurI3 (v ++ w) = (occurI3 v)+(occurI3 w).
Show that for all word w in the language L, we have occurI3 w <> Z0.
Deduce finally that ~(lang [M;U]).

Useful tactics: induction, inversion, destruct, discriminate, injection.
*)

Inductive Z3 := Z0 | Z1 |Z2.

Notation "0" := Z0.
Notation "1" := Z1.
Notation "2" := Z2.

Definition add z z':= 
match z with
| 0 => z'
| 1 => succ z'
| 2 => succ (succ z')
end.



End exos.

Module cours.
(* Already seen: injection and discriminate *)

(* injection H were H : S x = S y
    -----> x = y
               where H : x::l = y::l'
    -----> x = y and l = l'
*)

(* discriminate H where H : 0 = S x
    -----> goal concluded
*)

(* inversion is a generalization of both *)

Inductive even : nat -> Prop :=
| even_0 : even 0
| even_SS n : even n -> even (S (S n)).
(*
Lemma even_2
*)
Lemma even_plus4 : forall n, even n -> even (4+4).
Proof.
  intros.
  repeat apply even_SS.
  constructor.
Qed.

Lemma even_plus5_bis : forall n, even (S n) -> even (5+n).
Proof.
  intros H.
  induction H.
  (* !!! induction has forgotten that we add a (S ...) *)
  Abort.

Lemma even_plus5_ter : forall n m, S n = m -> even m -> even (5+n).
Proof.
  intros n m EQ H.
  induction H.
  (* !!! induction has forgotten that we add a (S ...) *)
  - discriminate.  
  Abort.

Lemma not_even_one : ~even 1.
Proof.
  intro.
  remember 1 as m.
  induction H.
  - discriminate.
  - discriminate.
Qed.

Lemma not_even_one_bis : ~even 1.
Proof.
  intro.
  inversion H.
Qed.

Lemma even_plus3 n: even (3+n) -> even (1+n).
Proof.
  intros H. 
  inversion H.
  assumption.
Qed.

Lemma test_inj x y : S x = S y -> x = y.
Proof.
  intro H.
  inversion H.
  reflexivity.
Qed.

Lemma test_inj_bis x : S x = 0 -> False.
Proof.
  intro H.
  inversion H.
Qed.




End cours.