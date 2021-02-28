(**************************************************************************)
(*              Coherence of first-order Heyting arithmetic               *)
(*                                                                        *)
(*                         © 2011 Stéphane Glondu                         *)
(*                         © 2013 Pierre Letouzey                         *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*   it under the terms of the CeCILL free software license, version 2.   *)
(**************************************************************************)

Require Import List Arith Omega.
Import ListNotations.
(* Tactics *)
(* First, tell the "auto" tactic to use the "omega" solver. *)

Hint Extern 8 (_ = _ :> nat) => omega.
Hint Extern 8 (_ <= _) => omega.
Hint Extern 8 (_ < _) => omega.
Hint Extern 8 (_ <> _ :> nat) => omega.
Hint Extern 8 (~ (_ <= _)) => omega.
Hint Extern 8 (~ (_ < _)) => omega.
Hint Extern 12 => exfalso; omega.

Print Nat.leb_spec.

(* Destructing the <=? and ?= (in)equality tests, useful when proving facts
   about "if ... then ... else" code. *)

Ltac break := match goal with
 | |- context [ ?x <=? ?y ] => destruct (Nat.leb_spec x y)
 | |- context [ ?x ?= ?y ] => destruct (Nat.compare_spec x y)
end.


(* Terms : first-order terms over the Peano signature 0 S + *.
   The variable are represented as De Bruijn indices. *)

Inductive term :=
  | Tvar : nat -> term
  | Tzero : term
  | Tsucc : term -> term
  | Tplus : term -> term -> term
  | Tmult : term -> term -> term.

Hint Extern 10 (Tvar _ = Tvar _) => f_equal.

(* Term lifting: add n to all variables of t which are >= k *)

Fixpoint tlift n t k :=
  match t with
    | Tvar i => Tvar (if k <=? i then n+i else i)
    | Tzero => Tzero
    | Tsucc u => Tsucc (tlift n u k)
    | Tplus u v => Tplus (tlift n u k) (tlift n v k)
    | Tmult u v => Tmult (tlift n u k) (tlift n v k)
  end.

Lemma tlift_1 : forall t n n' k k', k <= k' -> k' <= k + n ->
  tlift n' (tlift n t k) k' = tlift (n' + n) t k.
Proof.
    induction t; intros; simpl; f_equal; repeat break; auto.
Qed.

Lemma tlift_2 : forall t n n' k k', k' <= k ->
  tlift n' (tlift n t k) k' = tlift n (tlift n' t k') (n' + k).
Proof.
  induction t; intros; simpl; f_equal; repeat break; auto.
Qed.

Hint Resolve tlift_1 tlift_2.

(* Term substitution: replace variable x by (tlift x t' 0) in t *)

Fixpoint tsubst x t' t :=
  match t with
    | Tvar i =>
      match x ?= i with
        | Eq => tlift x t' 0
        | Lt => Tvar (pred i)
        | Gt => Tvar i
      end
    | Tzero => Tzero
    | Tsucc u => Tsucc (tsubst x t' u)
    | Tplus u v => Tplus (tsubst x t' u) (tsubst x t' v)
    | Tmult u v => Tmult (tsubst x t' u) (tsubst x t' v)
  end.

Lemma tsubst_1 : forall t x t' n k, k <= x -> x <= k + n ->
  tsubst x t' (tlift (S n) t k) = tlift n t k.
Proof.
  induction t; intros; simpl; f_equal; auto; repeat (break; simpl; auto).
Qed.

Lemma tsubst_2 : forall t x t' n k, k <= x ->
  tlift n (tsubst x t' t) k = tsubst (n + x) t' (tlift n t k).
Proof.
  induction t; intros; simpl; f_equal; auto; repeat (break; simpl; auto).
Qed.

Hint Resolve tsubst_1 tsubst_2.

Lemma tsubst_3 : forall t x t' n k,
  tlift n (tsubst x t' t) (x + k) =
  tsubst x (tlift n t' k) (tlift n t (x + S k)).
Proof.
  induction t; intros; simpl; f_equal; auto; repeat (break; simpl; auto).
  symmetry. auto.
Qed.

Lemma tsubst_4 : forall t x t' y u',
  tsubst (x + y) u' (tsubst x t' t) =
  tsubst x (tsubst y u' t') (tsubst (x + S y) u' t).
Proof.
  induction t; intros; simpl; try (f_equal; auto; fail).
  repeat (break; simpl; auto);
  symmetry; rewrite <- ?plus_n_Sm; auto.
Qed.

(* Terms where all variables are < n *)

Inductive cterm n : term -> Prop :=
  | cterm_var : forall i, i < n -> cterm n (Tvar i)
  | cterm_zero : cterm n (Tzero)
  | cterm_succ : forall u, cterm n u -> cterm n (Tsucc u)
  | cterm_plus : forall u v, cterm n u -> cterm n v -> cterm n (Tplus u v)
  | cterm_mult : forall u v, cterm n u -> cterm n v -> cterm n (Tmult u v).

Hint Constructors cterm.

Lemma cterm_1 : forall n t, cterm n t -> forall n', n <= n' -> cterm n' t.
Proof.
  intros n. intros t H.
  induction H ; simpl; intuition.
Qed.

Lemma cterm_2 : forall n t, cterm n t -> forall k, tlift k t n = t.
Proof.
  (* QQ: soient n, t, si (cterm n t) alors toute variable de t est < n, 
    donc l'augmenter les variables
      >= n de t ne change rien. *) 
  intros n. intros t H.
  induction H ; simpl; intuition. 
  - break; intuition.
  - rewrite IHcterm. reflexivity.
  - rewrite IHcterm1,IHcterm2. reflexivity.
  - rewrite IHcterm1, IHcterm2. reflexivity.
Qed.

Lemma cterm_3 : forall n t, cterm n t -> forall t' j, n <= j -> tsubst j t' t = t.
Proof.
  (* QQ: soient n, t, si (cterm n t) alors toute variable de t est 
     de numéro < n, donc substitue la viariable j >= n de t par t'
     ne change rien. *) 
  intros n t H.
  induction H; simpl; intuition.
  - break; intuition.
  - rewrite IHcterm.
    + reflexivity. + assumption.
  - rewrite IHcterm1. rewrite IHcterm2.
    + reflexivity. + assumption. + assumption.
  - rewrite IHcterm1. rewrite IHcterm2. 
    + reflexivity. + assumption. + assumption.
Qed.

Lemma cterm_4 : forall n t, cterm (S n) t ->
  forall t', cterm 0 t' -> cterm n (tsubst n t' t).
Proof.
  (* QQ: soient n, t, supposons (cterm n t) i.e. toute variable de t est 
         de numéro < S n, 
         soit t', supposons (cterm 0 t') i.e. toute variable de t' est < 0,
         c-a-d terme constant alors en substituant toute variable n par t',
         on obtien un terme de degree < n*)
  intros n t H. 
  induction H; simpl; intuition.
  break; intuition.
  elim H0; simpl; intuition.
Qed.

(* Formulas of Heyting Arithmetic. *)

Inductive formula :=
  | Fequal : term -> term -> formula
  | Ffalse : formula
  | Fand : formula -> formula -> formula
  | For : formula -> formula -> formula
  | Fimplies : formula -> formula -> formula
  | Fexists : formula -> formula
  | Fforall : formula -> formula.

Delimit Scope pa_scope with pa.
Bind Scope pa_scope with term.
Bind Scope pa_scope with formula.
Arguments Tsucc _%pa.
Arguments Tplus _%pa _%pa.
Arguments Tmult _%pa _%pa.
Arguments Fequal _%pa _%pa.
Arguments Fand _%pa _%pa.
Arguments For _%pa _%pa.
Arguments Fimplies _%pa _%pa.
Arguments Fexists _%pa.
Arguments Fforall _%pa.

(* Formula lifting: add n to all variables of t which are >= k *)

Fixpoint flift n A k :=
  match A with
    | Fequal u v => Fequal (tlift n u k) (tlift n v k)
    | Ffalse => Ffalse
    | Fand B C => Fand (flift n B k) (flift n C k)
    | For B C => For (flift n B k) (flift n C k)
    | Fimplies B C => Fimplies (flift n B k) (flift n C k)
    | Fexists B => Fexists (flift n B (S k))
    | Fforall B => Fforall (flift n B (S k))
  end.

Lemma flift_1 : forall A n n' k k', k <= k' -> k' <= k + n ->
  flift n' (flift n A k) k' = flift (n' + n) A k.
Proof.
  induction A; intros; simpl; f_equal; auto.
Qed.

Lemma flift_2 : forall A n n' k k', k' <= k ->
  flift n' (flift n A k) k' = flift n (flift n' A k') (n' + k).
Proof.
  induction A; intros; simpl; f_equal; rewrite ?plus_n_Sm; auto.
Qed.

(* Formula substitution: replace variable x by (tlift x t' 0) in A *)

Fixpoint fsubst x t' A :=
  match A with
    | Fequal u v => Fequal (tsubst x t' u) (tsubst x t' v)
    | Ffalse => Ffalse
    | Fand B C => Fand (fsubst x t' B) (fsubst x t' C)
    | For B C => For (fsubst x t' B) (fsubst x t' C)
    | Fimplies B C => Fimplies (fsubst x t' B) (fsubst x t' C)
    | Fexists B => Fexists (fsubst (S x) t' B)
    | Fforall B => Fforall (fsubst (S x) t' B)
  end.

Lemma fsubst_1 : forall A x t' n k, k <= x -> x <= k + n ->
  fsubst x t' (flift (S n) A k) = flift n A k.
Proof.
  induction A; intros; simpl; f_equal; auto.
Qed.

Lemma fsubst_2 : forall A x t' n k, k <= x ->
  flift n (fsubst x t' A) k = fsubst (n + x) t' (flift n A k).
Proof.
  induction A; intros; simpl; f_equal; rewrite ?plus_n_Sm; auto.
Qed.

Lemma fsubst_3 : forall A x t' n k,
  flift n (fsubst x t' A) (x + k) =
  fsubst x (tlift n t' k) (flift n A (x + S k)).
Proof.
  induction A; intros; simpl; f_equal; auto using tsubst_3;
  apply (IHA (S x)).
Qed.

Lemma fsubst_4 : forall A x t' y u',
  fsubst (x + y) u' (fsubst x t' A) =
  fsubst x (tsubst y u' t') (fsubst (x + S y) u' A).
Proof.
  induction A; intros; simpl; f_equal; auto using tsubst_4;
  apply (IHA (S x)).
Qed.

(* Formulas where all variables are < n *)

Inductive cformula n : formula -> Prop :=
  | cformula_equal : forall u v,
    cterm n u -> cterm n v -> cformula n (Fequal u v)
  | cformula_false : cformula n Ffalse
  | cformula_and : forall B C,
    cformula n B -> cformula n C -> cformula n (Fand B C)
  | cformula_or : forall B C,
    cformula n B -> cformula n C -> cformula n (For B C)
  | cformula_implies : forall B C,
    cformula n B -> cformula n C -> cformula n (Fimplies B C)
  | cformula_exists : forall B,
    cformula (S n) B -> cformula n (Fexists B)
  | cformula_forall : forall B,
    cformula (S n) B -> cformula n (Fforall B).

Print cformula_ind.


Hint Constructors cformula.

Lemma cformula_1 : forall n A, cformula n A ->
  forall n', n <= n' -> cformula n' A.
Proof. 
  intros n A H.
  elim H; simpl; intuition.
  apply cformula_equal; apply (cterm_1 n0); (assumption || reflexivity).
Qed.

Lemma cformula_2 : forall n A, cformula n A -> forall k, flift k A n = A.
Proof.
  intros n A H.
  elim H; simpl; auto; intros. 
  - (* cformula n (Fequal u v) *)
    rewrite (cterm_2 n0 u); 
    repeat (try (reflexivity || assumption || rewrite H1|| rewrite H3));
    rewrite (cterm_2 n0 v); 
    repeat (try (reflexivity || assumption || rewrite H1|| rewrite H3)).
  - (* cformula n (Fand B C) *)
    rewrite H1,H3; reflexivity.
  - (* cformula n (For B C) *)
    rewrite H1,H3; reflexivity.
  - (* cformula n (Fimplies B C) *) 
    rewrite H1,H3; reflexivity.
  - (* cformula n (Fexists B) *)
    rewrite H1; reflexivity.
  - (* cformula n (Fforall B) *)
    rewrite H1; reflexivity.
Qed.

(*qq:  si toute variable d'une formule est de dedgré < n
       alors substituer la variable j, avec j >= n, par une terme 
       quelconque, ne modifie pas cette formule *)
Lemma cformula_3 : forall n A, cformula n A ->
  forall t' j, n <= j -> fsubst j t' A = A.
Proof. 
  intros n A H. 
  (* induction sur la structure de la proposition H *)
  elim H; simpl; intros.
  - (* cformula n (Fequal u v) *)
    rewrite (cterm_3 n0 u); try assumption;
    rewrite (cterm_3 n0 v); try (assumption||reflexivity).
  - (* cformula n False *)
    reflexivity.
  - (* cformula n (Fand B C) *)
    repeat (try (reflexivity || assumption || rewrite H1|| rewrite H3)).
  - (* cformula n (For B C) *)
    repeat (try (reflexivity || assumption || rewrite H1|| rewrite H3)).
  - (* cformula n (Fimplies B C) *)
    repeat (try (reflexivity || assumption || rewrite H1|| rewrite H3)).
  - (* cformula n (Fexists B) *)
    repeat (try (reflexivity || assumption || rewrite H1|| rewrite H3));
    auto.
  - (* cformula n (Fforall B) *)
    repeat (try (reflexivity || assumption || rewrite H1|| rewrite H3)); 
    apply le_n_S; assumption.
Qed.


(*qq:  si le numéro de toute variable d'une formule est inférieure 
      ou égale à n, alors en substituant la variable de numéro n par
      un terme clos, on obtient une formule dont le numéro de toute 
      variable est inférieure ou égale à (n-1).  *)
Lemma cformula_4 : forall n A, cformula (S n) A ->
  forall t', cterm 0 t' -> cformula n (fsubst n t' A).  
Proof.
  intros n A;  
  revert n.
  (* induction sur la structure de A *)
  induction A; 
  simpl;
  intros n H_cformula_Sn t' H_cterm_0.
  - (* A = Fequal t t0 *)
    apply cformula_equal; apply cterm_4; 
    try inversion H_cformula_Sn;assumption.
  - (* A = Ffalse *)
    constructor.
  - (* A = Fand A1 A2 *)
    inversion H_cformula_Sn; 
    apply cformula_and;
    try (apply IHA1||apply IHA2);
    assumption.
  - (* A = For A1 A2 *)
    inversion H_cformula_Sn; 
    apply cformula_or; 
    try (apply IHA1 || apply IHA2); 
    assumption.
  - (* A = Fimplies A1 A2 *)
    apply cformula_implies; 
    try (apply IHA1 || apply IHA2); 
    inversion H_cformula_Sn; 
    assumption.
  - (* A = Fexists A1 *)
    apply cformula_exists.
    inversion H_cformula_Sn;
    apply IHA;
    assumption.
  - (* forall *)
    apply cformula_forall;
    inversion H_cformula_Sn;
    apply IHA;
    assumption.
Qed.

Reserved Notation "A ==> B" (at level 86, right associativity).
Reserved Notation "# n" (at level 2).

Notation "A /\ B" := (Fand A B) : pa_scope.
Notation "A \/ B" := (For A B) : pa_scope.
Notation "A ==> B" := (Fimplies A B) : pa_scope.
Notation "x = y" := (Fequal x y) : pa_scope.
Notation "x + y" := (Tplus x y) : pa_scope.
Notation "x * y" := (Tmult x y) : pa_scope.
Notation "# n" := (Tvar n) (at level 2) : pa_scope.

Close Scope nat_scope.
Close Scope type_scope.
Close Scope core_scope.
Open Scope pa_scope.
Open Scope core_scope.
Open Scope type_scope.
Open Scope nat_scope.

(* Contexts (or environments), represented as list of formulas. *)

Definition context := list formula.

(* Lifting an context *)

Definition clift n Γ k := map (fun A => flift n A k) Γ.

(* Rules of (intuitionistic) Natural Deduction.

   This predicate is denoted with the symbol ":-", which
   is easier to type than "⊢".
   After this symbol, Coq expect a formula, hence uses the formula
   notations, for instance /\ is Fand instead of Coq own conjunction).
*)

Reserved Notation "Γ :- A" (at level 87, no associativity).
Inductive rule : context -> formula -> Prop :=
  | Rax Γ A :  In A Γ   ->  Γ:-A   (* QQ:  In A Γ -> rule Γ A *)
  (* QQ :     In : forall A : Type, A -> list A -> Prop *)
  (* QQ :                                    In A Γ -> Γ :- A est une Prop *)
  | Rfalse_e Γ :   Γ:-Ffalse -> forall A, Γ:-A (*QQ:  rule Γ Ffalse -> forall A, rule Γ A*)
  | Rand_i Γ B C :   Γ:-B -> Γ:-C -> Γ:-B/\C   (*QQ:   rule Γ B -> rule Γ C -> rule Γ (Fand B C) *)
  | Rand_e1 Γ B C :   Γ:-B/\C -> Γ:-B          (*QQ:   rule Γ (Fand B C) -> rule Γ B  *)
  | Rand_e2 Γ B C :   Γ:-B/\C -> Γ:-C          (*QQ:   rule Γ (Fand B C) -> rule Γ C *)
  | Ror_i1 Γ B C :   Γ:-B -> Γ:-B\/C           (*QQ:   rule Γ B -> rule Γ (For B C) *)
  | Ror_i2 Γ B C :   Γ:-C -> Γ:-B\/C           (*QQ:   rule Γ C -> rule Γ (For B C) *)  
  | Ror_e Γ A B C :   Γ:-B\/C -> (B::Γ):-A -> (C::Γ):-A -> Γ:-A 
                           (*QQ:   rule Γ (For B C) -> rule (B::Γ) A -> rule (C::Γ) A -> rule Γ A *)
  | Rimpl_i Γ B C :   (B::Γ):-C -> Γ:-B==>C    (*QQ:   rule (B::Γ) C -> rule Γ (Fimplies B C) *) 
  | Rimpl_e Γ B C :   Γ:-B==>C -> Γ:-B -> Γ:-C (*QQ:   rule Γ (Fimplies B C) -> rule Γ B -> rule Γ C *)
  | Rforall_i Γ B :   (clift 1 Γ 0):-B -> Γ:-(Fforall B)
                           (*QQ:   rule (clift 1 Γ 0) B -> rule Γ (Fforall B) *) 
                           (*QQ:   rule (map (fun A => flift 1 A k) Γ) B -> rule Γ (Fforall B) *)
  | Rforall_e Γ B t :   Γ:-(Fforall B) -> Γ:-(fsubst 0 t B)
                           (*QQ:   rule Γ (Fforall B) -> rule Γ (fsubst 0 t B) *)
  | Rexists_i Γ B t :   Γ:-(fsubst 0 t B) -> Γ:-(Fexists B) (*QQ:   rule Γ (fsubst 0 t B) -> rule Γ (fexists B) *)
  | Rexists_e Γ A B :
    Γ:-(Fexists B) -> (B::clift 1 Γ 0):-(flift 1 A 0) -> Γ:-A
                 (*QQ:   rule Γ (Fexists B) -> rule (B::clift 1 Γ 0) (flift 1 A 0) -> rule Γ A  *)
where "Γ :- A" := (rule Γ A).

Print rule_ind.
(* Auxiliary connectives and admissible rules *)
Definition Ftrue : formula := Ffalse ==> Ffalse.
Definition Fnot : formula -> formula := fun x:formula => x ==> Ffalse.
Definition Fiff := fun A B : formula => Fand (A ==> B) (B ==> A).
Fixpoint nFforall (n:nat) (A:formula) := 
match n with 
| 0 => A
| S n' => Fforall (nFforall n' A)
end.
Notation "~ A" := (Fnot A) : pa_scope.

Lemma Rtrue_i : forall Γ, Γ:-Ftrue.
Proof.
  intro Γ. unfold Ftrue. apply Rimpl_i. apply Rax. simpl. left. reflexivity.
Qed.
    

Lemma Rnot_i : forall Γ A, (A::Γ):-Ffalse -> Γ:- ~A.
Proof.
  intros Γ A H. unfold Fnot. apply Rimpl_i. assumption.
Qed. 


Lemma Rnot_e : forall Γ A, Γ:-A -> Γ:- ~A -> Γ:-Ffalse.
Proof.
  intros Γ A H H1; unfold Fnot in H1. apply (Rimpl_e  Γ A Ffalse);assumption.
Qed. 
  
Lemma Riff_i : forall Γ A B,
  (A::Γ):-B -> (B::Γ):-A -> Γ:-(Fiff A B).
Proof.
  intros  Γ A B H1 H2; unfold Fiff. 
  apply (Rand_i  Γ (A==>B) (B==>A)); apply Rimpl_i; assumption.
Qed.

Lemma nFforall_1 : forall n x t A,
  fsubst x t (nFforall n A) = nFforall n (fsubst (n + x) t A).
Proof.
  induction n; simpl; intros x t A.
  - reflexivity.
  - f_equal; pattern (S (n+x)); rewrite <- Nat.add_succ_r; apply IHn. 
Qed.

(* Peano axioms *)
(*QQ: Notation "# n" := (Tvar n) (at level 2) : pa_scope.*)
Inductive PeanoAx : formula -> Prop :=
  | pa_refl : PeanoAx (nFforall 1 (#0 = #0))
  | pa_sym : PeanoAx (nFforall 2 (#1 = #0 ==> #0 = #1))
  | pa_trans : PeanoAx (nFforall 3 (#2 = #1 /\ #1 = #0 ==> #2 = #0))
  | pa_compat_s : PeanoAx (nFforall 2 (#1 = #0 ==> Tsucc #1 = Tsucc #0))
  | pa_compat_plus_l : PeanoAx (nFforall 3 (#2 = #1 ==> #2 + #0 = #1 + #0))
  | pa_compat_plus_r : PeanoAx (nFforall 3 (#1 = #0 ==> #2 + #1 = #2 + #0))
  | pa_compat_mult_l : PeanoAx (nFforall 3 (#2 = #1 ==> #2 * #0 = #1 * #0))
  | pa_compat_mult_r : PeanoAx (nFforall 3 (#1 = #0 ==> #2 * #1 = #2 * #0))
  | pa_plus_O : PeanoAx (nFforall 1 (Tzero + #0 = #0))
  | pa_plus_S : PeanoAx (nFforall 2 (Tsucc #1 + #0 = Tsucc (#1 + #0)))
  | pa_mult_O : PeanoAx (nFforall 1 (Tzero * #0 = Tzero))
  | pa_mult_S : PeanoAx (nFforall 2 (Tsucc #1 * #0 = (#1 * #0) + #0))
  | pa_inj : PeanoAx (nFforall 2 (Tsucc #1 = Tsucc #0 ==> #1 = #0))
  | pa_discr : PeanoAx (nFforall 1 (~ Tzero = Tsucc #0))
  | pa_ind : forall A n, cformula (S n) A ->
    PeanoAx (nFforall n (
      fsubst 0 Tzero A /\
      Fforall (A ==> fsubst 0 (Tsucc #0) (flift 1 A 1)) ==> Fforall A
    )).

(* Definition of theorems over Heyting Arithmetic.

   NB: we should normally restrict theorems to closed terms only,
   but this doesn't really matter here, since we'll only prove that
   False isn't a theorem. *)

Definition Thm T :=
  exists axioms, (forall A, In A axioms -> PeanoAx A) /\ (axioms:-T). 

Lemma HA_n_Sn_auxiliaire_PeanoAx_forall_n_not_eq_n_sn : 
      PeanoAx (
              nFforall (S 0) (
                 fsubst 0 Tzero (~ #0 = Tsucc # 0) /\
                 Fforall ((~ #0 = Tsucc # 0) 
                     ==> fsubst 0 (Tsucc #0) (flift 1 (~ #0 = Tsucc # 0) 1)) 
                 ==> Fforall (~ #0 = Tsucc # 0)
                             )
              ).
Proof.
  apply pa_ind; unfold Fnot; 
  apply cformula_implies ;
  repeat try (apply cformula_equal || constructor || auto).
Qed. 


(* Example of theorem *)
Lemma HA_n_Sn :  Thm (Fforall (Fnot (Fequal #0 (Tsucc #0)) )).
Proof.
  unfold Thm.
  pose (axiome_ind_init := fsubst 0 Tzero (~ #0 = Tsucc # 0) ).
  pose (axiome_ind_next := Fforall ((~ #0 = Tsucc # 0) ==> fsubst 0 (Tsucc #0) (flift 1 (~ #0 = Tsucc # 0) 1))).    
  pose (axiome_ind := (nFforall (S 0) ( axiome_ind_init /\ axiome_ind_next ==> Fforall (~ #0 = Tsucc # 0)))).
  pose (axiome_inj := (nFforall 2 (Tsucc #1 = Tsucc #0 ==> #1 = #0))).  
  pose (axiome_discr := nFforall 1 (~ Tzero = Tsucc #0)).
  pose (axiomes :=   [
                axiome_ind; axiome_inj; axiome_discr
                     ]).
  exists axiomes.  
  split. 
  (* montrer que chaque formule dans [axiome_ind; axiome_inj; axiome_discr]
     est un PeanoAx. *)
  - intros A H_AInAxiomes.  
    destruct H_AInAxiomes as [HA|H_AInAxiomes]. (* traiter par formule *) 
    + (* Montrer que "axiome_ind" est dans PeanoAx *) 
      assert (HA_n_Sn_auxiliaire_PeanoAx_forall_n_not_eq_n_sn := 
                        HA_n_Sn_auxiliaire_PeanoAx_forall_n_not_eq_n_sn ). 
      (* ajout de lemme auxiliaire dans la contexte *)          
      rewrite <- HA; unfold axiome_ind; simpl in *; 
      exact HA_n_Sn_auxiliaire_PeanoAx_forall_n_not_eq_n_sn.
    + (* Montrer que chaque formule dans [axiome_inj; axiome_discr]
     est un PeanoAx. *)
      destruct H_AInAxiomes as [HA|H_AInAxiomes]. 
      ++ (* montrer que axiome_inj est un PeanoAx*)  
         rewrite <- HA; unfold axiome_inj; constructor.
      ++ (* Montrer que chaque formule dans [axiome_discr]
     est un PeanoAx. *) 
         destruct H_AInAxiomes as [HA|H_AInAxiomes].
         +++ (* montrer que axiome_discr est un PeanoAX*) 
             rewrite <- HA; unfold axiome_discr; constructor.
         +++ (* montrer que toute formule dans la list [] est un PeanoAx *)
             destruct H_AInAxiomes; auto.
  - (* deduction de la formule avec les axiomes posés et les "rule" *)
    apply (Rimpl_e axiomes (axiome_ind_init /\ axiome_ind_next) 
                           (Fforall (~ #0 = Tsucc # 0))           ). 
    + apply (Rforall_e _ (axiome_ind_init /\ axiome_ind_next 
                          ==> Fforall (~ # 0 = Tsucc # 0))
                          #0                                      ). 
      apply Rax; unfold In; simpl; auto.
    + apply Rand_i.  
      ++ apply (Rforall_e _ (Tzero = Tsucc #0 ==> Ffalse) Tzero). 
         apply Rax; unfold In; simpl; auto.
      ++ apply (Rforall_i); simpl; apply (Rimpl_i); apply (Rimpl_i).
         apply (Rimpl_e _ (# 0 = Tsucc # 0) Ffalse).
         +++ apply Rax; simpl; right; left; reflexivity.
         +++ apply (Rimpl_e _ (Tsucc # 0 = Tsucc (Tsucc # 0)) _).
             ++++ apply (Rforall_e _ ((Tsucc # 1 = Tsucc #0) ==> # 1 = # 0) (Tsucc #0)).  (* forall elim *)
                  apply (Rforall_e _ (Fforall (Tsucc # 1 = Tsucc # 0 ==> # 1 = # 0)) #0).  (* forall elim *)
                  apply Rax; simpl; auto.
             ++++ apply Rax; simpl; auto.
Qed.


Definition valuation := list nat.
 
Fixpoint tinterp (v:valuation) t :=
  match t with
    | Tvar j => nth j v O
    | Tzero => O
    | Tsucc t => S (tinterp v t)
    | Tplus t t' => tinterp v t + tinterp v t'
    | Tmult t t' => tinterp v t * tinterp v t'
  end.


Lemma tinterp_1_aux_arith : forall m n:nat,
                                        m <= n -> exists k:nat, m + k = n.
Proof. 
  intros m n H; elim H.
  - exists 0; auto.
  - intros m0 H_m_le_m0 H_exist.  destruct H_exist. exists (S x). auto.
Qed.

Lemma tinterp_1 : forall t v0 v1 v2,
  tinterp (v0++v1++v2) (tlift (length v1) t (length v0)) =
  tinterp (v0++v2) t.
Proof.
  induction t; simpl; intuition. (*induction sur la structure de t*)
  break; simpl; intuition. 
   case H; simpl; auto.
  - rewrite Nat.add_comm, app_nth2_plus, app_nth2, app_nth2.
    assert (length v1 - length v1 = length v0 - length v0); auto.
    rewrite H0; reflexivity. apply Nat.le_refl.
    apply Nat.le_refl.
  - assert (forall m n:nat, m <= n -> exists k:nat, m + k = n).
    exact tinterp_1_aux_arith.
    intros; assert (exists k:nat, length v0 + k = S m).
    apply H0. apply (Nat.le_trans (length v0) m (S m));auto.
    destruct H2; rewrite <- H2; rewrite Nat.add_assoc. 
    pattern (length v1 + length v0); rewrite Nat.add_comm.
    repeat rewrite app_nth2;f_equal; auto.
  - repeat rewrite app_nth1;auto.
Qed.

Lemma tinterp_2_aux_nth {A:Type}: forall n:nat, forall l:list A, forall d k:A, n >= 1 -> nth (Nat.pred n) l d = nth n (k::l) d.
Proof.
  (* induction sur la structure de t et puis celle de n *)
  induction l; simpl; auto; induction n; simpl; auto.
Qed.

Lemma tinterp_2_aux_plus_pred : forall m n:nat, m > n -> Nat.pred m - n = Nat.pred (m - n).
Proof.
  auto.
Qed.

Lemma tinterp_2_aux_nth_length :forall A:Type, forall l l2:list A, forall d e:A,
                                       nth (length l) (l ++ e::l2) d = e.
Proof.
  intros A l d e. induction l;auto.
Qed.

Lemma aux_nil: forall A:Type, forall l:list A, l = [] -> length l = 0.
Proof.
  induction l;auto.
  intro. discriminate.
Qed.

Lemma tinterp_2 : forall t' t v1 v2,
  tinterp (v1 ++ v2) (tsubst (length v1) t' t) =
  tinterp (v1 ++ (tinterp v2 t') :: v2) t.
(* QQ:  replacing variable (length v1) by (tlift (length v1) t' 0) in t
        equals to no replacement, incert (tinterp v2 t') between v1 and v2*)     
Proof.
  induction t; simpl; intuition; intros. (* induction sur t *)
  break; simpl;intuition.
  - rewrite H. assert (nth n (v1 ++ tinterp v2 t' :: v2) 0 = tinterp v2 t').
     + rewrite <- H, tinterp_2_aux_nth_length. reflexivity.
     + rewrite <- H, tinterp_2_aux_nth_length.  
       pattern v1 at 1; 
       rewrite <- app_nil_l, <- app_assoc, <- (aux_nil nat []).
       erewrite (tinterp_1 t' [] v1 v2), app_nil_l; reflexivity.
       reflexivity.
  - rewrite app_nth2; auto. rewrite app_nth2; auto.
    rewrite tinterp_2_aux_plus_pred. rewrite (tinterp_2_aux_nth (n - (length v1)) v2 0 (tinterp v2 t')) .
    + auto. + auto. + assumption.
  - repeat rewrite app_nth1;auto.
Qed.

 (* Interpretation of formulas *)
Fixpoint finterp v A :=
  match A with
    | Fequal t t' => tinterp v t = tinterp v t'
    | Ffalse => False
    | Fand B C => finterp v B /\ finterp v C
    | For B C => finterp v B \/ finterp v C
    | Fimplies B C => finterp v B -> finterp v C
    | Fexists B => exists n, finterp (n::v) B
    | Fforall B => forall n, finterp (n::v) B
  end.

Lemma finterp_1 : forall A v0 v1 v2,
  finterp (v0 ++ v1 ++ v2) (flift (length v1) A (length v0)) <->
  finterp (v0 ++ v2) A.
Proof. 
  induction A; split; simpl; auto; intros. 
  - (* t = t0 *)
    repeat rewrite tinterp_1 in H; assumption.
  - (* t = t0 *)
    repeat rewrite tinterp_1; assumption.
  - (* A1 /\ A2 *)
    split. 
    + destruct (IHA1 v0 v1 v2); destruct H; apply H0; assumption.
    + destruct (IHA2 v0 v1 v2); destruct H; apply H0; assumption.   
  - (* A1 /\ A2 *)
    destruct (IHA1 v0 v1 v2); destruct (IHA2 v0 v1 v2); destruct H; split; auto.
  - (* A1 \/ A2 *) 
    destruct (IHA1 v0 v1 v2); destruct (IHA2 v0 v1 v2);destruct H; auto. 
  - (* A1 \/ A2 *)
    destruct H; destruct (IHA1 v0 v1 v2); destruct (IHA2 v0 v1 v2); auto.
  - (* A1 -> A2 *)
    destruct (IHA1 v0 v1 v2); destruct (IHA2 v0 v1 v2); auto.
  - (* A1 -> A2 *)
    destruct (IHA1 v0 v1 v2); destruct (IHA2 v0 v1 v2); auto.
  - (* exists A *) 
    destruct H; exists x; destruct (IHA (x::v0) v1 v2); apply H0; assumption.
  - (* exists A *) 
    destruct H; exists x; destruct (IHA (x::v0) v1 v2); apply H1; assumption.
  - (* forall A *)
    destruct (IHA (n::v0) v1 v2); apply H0; simpl; exact (H n).
  - (* forall A *) 
    destruct (IHA (n::v0) v1 v2); simpl in H1; apply H1; exact (H n).
Qed.

 
Lemma finterp_2 : forall t' A v1 v2,
  finterp (v1 ++ v2) (fsubst (length v1) t' A) <->
  finterp (v1 ++ (tinterp v2 t') :: v2) A.
Proof.
  (* induction sur la structure de A *)
  induction A; simpl; intuition; intros. 
  - repeat rewrite <- tinterp_2; assumption.
  - repeat rewrite tinterp_2; assumption.
  - destruct (IHA1 v1 v2); apply H; assumption.
  - destruct (IHA2 v1 v2); apply H; assumption.
  - destruct (IHA1 v1 v2); apply H2; assumption.
  - destruct (IHA2 v1 v2); apply H2; assumption.
  - left; destruct (IHA1 v1 v2); apply H; assumption. 
  - right; destruct (IHA2 v1 v2); apply H; assumption.
  - left; destruct (IHA1 v1 v2); apply H1; assumption.
  - right; destruct (IHA2 v1 v2); apply H1; assumption.
  - apply IHA2; apply H; apply IHA1; assumption.
  - apply IHA2; apply H; apply IHA1; assumption.
  - destruct H; exists x; apply (IHA (x::v1) v2); assumption.
  - destruct H; exists x; apply (IHA (x::v1) v2); assumption.
  - apply (IHA (n::v1) v2); eapply H.
  - apply (IHA (n::v1) v2); eapply H.
Qed.

Lemma finterp_3 : forall n A,
  (forall v, finterp v A) -> (forall v, finterp v (nFforall n A)).
Proof.
  (* induction sur n*)
  induction n; simpl; auto.
Qed.


(* Interpretation of contexts *)

Definition cinterp v Γ := forall A, In A Γ -> finterp v A.

Lemma clift_1 : forall Γ A, In A Γ -> In (flift 1 A 0) (clift 1 Γ 0).
Proof.
  induction Γ;auto.
  - intros. destruct H.
    + rewrite H. unfold clift. simpl. auto.
    + assert (In (flift 1 A 0) (clift 1 Γ 0)) as H1.
      ++ auto.
      ++ unfold In in *. simpl in *. auto.
Qed.
      
Lemma soundness_rules_aux_1emma_1 :
  forall A Γ, In A (clift 1 Γ 0) -> exists B, In B Γ /\ flift 1 B 0 = A.
Proof.
  induction Γ. (* induction sur la structure de Γ *)
  - (* [] *)
    intros H; destruct H.
  - (* a::Γ' *)
    intros H_A; destruct H_A.
    + (* cas A = A *)
      exists a. split;auto; unfold In; auto.
    + (* cas A in Γ' *)
      simpl; assert (H_exists := IHΓ H); destruct H_exists as (x, Hyp);
      exists x; split.
      ++ right; apply Hyp.
      ++ apply Hyp.
Qed.


(* Lemme auxilaire:
       une formule A est vraie sous une valuation v
       ssi 
       la formule obtenue en ajoutant une variable #0 qui n'a pas d'occurrence 
       dans une formule A est vraie  *)
Lemma soundness_rules_aux_3 : forall A n v,
      finterp v A <-> finterp (n::v) (flift 1 A 0).
Proof.
  split; assert (H := finterp_1 A [] [n] v); simpl in H; apply H.
Qed.  

(* Lemme auxiliaire *)
Lemma soundness_rules_aux_2 : forall Γ v A, cinterp v (A::Γ) -> 
  (finterp v A /\ cinterp v Γ).
Proof.
  induction Γ.
  - intros v A H.
    unfold cinterp in H. simpl in H.
    split.
    + assert (H1 := H A).
      auto.
    + unfold cinterp. auto.
  - intros v A H. split.
    + unfold cinterp in H. simpl in H. 
      assert (H1 := H A). auto.
    + unfold cinterp in H. unfold cinterp. simpl in *.
      auto.
Qed.

(* Lemme auxiliare*)
Lemma soundness_rules_aux_1 : forall Γ n v,
      cinterp v Γ <-> cinterp (n::v) (clift 1 Γ 0).
Proof.
  split.
  revert n v.
  induction Γ.
  - unfold cinterp. simpl. auto.
  - simpl. intros n v H.
    assert (H1 := soundness_rules_aux_2 Γ v a H).
    destruct H1.
    assert (H2 := IHΓ n v H1).
    assert (H3 := soundness_rules_aux_3 a n v). destruct H3 as (H3,H5).
    assert (H6 := H3 H0).
    intros A H4. simpl in H4. 
    destruct H4.
    + rewrite <- H4. assumption.
    + apply H2. assumption.
  - unfold cinterp. intros H A H1.
    assert ( H2 := soundness_rules_aux_3). 
    apply (H2 A n v).
    apply H.
    apply clift_1. assumption.
Qed.

Lemma soundness_rules : forall Γ A, 
      Γ:-A -> (forall v, cinterp v Γ -> finterp v A).
Proof. 
  intros Γ0 A0 H. 
  induction H. (* induction sur la dernière règle de la déduction *)
  - (* Rax *)
    auto.
  - (* Rfalse_e *)
    intros; assert ( finterp v Ffalse ); try (exact (IHrule v H0) || destruct H1).
  - (* Rand_i *)
    intros; split; try (apply IHrule1 || apply IHrule2);auto.
  - (* Rand_e1 *)
    intros; assert ( finterp v (B /\ C)). exact (IHrule v H0).
    destruct H1; assumption.
  - (* Rand_e2 *) intros; assert ( finterp v (B /\ C)). exact (IHrule v H0).
    destruct H1; assumption.
  - (* Ror_i1 *)
    intros; simpl; left; apply IHrule; assumption.
  - (* Ror_i2 *) 
    intros; simpl; right; apply IHrule; assumption.
  - (* Ror_e *)
    intros; assert ( finterp v (B \/ C)). exact (IHrule1 v H2). destruct H3.
    + apply IHrule2; unfold cinterp; intros A0 H4;
      destruct H4.
      ++ rewrite <- H4; assumption.
      ++ auto.
    + apply IHrule3; unfold cinterp; intros A0 H4;
      destruct H4.
      ++ rewrite <- H4; assumption.
      ++ auto.
  - (* Rimpl_i *)
    intros; simpl; intros H_B; apply IHrule; unfold cinterp; intros A0 H_A0.
    destruct H_A0.
    + rewrite <- H1; assumption.
    + auto.
  - (* Rimpl_e *)
    intros;
    assert (H_B_implies_C := IHrule1 v H1);
    assert (H_B := IHrule2 v H1);
    auto.
  - (* Rforall_i *) 
    intros. simpl. intros n. apply IHrule.
    unfold cinterp in *.
    intros A H_A.
    assert (lemma_aux_1 := soundness_rules_aux_1emma_1 A Γ H_A).
    destruct lemma_aux_1 as (A0,(H_B_in, H_B_A)).
    assert (H_finterp_A0 := H0 A0 H_B_in).
    rewrite <- H_B_A.
    apply (finterp_1 A0 [] [n] v).
    simpl. assumption.
  - (* Rforall_e *) 
    intros. simpl in IHrule.
    assert (Lemma_2 := IHrule v H0).
    assert (Lemma_1 := finterp_2 t B [] v).
    simpl in Lemma_1.
    rewrite Lemma_1.
    apply Lemma_2.
  - (* Rexists_i *)
     intros v H_cinterp.
    assert (H_finterp_nv := IHrule v H_cinterp).
    simpl.
    assert (Lemma_1 := finterp_2 t B [] v). 
    simpl in Lemma_1.   
    destruct Lemma_1.
    assert (H2 := H0 H_finterp_nv).
    exists (tinterp v t). assumption.
  - (* Rexists_e *)
    intros.
    assert (H_exists_n_interp_nv_B := IHrule1 v H1); simpl in H_exists_n_interp_nv_B.
    destruct H_exists_n_interp_nv_B as (n,interp_nv_B).
    assert (cinterp (n::v) (clift 1 Γ 0)) as H2. 
    + apply soundness_rules_aux_1. assumption.
    + assert (cinterp (n::v) (B::clift 1 Γ 0)) as H3.
      ++ intros C H3. destruct H3.
          +++ rewrite <- H3. auto.
          +++ auto.
      ++   
    assert (H4 := soundness_rules_aux_3).
    eapply H4.
    apply IHrule2.
    exact H3.
Qed.

(* Lemme auxiliaire *)
Lemma aux_interp_1 : forall t n v,
  tinterp (n :: v) (tsubst 0 (Tsucc # 0) (tlift 1 t 1)) = tinterp (S n :: v) t.
Proof. 
  (* induction sur t et puis sur n *)
  induction t; simpl; auto.
  induction n; simpl;auto.
Qed.


(*qq pour demontrer :   
            finterp n::v (fsubst 0 (Tsucc #0) (flift A 1) = finterp (S n::v) A
     on definit la fonction suivante :
*) 
Fixpoint Tn n := 
  match n with
  | 0 => Tzero
  | S n' => Tsucc (Tn n')
  end.
(*qq pour tout n, Tn n est un un terme clos *)
Lemma cterm_Tn_n : forall n, cterm 0 (Tn n).
Proof.
    induction n.
    auto. simpl. auto.
Qed.

(* Lemma auxiliaire *)
Lemma tlift_0_t_eq_t: forall t n, tlift 0 t n = t.
Proof.
    induction t.
    - unfold tlift. simpl. intro n0. destruct (n0 <=? n); auto.
    - auto.
    - simpl. intro n. f_equal. auto.
    - simpl. intro n. rewrite (IHt1 n),(IHt2 n). reflexivity.
    - simpl. intro n. rewrite (IHt1 n),(IHt2 n). reflexivity.
Qed.

(* Lemma auxiliaire *)
Lemma flift_0_A_eq_A: forall A n, flift 0 A n = A.
Proof.
  induction A.
  - simpl. intro n. repeat rewrite tlift_0_t_eq_t. reflexivity.
  - auto.
  - simpl. intro n. repeat rewrite IHA1,IHA2. reflexivity.
  - simpl. intro n. repeat rewrite IHA1,IHA2. reflexivity.
  - simpl. intro n. repeat rewrite IHA1,IHA2. reflexivity.
  - simpl. intro n. rewrite IHA. reflexivity.
  - simpl. intro n. rewrite IHA. reflexivity.
Qed. 

(* Lemma auxiliaire *)
Lemma finterp_apres_une_substitution : 
  forall n A v, 
    finterp (n::v) A <-> finterp v (fsubst 0 (Tn n) A).
Proof.
    intros n A v.
    assert (H0 :=finterp_2).
    assert (H1 := H0 (Tn n) A [] v).
    simpl in H1.
    assert (forall v n, tinterp v (Tn n) = n) as H2.
    - induction n0; simpl; auto.
    - rewrite <- (H2 v n) at 1. destruct H1; split; assumption.
Qed.

Lemma soundness_axioms : forall A, PeanoAx A -> forall v, finterp v A.
Proof. 
  intros A H.  
  induction H; simpl; auto. (* induction sur (PeanoAx A) *)
  apply finterp_3; revert H; simpl.
  intros H1 v H2.  
  destruct H2 as (H3,H4). 
  (* montrer que:    forall n0 : nat, finterp (n0 :: v) A *)
  induction n0. (* par induction sur n0 *)
  + (* ind_init:  finterp (0 :: v) A *)
    assert (aux_1 := finterp_2). rewrite <- (aux_1 Tzero A [] v).
    simpl in *. assumption.
  + (* ind_next:  montrer que:
              finterp (n0 :: v) A  ==> finterp (S n0 :: v) *)
    assert (H5 := H4 n0 IHn0).
    assert (H6 := finterp_apres_une_substitution).
    assert (H7 := H6 n0 (fsubst 0 (Tsucc # 0) (flift 1 A 1)) v).
    destruct H7 as (H8,H9).
    assert (H10 := H8 H5).

    assert (H_f_subst_subst := fsubst_4).
    assert (H11 := H_f_subst_subst (flift 1 A 1) 0 (Tsucc # 0) 0 (Tn n0)).
    simpl in H11.
    assert ( finterp v
        (fsubst 0 (Tsucc (tlift 0 (Tn n0) 0))
        (fsubst 1 (Tn n0) (flift 1 A 1)))) as H12.
    ++ f_equal. rewrite <- H11. assumption.
    ++ assert (finterp v
        (fsubst 0 (Tsucc (tlift 0 (Tn n0) 0))
           (fsubst 1 (Tn n0) (flift 1 A 1))) <-> finterp (S n0 :: v) A).
    +++ assert (tlift 0 (Tn n0) 0 = (Tn n0)) as H13. 
       ++++ (* monter  tlift 0 (Tn n0) 0 = Tn n0 *)
           apply cterm_2. 
           (* Monter  cterm 0 (Tn n0)*)
           apply cterm_Tn_n.
       ++++ rewrite H13.
            assert (fsubst 1 (Tn n0) (flift 1 A 1) = A) as H14.
            assert (H15 := fsubst_1). rewrite H15;auto. apply flift_0_A_eq_A.
            rewrite H14. 
            assert (Tsucc (Tn n0) = Tn (S n0)) as H16;auto.
            rewrite H16. rewrite finterp_apres_une_substitution. reflexivity.
    +++ apply H. assumption. 
Qed.

Theorem soundness : forall A, Thm A -> forall v, finterp v A. 
Proof. 
  intros A Hyp v. 
  unfold Thm in Hyp. (* par def de Thm*)
  destruct Hyp as (axiomes,Hyp).
  destruct Hyp. 
  apply (soundness_rules axiomes).
  - assumption.
  - unfold cinterp.
    intros A0 H1.
    apply soundness_axioms.
    apply H. 
    assumption.
Qed.    

Theorem coherence : ~Thm Ffalse.
Proof.
  intro H.     
      (*supposons (Thm Ffalse), on a alors une preuve de False dans LI*)
  change (finterp [] Ffalse).  
      (* parce que, par exemple, on peut demontrer (finterp [] Ffalse) *)
  apply soundness.
  assumption.
Qed.
