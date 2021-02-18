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


(* qq:  si k <= k' et n + k >= k' alors +n to all var >= k et puis +n' to 
  all var  k'
        est egal a    + (n' + n) to all var >= k.
*)
Lemma tlift_1 : forall t n n' k k', k <= k' -> k' <= k + n ->
  tlift n' (tlift n t k) k' = tlift (n' + n) t k.
Proof.
  induction t; intros; simpl; f_equal; repeat break; auto.
Qed.

(* + n to all var >= k et puis +n' to all var >= k' 
   =   + n' to all var >= k'  et puis +n to all var >= n'+k (i.e. tous les 
      variabl qui sont initialement >= k') *)
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

(* qq :  +(n+1) to all var >= k (there's no x anymore)  and then  subs 
        var x by t'    =    *)
Lemma tsubst_1 : forall t x t' n k, k <= x -> x <= k + n ->
  tsubst x t' (tlift (S n) t k) = tlift n t k.

Lemma tsubst_2 : forall t x t' n k, k <= x ->
  tlift n (tsubst x t' t) k = tsubst (n + x) t' (tlift n t k).

Hint Resolve tsubst_1 tsubst_2.

Lemma tsubst_3 : forall t x t' n k,
  tlift n (tsubst x t' t) (x + k) =
  tsubst x (tlift n t' k) (tlift n t (x + S k)).

Lemma tsubst_4 : forall t x t' y u',
  tsubst (x + y) u' (tsubst x t' t) =
  tsubst x (tsubst y u' t') (tsubst (x + S y) u' t).

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
  (* QQ: soient n, t, si (cterm n t) alors toute variable de t est < n, donc l'augmenter les variables
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
  (* QQ: soient n, t, si (cterm n t) alors toute variable de t est < n, 
     donc substitue la viariable j >= n de t par t' ne change rien. *) 
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
  (* QQ: soient n, t, supposons (cterm n t) i.e. toute variable de t est < S n, 
         soit t', supposons (cterm 0 t') i.e. toute variable de t' est < 0, c-a-d terme constant
         alors en substituant toute variable n par t', on obtien un terme de degree < n*)
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


Lemma flift_2 : forall A n n' k k', k' <= k ->
  flift n' (flift n A k) k' = flift n (flift n' A k') (n' + k).


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

Lemma fsubst_3 : forall A x t' n k,
  flift n (fsubst x t' A) (x + k) =
  fsubst x (tlift n t' k) (flift n A (x + S k)).

Lemma fsubst_4 : forall A x t' y u',
  fsubst (x + y) u' (fsubst x t' A) =
  fsubst x (tsubst y u' t') (fsubst (x + S y) u' A).

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

Lemma cformula_2 : forall n A, cformula n A -> forall k, flift k A n = A.

Lemma cformula_3 : forall n A, cformula n A ->
  forall t' j, n <= j -> fsubst j t' A = A.

Lemma cformula_4 : forall n A, cformula (S n) A ->
  forall t', cterm 0 t' -> cformula n (fsubst n t' A).


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

Lemma Rnot_i : forall Γ A, (A::Γ):-Ffalse -> Γ:- ~A.

Lemma Rnot_e : forall Γ A, Γ:-A -> Γ:- ~A -> Γ:-Ffalse.
  
Lemma Riff_i : forall Γ A B,
  (A::Γ):-B -> (B::Γ):-A -> Γ:-(Fiff A B).


Lemma nFforall_1 : forall n x t A,
  fsubst x t (nFforall n A) = nFforall n (fsubst (n + x) t A).


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

nFforall n (
      fsubst 0 Tzero A /\
      Fforall (A ==> fsubst 0 (Tsucc #0) (flift 1 A 1)) ==> 
      Fforall A
    )


(* Definition of theorems over Heyting Arithmetic.

   NB: we should normally restrict theorems to closed terms only,
   but this doesn't really matter here, since we'll only prove that
   False isn't a theorem. *)

Definition Thm T :=
  exists axioms, (forall A, In A axioms -> PeanoAx A) /\ (axioms:-T). 

Lemma HA_n_Sn_auxilaire_PeanoAx_forall_n_not_eq_n_sn : PeanoAx (nFforall (S 0) (
      fsubst 0 Tzero (~ #0 = Tsucc # 0) /\
      Fforall ((~ #0 = Tsucc # 0) ==> fsubst 0 (Tsucc #0) (flift 1 (~ #0 = Tsucc # 0) 1)) ==> Fforall (~ #0 = Tsucc # 0)
    )).
Proof.
  apply pa_ind. unfold Fnot. 
  apply cformula_implies.
  - apply cformula_equal.
    + constructor. auto.
    + constructor. constructor. auto.
  - constructor.
Qed. 


(* Example of theorem *)
Lemma HA_n_Sn :  Thm (Fforall (Fnot (Fequal #0 (Tsucc #0)) )).

Definition valuation := list nat.
 
Fixpoint tinterp (v:valuation) t :=
  match t with
    | Tvar j => nth j v O
    | Tzero => O
    | Tsucc t => S (tinterp v t)
    | Tplus t t' => tinterp v t + tinterp v t'
    | Tmult t t' => tinterp v t * tinterp v t'
  end.


Lemma tinterp_1_aux_arith : forall m n:nat, m <= n -> exists k:nat, m + k = n.

Lemma tinterp_1 : forall t v0 v1 v2,
  tinterp (v0++v1++v2) (tlift (length v1) t (length v0)) =
  tinterp (v0++v2) t.

Lemma tinterp_2_aux_nth {A:Type}: forall n:nat, forall l:list A, forall d k:A, n >= 1 -> nth (Nat.pred n) l d = nth n (k::l) d.

Lemma tinterp_2_aux_plus_pred : forall m n:nat, m > n -> Nat.pred m - n = Nat.pred (m - n).

Lemma tinterp_2_aux_nth_length :forall A:Type, forall l l2:list A, forall d e:A,
                                       nth (length l) (l ++ e::l2) d = e.

Lemma aux_nil: forall A:Type, forall l:list A, l = [] -> length l = 0.

Lemma tinterp_2 : forall t' t v1 v2,
  tinterp (v1 ++ v2) (tsubst (length v1) t' t) =
  tinterp (v1 ++ (tinterp v2 t') :: v2) t.
(* QQ:  replacing variable (length v1) by (tlift (length v1) t' 0) in t
        equals to no replacement, incert (tinterp v2 t') between v1 and v2*)     

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

 
Lemma finterp_2 : forall t' A v1 v2,
  finterp (v1 ++ v2) (fsubst (length v1) t' A) <->
  finterp (v1 ++ (tinterp v2 t') :: v2) A.

Lemma finterp_3 : forall n A,
  (forall v, finterp v A) -> (forall v, finterp v (nFforall n A)).


(* Interpretation of contexts *)

Definition cinterp v Γ := forall A, In A Γ -> finterp v A.

(* Soundess of deduction rules *)
(*Lemma finterp_0 : forall A v0 v1,
  finterp (v0 ++ v1 ++ v2) (flift (length v1) A (length v0)) <->
  finterp (v0 ++ v2) A.


Lemma finterp_0 : forall A v0 v1,
  finterp (v0 ++ v1 ++ v2) (flift (length v1) A (length v0)) <->
  finterp (v0 ++ v2) A.
*)

Lemma soundness_rules_aux_1emma_1 :
  forall A Γ, In A (clift 1 Γ 0) -> exists B, In B Γ /\ flift 1 B 0 = A.

(*Lemma soundness_rules_aux_1emma_2 :
  forall v v1 Γ, cinterp v Γ -> cinterp (v++v1) Γ.
Proof.
    intros v v1 Γ H. revert v Γ H. induction v1; unfold cinterp;simpl;intros.
  - rewrite app_nil_r. auto.
  - assert (H1 : forall {A} (x:A) (l:list A), x::l = [x] ++ l);auto.
    rewrite H1.
    assert (H2 := finterp_1 A v [a] v1).
    destruct H2.
    apply (IHv1 (v++[a]) Γ).


Lemma finterp_1 : forall A v0 v1 v2,
  finterp (v0 ++ v1 ++ v2) (flift (length v1) A (length v0)) <->
  finterp (v0 ++ v2) A.

  *)



Lemma soundness_rules : forall Γ A, 
      Γ:-A -> (forall v, cinterp v Γ -> finterp v A).

Lemma soundness_axioms : forall A, PeanoAx A -> forall v, finterp v A.


Theorem soundness : forall A, Thm A -> forall v, finterp v A.
   

Theorem coherence : ~Thm Ffalse.


  



