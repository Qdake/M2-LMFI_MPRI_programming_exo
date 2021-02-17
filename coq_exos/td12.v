Set Implicit Arguments.

Print bool.
Inductive color : Set := 
| Bl : color
| Wh : color.

Definition inv_color c : color :=
match c with
| Bl => Wh
| Wh => Bl
end.


Section Triple.

Variable X:Type.

Definition triple : Type := X * X * X.

Definition triple_x (x:X) := (x,x,x).

Definition triple_map (f:X->X) (t:triple) : triple :=
match t with
|(x,y,z) => ((f x),(f y),(f z))
end.

Inductive pos : Set :=
| A : pos
| B : pos
| C : pos.

Definition triple_proj (i:pos) (t:triple) : X :=
match i,t with
| A, (a,_,_) => a
| B, (_,b,_) => b
| C, (_,_,c) => c
end.

Definition triple_map_select (f:X->X) (i:pos) (t:triple) : triple :=
match i,t with
| A, (a,b,c) => ((f a),b,c)
| B, (a,b,c) => (a,(f b),c)
| C, (a,b,c) => (a,b,(f c))
end.

End Triple.

Definition board : Type := triple (triple color).
(*    (l1,
       l2,
       l3)  
*)

Definition white_board : board := triple_x (triple_x Wh).

Definition start : board :=
((Wh,Wh,Bl),
 (Bl,Wh,Wh),
 (Bl,Bl,Bl)).

Definition target :board :=
 ((Bl,Bl,Bl),
  (Wh,Bl,Wh),
  (Bl,Bl,Wh)).


(* Configuration manipulations *)
(* ligne i colonne j *)
Definition board_proj (b:board) (l c:pos) : color :=
  triple_proj c (triple_proj l b).


Definition inv_row (b:board) (l:pos) : board :=
let '(l1,l2,l3) := b in
  match l with
  | A => ((triple_map inv_color l1),l2,l3)
  | B => (l1,(triple_map inv_color l2),l3)
  | C => (l1,l2,(triple_map inv_color l3))
  end.

Definition inv_col (b:board) (c:pos) : board :=
let '(l1,l2,l3) := b in
  ((triple_map_select inv_color c l1),
   (triple_map_select inv_color c l2),
   (triple_map_select inv_color c l3)).

Compute inv_col target C.


Definition move (b1 b2 : board) : Prop :=
  exists i:pos, inv_row b1 i = b2 \/
                inv_col b1 i = b2.

Definition symmetric_binary_relation {X:Type} (R:X->X->Prop)
 : Prop := forall x y:X, R x y -> R y x.

Lemma move_symmetric : symmetric_binary_relation move.
Admitted.

Inductive moves : board -> board -> Prop :=
| moves_refl : forall b : board, moves b b
| moves_step : forall b1 b2 b3 : board, moves b1 b2 -> moves b2 b3 
                                        -> moves b1 b3.

Definition reflexive {X:Type} (R:X->X->Prop)
 : Prop := forall x :X, R x x.

Definition transitive {X:Type} (R:X->X->Prop)
 : Prop := forall x y z : X, R x y -> R y z -> R x z.

Lemma moves_reflexive : reflexive moves.
Admitted.


Lemma moves_symmetric : symmetric_binary_relation moves.
Admitted.
Lemma moves_transitive : transitive moves.
Admitted.

Theorem moves_start_target : moves start target.
Admitted.

Definition inv_col_if_Bl (b:board) (i:pos) (c:color) :=
match c with
| Bl => inv_col b i 
| Wh => b
end.

Definition inv_row_if_Bl (b:board) (i:pos) (c:color) :=
match c with
| Bl => inv_row b i 
| Wh => b
end.

Definition force_white (b:board) : board :=
  let b := inv_col_if_Bl b A (board_proj b A A) in
    let b := inv_col_if_Bl b B (board_proj b A B) in
      let b := inv_col_if_Bl b C (board_proj b A C) in
        let b := inv_row_if_Bl b B (board_proj b B A) in
          let b := inv_row_if_Bl b C (board_proj b C A) in
            b.
    



(* Normalization 

Define a function force_white : board -> board which flips
some rows and/or some columns of a configuration in such a
way that both the obtained first row and first column is
entirely white.
Prove that for all configuration b we have moves b (force_white b).
Prove that move b1 b2 -> force_white b1 = force_white b2.
Prove that moves b1 b2 <-> force_white b1 = force_white b2.
Deduce that ~(moves white_board start), and also obtain a simplified proof that moves start target.
*)

(* Decidability of the moves relation 

Consider a relation R : X->X->Prop defined on some domain X. In Coq, we express that this relation is decidable (i.e. decidable via a computable algorithm) via the following statement :
forall x y : X, { R x y }+{ ~R x y }
Here the {...}+{...} syntax designates the computational disjunction : named sumbool internally, it is defined in Type, unlike the usual disjunction \/ which is defined in Prop. And the above statement is hence a form of excluded-middle, but a computational excluded-middle that cannot be deduced from the propositional excluded-middle.

Show that the equality x = y is decidable on type color.
Show that whenever the equality is decidable on a type X, then it is also the case for the equality on triple X.
Deduce that the equality is decidable on the type board.
Thanks to all the previous proofs, conclude now that the moves relation is decidable.
Use the Coq extraction to obtain a corresponding program and test it.

*)

(*
Section Triple.

Variable X:Type.

Inductive triple : Type := prod(prod X X) X.

Definition triple_x (x:X) := triplet x x x.

Definition triple_map (f:X->X) (t:triple) : triple :=
match t with
|triplet x y z => triplet (f x) (f y) (f z)
end.

Inductive pos : Set :=
| A : pos
| B : pos
| C : pos.

Definition triple_proj (i:pos) (t:triple) : X :=
match i,t with
| A, triplet a _ _ => a
| B, triplet _ b _ => b
| C, triplet _ _ c => c
end.

Definition triple_map_select (f:X->X) (i:pos) (t:triple) : triple :=
match i,t with
| A, triplet a b c => triplet (f a) b c
| B, triplet a b c => triplet a (f b) c
| C, triplet a b c => triplet a b (f c)
end.

End Triple.

Inductive board : Type := 
| tableau : triple color -> triple color -> triple color -> board.

Definition white_board : board := 
tableau (triple_x Wh) (triple_x Wh) (triple_x Wh).
*)


