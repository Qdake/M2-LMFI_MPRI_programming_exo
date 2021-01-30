
Inductive term :=
| Var : nat -> term
| Lam : term -> term
| App : term -> term -> term.


Check Lam (Lam (Lam (App 
                         (App (Var 1) (Lam (App (Var 2) 
                                                (Var 0))))
                         (Var 3)))):term.

(* lift_level lvl n t  retourne le terme t dans lequel les variables libres
   d'indice superieurs à lvl ont été augmentés de n.  *)
Fixpoint lift_level (lvl:nat) (n:nat) (t:term) : term :=
match t with
| Var k => if Nat.leb lvl k then Var (k + n) else t
| Lam t' => Lam (lift_level (lvl+1) n t')
| App t1 t2 => App (lift_level lvl n t1) (lift_level lvl n t2)
end.

Definition t1 := Lam (Lam (App (App (Var 4) (Var 2))
                               (Lam (App (Var 1) (Var 3))))).

Compute lift_level 4 2 t1.

Definition lift (n:nat) (t:term) : term := lift_level 1 n t.

Compute lift 3 t1.

Fixpoint subst (lvl:nat) (t u:term) : term :=
match t with
| Var k => if Nat.eqb k lvl then u else t
| Lam t' => Lam (subst (lvl + 1) t' (lift 1 u))
| App t1 t2 => App (subst lvl t1 u) (subst lvl t2 u)
end.

Definition t2 := Lam (App (Var 1) (Var 8)).
Compute subst 0 t2 (Var 2).

Fixpoint search_beta_redex (t:term) : option term := 
match t with
| Var _ => None
| Lam t' => search_beta_redex t'
| App (Lam t1) t2 => Some t
| App t1 t2 => let res := (search_beta_redex t1) 
               in match res with
               | None => search_beta_redex t2
               | Some t' => Some t'
               end
end.

Compute search_beta_redex t2.
Compute search_beta_redex t1.
Definition t3 := App (Var 3) (App (Lam (Var 4)) (App (Lam (Var 2)) (Lam (Var 1)))).
Compute search_beta_redex t3.

Definition beta (t:term) :=
  let res := search_beta_redex t in
  match res with
  | None => t
  | Some (App (Lam t1) t2) => subst 0 t1 t2
  | _ => t  (* impossible*)
  end.

(* ....... *)


 

