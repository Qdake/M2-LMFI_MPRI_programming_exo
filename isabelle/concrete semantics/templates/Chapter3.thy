theory Chapter3
imports "HOL-IMP.BExp"
        "HOL-IMP.ASM"
begin

(*
\section*{Chapter 3}

\exercise
To show that @{const asimp_const} really folds all subexpressions of the form
@{term "Plus (N i) (N j)"}, define a function
*)

fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N _) = True"
| "optimal (V _) = True"
| "optimal (Plus (N _) (N _)) = False"
| "optimal (Plus a1 a2) = (case ((optimal a1),(optimal a2)) of
      (False,_) \<Rightarrow> False
      |(_,False) \<Rightarrow> False
      |_ \<Rightarrow> True)"
(*
that checks that its argument does not contain a subexpression of the form
@{term "Plus (N i) (N j)"}. Then prove that the result of @{const asimp_const}
is optimal:
*)

lemma "optimal (asimp_const a)"
  apply(induction a rule:asimp_const.induct)
  apply(auto split:aexp.split)
  done
(*
fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)"
*)

lemma "optimal (asimp_const a)" (is "?P a")
proof (induction a rule:asimp_const.induct)
  fix n
  let ?a = "N n"
  show "?P ?a" by simp
next 
  fix x 
  let ?a = "V x"
  show "?P ?a" by simp
next 
  fix a1 a2
  assume ind1: "optimal (asimp_const a1)" "optimal (asimp_const a2)"
  let ?a = "Plus a1 a2"
  show "?P ?a" 
    using ind1 by (auto split : aexp.split)
qed



(*
This proof needs the same @{text "split:"} directive as the correctness proof of
@{const asimp_const}. This increases the chance of nontermination
of the simplifier. Therefore @{const optimal} should be defined purely by
pattern matching on the left-hand side,
without @{text case} expressions on the right-hand side.
\endexercise


\exercise
In this exercise we verify constant folding for @{typ aexp}
where we sum up all constants, even if they are not next to each other.
For example, @{term "Plus (N 1) (Plus (V x) (N 2))"} becomes
@{term "Plus (V x) (N 3)"}. This goes beyond @{const asimp}.
Below we follow a particular solution strategy but there are many others.

First, define a function @{text sumN} that returns the sum of all
constants in an expression and a function @{text zeroN} that replaces all
constants in an expression by zeroes (they will be optimized away later):*)

fun sumN :: "aexp \<Rightarrow> int" where
  "sumN (N n) = n"
| "sumN (V x) = 0"
| "sumN (Plus a1 a2) = (+) (sumN a1) (sumN a2)"

fun zeroN :: "aexp \<Rightarrow> aexp" where
  "zeroN (N n) = N 0"
| "zeroN (V x) = V x"
| "zeroN (Plus a1 a2) = Plus (zeroN a1) (zeroN a2)"

(*
Next, define a function @{text sepN} that produces an arithmetic expression
that adds the results of @{const sumN} and @{const zeroN}. Prove that
@{text sepN} preserves the value of an expression.
*)

definition sepN :: "aexp \<Rightarrow> aexp" where
  "sepN a = Plus (N (sumN a)) (zeroN a)"

lemma aval_sepN: "aval (sepN t) s = aval t s"
  apply(induction t)
  apply(auto simp add : sepN_def)
  done

lemma aval_sepN_isar: "aval (sepN t) s = aval t s" (is "?P t s")
proof (induction t arbitrary : s)
  fix x s
  let ?t = "N x" 
  have "aval (sepN ?t) s = (aval (Plus (N (sumN ?t)) (zeroN ?t)) s)" by (auto simp add : sepN_def)
  also have "(aval (Plus (N (sumN ?t)) (zeroN ?t)) s) = (aval ?t s)" by simp
  finally show "?P ?t s" by simp
next
  fix x s
  let ?t = "V x"
  show "?P ?t s" by (simp add : sepN_def)
next
  fix t1 t2 s
  assume IH : "\<And>s. aval (sepN t1) s = aval t1 s" "\<And>s. aval (sepN t2) s = aval t2 s"
  let ?t = "Plus t1 t2"
  have "aval (sepN (Plus t1 t2)) s = aval (Plus (N (sumN ?t)) (zeroN ?t)) s" using sepN_def by simp
  also have "... = (+) (aval (N (sumN ?t)) s) (aval (zeroN ?t) s)" by simp
  also have "... = (+) ((+) (aval (N (sumN t1)) s) (aval (N (sumN t2)) s))
                       ((+) (aval (zeroN t1) s) (aval (zeroN t2) s))" by simp
  also have "... = (+) ((+) (aval (N (sumN t1)) s) (aval (zeroN t1) s))
                       ((+) (aval (N (sumN t2)) s) (aval (zeroN t2) s))" by simp
  also have "... = (+) (aval (sepN t1) s)
                       (aval (sepN t2) s)" using sepN_def by simp
  also have "... = aval ?t s" using IH by simp
  finally show "?P ?t s" using sepN_def by auto
qed

(*
Finally, define a function @{text full_asimp} that uses @{const asimp}
to eliminate the zeroes left over by @{const sepN}.
Prove that it preserves the value of an arithmetic expression.
*)

definition full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp a = asimp (sepN a)"

lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
  apply(induction t)
  apply(auto simp add:full_asimp_def sepN_def)
  done

lemma aval_full_asimp_isar : "aval (full_asimp t) s = aval t s" (is "?P t s")
proof (induction t)
  fix x 
  let ?t = "N x"
  show "?P ?t s" by (simp add : full_asimp_def sepN_def)
next
  fix x
  let ?t = "V x"
  show "?P ?t s" by (simp add : full_asimp_def sepN_def)
next
  fix t1 t2
  assume ind : "aval (full_asimp t1) s = aval t1 s" "aval (full_asimp t2) s = aval t2 s"
  let ?t = "Plus t1 t2"
  have "aval (full_asimp ?t) s = aval (asimp (sepN ?t)) s" by (simp add : full_asimp_def)
  also have "... = aval (asimp (Plus (N (sumN ?t)) (zeroN ?t))) s" by (simp add : sepN_def)
  finally show "?P ?t s" using ind full_asimp_def sepN_def by simp
qed
  
 (*
Substitution is the process of replacing a variable
by an expression in an expression. Define a substitution function
*)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x a (V y) = (if x = y then a else V y)"
| "subst _ _ (N n) = N n"
| "subst x a1 (Plus a2 a3) = Plus (subst x a1 a2) (subst x a1 a3)"

(*
such that @{term "subst x a e"} is the result of replacing
every occurrence of variable @{text x} by @{text a} in @{text e}.
For example:
@{lemma[display] "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" by simp}

Prove the so-called \concept{substitution lemma} that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
*)

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
    apply(auto)
  done
lemma subst_lemma_isar : "aval (subst x a e) s = aval e (s (x := aval a s))" (is "?P e")
proof (induction e)
  fix n 
  let ?e = "N n"
  show "?P ?e" by auto 
next
  fix v
  let ?e = "V v"
  show "?P ?e" by auto
next
  fix e1 e2
  assume ind : "aval (subst x a e1) s = aval e1 (s(x := aval a s))"
               "aval (subst x a e2) s = aval e2 (s(x := aval a s))"
  let ?e ="Plus e1 e2"
  have "aval (subst x a ?e) s = aval (Plus (subst x a e1) (subst x a e2)) s" by simp
  also have "... = (aval (subst x a e1) s) + (aval (subst x a e2) s)" by simp
  also have "... = (aval e1 (s(x := aval a s))) + (aval e2 (s(x := aval a s)))" using ind by simp
  also have "... = aval (Plus e1 e2) (s (x := aval a s))" by simp
  (* finally show "?P ?e" by simp   *) (* qqq : pourquoi pas *) 
  finally show "aval (subst x a ?e) s = aval ?e (s (x := aval a s))" by simp
qed

(*
As a consequence prove that we can substitute equal expressions by equal expressions
and obtain the same result under evaluation:
*)

lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(induction e)
    apply(auto)
  done

lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
proof-
  fix a1 a2 s
  assume H : "aval a1 s = aval a2 s"
  show "aval (subst x a1 e) s = aval (subst x a2 e) s" (is "?P e")
  proof (induction e)
    fix n
    let ?e = "N n"
    show "?P ?e" by simp
  next
    fix v
    let ?e = "V v"
(*    have "aval (subst x a1 ?e) s = aval (if x = v then a1 else V v) s" (is "?Q = ?R")
      by simp
    also have "... = (if x = v then aval a1 s else aval (V v) s)" by simp
    finally show "?P ?e" using \<open>aval a1 s = aval a2 s\<close> by simp  *)
    show "?P ?e" using \<open>aval a1 s = aval a2 s\<close> by simp
  next
    fix e1 e2
    assume id : "aval (subst x a1 e1) s = aval (subst x a2 e1) s"
                "aval (subst x a1 e2) s = aval (subst x a2 e2) s"
    let ?e = "Plus e1 e2"
    show "?P ?e" using H id by simp
  qed
qed
    
(*
Take a copy of theory @{short_theory "AExp"} and modify it as follows.
Extend type @{typ aexp} with a binary constructor @{text Times} that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const asimp_const}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
*)

datatype myaexp = N int | V vname | Plus myaexp myaexp | Times myaexp myaexp

fun myaval :: "myaexp \<Rightarrow> state \<Rightarrow> val" where
  "myaval (N n) _ = n"
| "myaval (V x) s = s x"
| "myaval (Plus a1 a2) s = (+) (myaval a1 s) (myaval a2 s)"
| "myaval (Times a1 a2) s = (*) (myaval a1 s) (myaval a2 s)"

fun myplus :: "myaexp \<Rightarrow> myaexp \<Rightarrow> myaexp" where
  "myplus (N n1) (N n2) = N (n1 + n2)"
| "myplus (N n) a = (if n = 0 then a else (Plus (N n) a))"
| "myplus a (N n) = (if n = 0 then a else (Plus a (N n)))"
| "myplus a1 a2 = Plus a1 a2"

fun mytimes :: "myaexp \<Rightarrow> myaexp \<Rightarrow> myaexp" where
  "mytimes (N n1) (N n2) = N (n1 * n2)"
| "mytimes (N n) a = (if n = 0 then N 0 else if n = 1 then a else (Times (N n) a))"
| "mytimes a (N n) = (if n = 0 then N 0 else if n = 1 then a else (Times a (N n)))"
| "mytimes a1 a2 = Times a1 a2"

fun myasimp :: "myaexp \<Rightarrow> myaexp" where
  "myasimp (N x) = (N x)"
| "myasimp (V x) = (V x)"
| "myasimp (Plus a1 a2) = myplus (myasimp a1) (myasimp a2)"
| "myasimp (Times a1 a2) = mytimes (myasimp a1) (myasimp a2)"

(*
Define a datatype @{text aexp2} of extended arithmetic expressions that has,
in addition to the constructors of @{typ aexp}, a constructor for
modelling a C-like post-increment operation $x{++}$, where $x$ must be a
variable. Define an evaluation function @{text "aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state"}
that returns both the value of the expression and the new state.
The latter is required because post-increment changes the state.

Extend @{text aexp2} and @{text aval2} with a division operation. Model partiality of
division by changing the return type of @{text aval2} to
@{typ "(val \<times> state) option"}. In case of division by 0 let @{text aval2}
return @{const None}. Division on @{typ int} is the infix @{text div}.
*)

(*

The following type adds a @{text LET} construct to arithmetic expressions:
*)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

(* The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of @{text e\<^sub>2}
in the state where @{text x} is bound to the value of @{text e\<^sub>1} in the original state.
Define a function @{const lval} @{text"::"} @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{const inline} @{text"::"} @{typ "lexp \<Rightarrow> aexp"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of @{text e\<^sub>1} for @{text x} in the converted form of @{text e\<^sub>2}.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{const inline} is correct w.r.t.\ evaluation.
\endexercise


\exercise
Show that equality and less-or-equal tests on @{text aexp} are definable
*)

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le a1 a2 = Not (Less a2 a1)"

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a1 a2 = And (Le a1 a2) (Le a2 a1)" 

(*
and prove that they do what they are supposed to:
*)

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply(simp add : Le_def)
  apply(auto)
  done

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply(simp add : Eq_def Le_def)
  apply(auto)
  done

(*
Consider an alternative type of boolean expressions featuring a conditional: 
*)

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp
(*
text {*  First define an evaluation function analogously to @{const bval}: *}

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where


text{* Then define two translation functions *}

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
(* your definition/proof here *)

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
(* your definition/proof here *)

text{* and prove their correctness: *}

lemma "bval (if2bexp exp) s = ifval exp s"
(* your definition/proof here *)

lemma "ifval (b2ifexp exp) s = bval exp s"
(* your definition/proof here *)

text{*
\endexercise

\exercise
We define a new type of purely boolean expressions without any arithmetic
*}

datatype pbexp =
  VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

text{*
where variables range over values of type @{typ bool},
as can be seen from the evaluation function:
*}

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"  |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

text {* Define a function that checks whether a boolean exression is in NNF
(negation normal form), i.e., if @{const NOT} is only applied directly
to @{const VAR}s: *}

fun is_nnf :: "pbexp \<Rightarrow> bool" where
(* your definition/proof here *)

text{*
Now define a function that converts a @{text bexp} into NNF by pushing
@{const NOT} inwards as much as possible:
*}

fun nnf :: "pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text{*
Prove that @{const nnf} does what it is supposed to do:
*}

lemma pbval_nnf: "pbval (nnf b) s = pbval b s"
(* your definition/proof here *)

lemma is_nnf_nnf: "is_nnf (nnf b)"
(* your definition/proof here *)

text{*
An expression is in DNF (disjunctive normal form) if it is in NNF
and if no @{const OR} occurs below an @{const AND}. Define a corresponding
test:
*}

fun is_dnf :: "pbexp \<Rightarrow> bool" where
(* your definition/proof here *)

text {*
An NNF can be converted into a DNF in a bottom-up manner.
The critical case is the conversion of @{term (sub) "AND b1 b2"}.
Having converted @{text b\<^sub>1} and @{text b\<^sub>2}, apply distributivity of @{const AND}
over @{const OR}. If we write @{const OR} as a multi-argument function,
we can express the distributivity step as follows:
@{text "dist_AND (OR a\<^sub>1 ... a\<^sub>n) (OR b\<^sub>1 ... b\<^sub>m)"}
= @{text "OR (AND a\<^sub>1 b\<^sub>1) (AND a\<^sub>1 b\<^sub>2) ... (AND a\<^sub>n b\<^sub>m)"}. Define
*}

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text {* and prove that it behaves as follows: *}

lemma pbval_dist: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
(* your definition/proof here *)

lemma is_dnf_dist: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
(* your definition/proof here *)

text {* Use @{const dist_AND} to write a function that converts an NNF
  to a DNF in the above bottom-up manner.
*}

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
(* your definition/proof here *)

text {* Prove the correctness of your function: *}

lemma "pbval (dnf_of_nnf b) s = pbval b s"
(* your definition/proof here *)

lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
(* your definition/proof here *)
*)


(*
exe:stack-underflow
A \concept{stack underflow} occurs when executing an @{text ADD}
instruction on a stack of size less than 2. In our semantics
a term @{term "exec1 ADD s stk"} where @{prop "length stk < 2"}
is simply some unspecified value, not an error or exception --- HOL does not have those concepts.
Modify theory @{short_theory "ASM"}
such that stack underflow is modelled by @{const None}
and normal execution by @{text Some}, i.e., the execution functions
have return type @{typ "stack option"}. Modify all theorems and proofs
accordingly.
Hint: you may find @{text"split: option.split"} useful in your proofs.
*)




(*
\endexercise

\exercise\label{exe:register-machine}
This exercise is about a register machine
and compiler for @{typ aexp}. The machine instructions are
*)
type_synonym reg = nat
datatype instr = LDI val reg | LD vname reg | ADD reg reg

(*
where type @{text reg} is a synonym for @{typ nat}.
Instruction @{term "LDI i r"} loads @{text i} into register @{text r},
@{term "LD x r"} loads the value of @{text x} into register @{text r},
and @{term[names_short] "ADD r\<^sub>1 r\<^sub>2"} adds   register @{text r\<^sub>2} to register @{text r\<^sub>1}.

Define the execution of an instruction given a state and a register state;
the result is the new register state: *)

type_synonym rstate = "reg \<Rightarrow> val"

fun exec_mr_1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec_mr_1 (LDI i r) s rs = rs(r:=i)"
| "exec_mr_1 (LD v r) s rs = rs(r:=s v)"
| "exec_mr_1 (ADD r1 r2) s rs = rs(r1 := (+) (rs r1) (rs r2))"

(*
Define the execution @{const[source] exec} of a list of instructions as for the stack machine.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into @{text r}. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "< r"} should be left alone.
Define the compiler and prove it correct:
*)

fun comp_mr :: "aexp \<Rightarrow> reg \<Rightarrow> rstate \<Rightarrow> instr list" where
  "comp_mr (aexp.N n) r rs = [LDI n r]"
| "comp_mr (aexp.V x) r rs = [LD x r]"
| "comp_mr (aexp.Plus e1 e2) r rs = (comp_mr e1 r rs) @ (comp_mr e2 (r+1) rs) @ [ADD r (r + 1)]" 

fun exec_mr :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec_mr [] _ rs = rs"
| "exec_mr (i#is) s rs = exec_mr is s (exec_mr_1 i s rs)"

(*theorem "exec_mr (comp_mr a r) s rs r = aval a s"
  *)


(*
This exercise is a variation of the previous one
with a different instruction set:
*)

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

(*
All instructions refer implicitly to register 0 as a source or target:
@{const LDI0} and @{const LD0} load a value into register 0, @{term "MV0 r"}
copies the value in register 0 into register @{text r}, and @{term "ADD0 r"}
adds the value in register @{text r} to the value in register 0;
@{term "MV0 0"} and @{term "ADD0 0"} are legal. Define the execution functions
*)

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
(* your definition/proof here *)

text{*
and @{const exec0} for instruction lists.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into register 0. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "\<le> r"} should be left alone
(with the exception of 0). Define the compiler and prove it correct:
*}

theorem "exec0 (comp0 a r) s rs 0 = aval a s"
(* your definition/proof here *)

text{*
\endexercise
*}

end

