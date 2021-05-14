theory Chapter5
imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_0: "iter r 0 x x" |
iter_Suc: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"




(*
\section*{Chapter 5}
*)

(*section 5.4.1 *)
lemma "length (tl xs) = length xs - 1"
proof (rule list.induct)
  have H1 : "length (tl []) = 0" by simp
  have H2 : "length [] = 0 - 1" by simp
  from H1 H2 show "length (tl []) = length [] - 1" by simp
next
  fix x1 x2
  assume "length (tl x2) = length x2 - 1"
  show "length (tl (x1 # x2)) = length (x1 # x2) - 1" by simp
qed

lemma "length (tl xs) = length xs - 1"
proof (induction xs)
  have H1 : "length (tl []) = 0" by simp
  have H2 : "length [] = 0 - 1" by simp
  from H1 H2 show "length (tl []) = length [] - 1" by simp
next
  fix x1 x2
  assume "length (tl x2) = length x2 - 1"
  show "length (tl (x1 # x2)) = length (x1 # x2) - 1" by simp
qed 

lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []"
  then have H1 : "length (tl xs) = 0" by simp
  from \<open>xs = []\<close> have H2 : "length xs = 0 - 1" by simp
  from H1 H2 show "length (tl xs) = length xs - 1" by simp
next
  fix y ys
  assume "xs = y#ys"
  then show "length (tl xs) = length xs - 1"
  proof-
    from \<open>xs = y#ys\<close> have "tl xs = ys" by simp
    from \<open>tl xs = ys\<close> show "length (tl xs) = length xs - 1" by auto
  qed
qed


(*
\exercise
Give a readable, structured proof of the following lemma:
*)

lemma "\<not> surj (f::'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma "\<not> surj (f::'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  from this show "False" by blast
qed

lemma "\<not> surj (f::'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp:surj_def)
  thus "False" by blast
qed

lemma 
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof- 
  have "\<exists>a. {x. x \<notin> f x} = f a" using s
    by(auto simp : surj_def)
  thus "False" by blast
qed

lemma 
  fixes a b :: int
  assumes "b dvd (a + b)" 
  shows "b dvd a"
proof-
  { fix k
    assume k: "a + b = b * k"
    have "\<exists>k'. a = b * k'"
    proof
      show "a = b * (k - 1)" using k by (simp add:algebra_simps)
    qed}
  then show ?thesis using assms by(auto simp add:dvd_def)
qed


(* exo  5.1 *)
lemma 
  assumes T : "\<forall> x y. T x y \<or> T y x"  (* T totale*)
  and A : "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"    (* A anti-symetrique*)
  and TA : "\<forall>x y. T x y \<longrightarrow> A x y"       (* T \<subseteq> A *)
  and Axy "A x y"                           
  shows "T x y"
proof(rule ccontr)
  assume 0 : "\<not> T x y"
  from 0 T have 1 : "T y x" by (auto)
  from 1 TA have 2 : "A y x" by (auto)
  from `A x y` A 2 have 3 : "x = y" by(auto)
  from 3 1 have 4 : "T x y" by (auto)
  from 0 4 show "False" by (auto)
qed


(*
Each step should use at most one of the assumptions @{text T}, @{text A}
or @{text TA}.
\endexercise

\exercise
Give a readable, structured proof of the following lemma:
*)
(*lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs)
      \<or> (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
*)

lemma "length (tl xs) = length xs - 1"
proof(cases xs)
  assume "xs = []"
  thus ?thesis by (simp)
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by (simp)
qed

lemma "length (tl xs) = length xs -1"
proof(cases xs)
  case (Nil)
  thus ?thesis by simp
next 
  case (Cons y ys)
  thus ?thesis by simp
qed

lemma "\<Sum>{ 0 .. (n::nat)} = n * (n + 1) div 2"
proof (induction n)
  case (0)
  show "\<Sum>{ 0 .. (0::nat)} = 0 * (0 + 1) div 2" by simp
next
  fix n 
  assume IH : " \<Sum> {0..n::nat} = n * (n + 1) div 2"
  from IH show " \<Sum> {0..(Suc n)} = (Suc n) * ((Suc n) + 1) div 2" by simp
qed

lemma "\<Sum>{ 0 .. (n::nat)} = n * (n + 1) div 2" (is "?P n")
proof(induction n)
  case 0
  show "?P 0" by simp
next 
  fix n
  assume IH : "?P n"
  thus "?P (Suc n)" by simp
  (* from IH show "?P (Suc n)" by simp *)
qed

lemma "\<Sum>{ 0 .. (n::nat)} = n * (n + 1) div 2"
proof(induction n)
  case 0
  show ?case by simp
next 
  case (Suc n)
  thus ?case by simp
  (* from IH show "?P (Suc n)" by simp *)
qed


inductive ev :: "nat \<Rightarrow> bool" where
ev0 : "ev 0"|
evSS : "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule:ev.induct)
  case ev0
  show ?case by simp
(*  show "evn 0" by simp*)
next  
  case (evSS n)
  thus ?case by simp
(*  thus "evn (Suc (Suc n))" by simp*)
qed

lemma "\<not> ev (Suc 0)"
proof
  assume "ev (Suc 0)" 
  then show False 
  proof cases
    case ev0 
  next
    case evSS
qed

(* rule inversion *)
lemma "\<not> ev (Suc 0)"
proof
  assume "ev (Suc 0)" 
  then show False by cases
qed

lemma "ev n \<Longrightarrow> ev (n-2)"
proof-
  assume "ev n"
  from this show "ev (n-2)"
  proof cases
    assume "n = 0"
    have "ev 0" ..
    from \<open>n = 0 \<close> \<open>ev 0\<close> show " ev (n - 2)" by simp
  next
    fix m
    assume "n = Suc (Suc m)" 
    and "ev m"
    from `n = Suc (Suc m)` have "n - 2 = m" by simp
    with `ev m` show "ev (n - 2)" by simp
  qed
qed

  

lemma "ev n \<Longrightarrow> ev (n - 2)"
proof-
  {assume "ev n"
  from this have "ev (n - 2)"
  proof cases
    case ev0 thus "ev (n - 2)" by (simp add: ev.ev0)
  next 
    case (evSS k) thus "ev (n - 2)" by (simp add: ev.evSS)
  qed}  note 1 = this
  assume 0: "ev n"
  from 0 1 show ?thesis by (simp)
qed

lemma 
  "\<not>ev (Suc (Suc (Suc 0)))"
proof (rule notI)
  assume H1 : "ev (Suc (Suc (Suc 0)))"
  then show "False"
  proof cases
    case ev0 
    show "ev (Suc 0) \<Longrightarrow> False"
    proof-
      assume "ev (Suc 0)"
      then show "False" by cases
    qed
  qed
qed
      

(* Exercices 5.3*)
lemma
  assumes a : "ev (Suc (Suc n))" 
  shows "ev n"
proof cases
  case ev0

(*
Hint: There are predefined functions @{const take} and {const drop} of type
@{typ "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"} such that @{text"take k [x\<^sub>1,\<dots>] = [x\<^sub>1,\<dots>,x\<^sub>k]"}
and @{text"drop k [x\<^sub>1,\<dots>] = [x\<^bsub>k+1\<^esub>,\<dots>]"}. Let sledgehammer find and apply
the relevant @{const take} and @{const drop} lemmas for you.
\endexercise

\exercise
Give a structured proof by rule inversion:
*)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"
lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
(* your definition/proof here *)

text{*
\exercise
Give a structured proof by rule inversions:
*}

lemma "\<not> ev(Suc(Suc(Suc 0)))"
(* your definition/proof here *)

text{*
If there are no cases to be proved you can close
a proof immediateley with \isacom{qed}.
\endexercise

\exercise
Recall predicate @{const star} from Section 4.5 and @{const iter}
from Exercise~\ref{exe:iter}.
*}

lemma "iter r n x y \<Longrightarrow> star r x y"
(* your definition/proof here *)

text{*
Prove this lemma in a structured style, do not just sledgehammer each case of the
required induction.
\endexercise

\exercise
Define a recursive function
*}

fun elems :: "'a list \<Rightarrow> 'a set" where
(* your definition/proof here *)

text{* that collects all elements of a list into a set. Prove *}

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Extend Exercise~\ref{exe:cfg} with a function that checks if some
\mbox{@{text "alpha list"}} is a balanced
string of parentheses. More precisely, define a recursive function *}
(* your definition/proof here *)
fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
(* your definition/proof here *)

text{* such that @{term"balanced n w"}
is true iff (informally) @{text"a\<^sup>n @ w \<in> S"}. Formally, prove *}

corollary "balanced n w \<longleftrightarrow> S (replicate n a @ w)"


text{* where @{const replicate} @{text"::"} @{typ"nat \<Rightarrow> 'a \<Rightarrow> 'a list"} is predefined
and @{term"replicate n x"} yields the list @{text"[x, \<dots>, x]"} of length @{text n}.
*}

end

