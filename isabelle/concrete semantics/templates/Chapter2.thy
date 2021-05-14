theory Chapter2
imports Main
begin

text{*
\section*{Chapter 2}

\exercise
Use the \textbf{value} command to evaluate the following expressions:
*}
value "bool"
value "True"
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"
value "[a,b] @ [c,d]"
value "(+) (1::nat) 1"
value "(=) 1 (1::nat)"

fun "conj" :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"

text{*
\endexercise
\exercise
Recall the definition of our own addition function on @{typ nat}:
*}

fun "add" :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

text{*
Prove that @{const add} is associative and commutative.
You will need additional lemmas.
*}

lemma add_assoc: "add (add m n) p = add m (add n p)"
  apply (induction m)
   apply (auto)
  done

lemma "add (add m n) p = add m (add n p)"
proof (induction m)
  case 0
  have "add (add 0 n) p = add n p" by simp
  also have "add n p = add 0 (add n p)" by simp
  finally show "add (add 0 n) p = add 0 (add n p)" by simp
next 
  case ind : (Suc m)
  have "add (add (Suc m) n) p = add (Suc (add m n)) p" by simp
  also have "add (Suc (add m n)) p = Suc (add (add m n) p)" by simp
  also have "Suc (add (add m n) p) = Suc (add m (add n p))" by (simp add : ind.IH)  
  also have "Suc (add m (add n p)) = add (Suc m) (add n p)" by simp
  finally show "add (add (Suc m) n) p = add (Suc m) (add n p)" by simp
qed
lemma add_comm_aux_1 [simp] : "add m 0 = m"
  apply (induction m)
  apply (auto)
  done

lemma add_comm_aux_2 [simp] : "add m (Suc n) = Suc (add m n)"
  apply (induction m)
   apply (auto)
  done

lemma add_comm: "add m n = add n m"
  apply (induction m)
   apply (auto)
done

lemma add_comm_isar : "add m n = add n m"
proof (induction m)
  case 0
  have "add 0 n = n" by simp
  also have "add n 0 = n" 
  proof (induction n)
    case 0 
    show "add 0 0 = 0" by simp
  next
    case ind: (Suc n)
    have "add (Suc n) 0 = Suc (add n 0)" by simp
    also have "Suc (add n 0) = Suc n" by (simp add : ind.IH)
    finally show "add (Suc n) 0 = Suc n" by simp
  qed
  then show "add 0 n = add n 0" by simp
next 
  case ind: (Suc m)
  have "add m n = add n m" by (simp add : ind.IH)
  also have "add (Suc m) n = Suc (add m n)" by simp
  have "add n (Suc m) = Suc (add n m)" by simp
  finally show "add (Suc m) n = add n (Suc m)" by (simp add : ind.IH)
qed


text{* Define a recursive function *}
fun "double" :: "nat \<Rightarrow> nat" where
  "double 0 = 0"|
  "double (Suc n) = Suc (Suc (double n))"

text{* and prove that *}

lemma double_add: "double m = add m m"
  apply (induction m)
   apply (auto)
  done

lemma double_add_isar : "double m = add m m"
proof (induction m)
  case 0
  show "double 0 = add 0 0" by simp
next
  case ind : (Suc m)
  have "double (Suc m) = Suc (Suc (double m))" by simp
  also have "Suc (Suc (double m)) = Suc (Suc (add m m))" by (simp add : ind.IH)
  also have "Suc (Suc (add m m)) = Suc (add (Suc m) m)" by simp
  also have "Suc (add (Suc m) m) = add (Suc m) (Suc m)" by simp
  finally show "double (Suc m) = add (Suc m) (Suc m)" by simp
qed



text{*
\endexercise


\exercise
Define a function that counts the number of occurrences of
an element in a list:
*}

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0"
| "count (x#xs) y = ((if x = y then 1 else 0) + count xs y)"

value "count [1,2,5,5] (5::nat)"

text {*
Test your definition of @{term count} on some examples.
Prove the following inequality:
*}

theorem "count xs x \<le> length xs"
  apply(induction xs)
   apply auto
  done
find_theorems count
thm count.simps
theorem "count xs y \<le> length xs"
proof (induction xs)
  case Nil
  have "count [] y = 0" by simp
  also have "0 \<le> length []" by simp
  finally show "count [] y \<le> length []" by auto
next
  case ind : (Cons x xs)
  have "count (x # xs) y \<le> 1 + count xs y" by simp
  also have "1 + count xs y \<le> 1 + length xs" using ind.IH by simp
  also have "1 + length xs = length (x # xs)" by simp
  finally show "count (x # xs) y \<le> length (x # xs)" by simp
qed

text{*
\endexercise
\exercise
Define a function @{text snoc} that appends an element to the end of a list.
Do not use the existing append operator @{text "@"} for lists.
*}

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]"
| "snoc (y#ys) x = y # (snoc ys x)"

value "snoc [1,2,3::nat] 4"

text {*
Convince yourself on some test cases that your definition
of @{term snoc} behaves as expected.
With the help of @{text snoc} define a recursive function @{text reverse}
that reverses a list. Do not use the predefined function @{const rev}.
*}

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x#xs) = snoc (reverse xs) x"

value "reverse [1,2,3::nat]"

text {*
Prove the following theorem. You will need an additional lemma.
*}

lemma rev_snoc : "reverse (snoc xs a) = a # (reverse xs)"  
  apply (induction xs)
   apply (auto)
  done

lemma rev_snoc_isar : "reverse (snoc xs a) = a # (reverse xs)"
proof (induction xs)
  case Nil
  have "reverse (snoc [] a) = [a]" by simp
  also have "a # (reverse []) = [a]" by simp
  finally show "reverse (snoc [] a) = a # (reverse [])" by simp
next
  case ind : (Cons x xs)
  show "reverse (snoc (x # xs) a) = a # reverse (x # xs)" by (simp add : ind.IH)
qed

theorem "reverse (reverse xs) = xs"
  apply (induction xs)
   apply (simp_all add : rev_snoc )
  done

theorem "reverse (reverse xs) = xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case ind : (Cons a xs)
  have "reverse (reverse (a # xs)) = reverse (snoc (reverse xs) a)" by simp
  also have "... = a # (reverse (reverse xs))" by (simp add : rev_snoc)
  also have "... = a # xs" by (simp add : ind.IH)
  finally show "reverse (reverse (a # xs)) = a # xs" by auto
qed

  
text{*
\endexercise


\exercise
The aim of this exercise is to prove the summation formula
\[ \sum_{i=0}^{n}i = \frac{n(n+1)}{2} \]
Define a recursive function @{text "sum_upto n = 0 + ... + n"}:
*}

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

value "sum_upto 3"

text {*
Now prove the summation formula by induction on @{text "n"}.
First, write a clear but informal proof by hand following the examples
in the main text. Then prove the same property in Isabelle:
*}

lemma "sum_upto n = n * (n+1) div 2"
  apply (induction n)
   apply (simp_all)
  done
lemma "sum_upto n = n * (n+1) div 2"
proof (induction n)
  case 0
  have "sum_upto (0::nat) = 0" by simp
  also have "(0::nat) * ((0 + 1) div 2) = 0" by simp
  finally show "sum_upto 0 = 0 * (0 + 1) div 2" by simp
next
  case ind : (Suc n)
  have "sum_upto (Suc n) = (Suc n) + sum_upto n" by simp
  also have "Suc n + sum_upto n = Suc n + (n * (n + 1) div 2)" by (simp add : ind.IH)
  finally show "sum_upto (Suc n) = Suc n * (Suc n + 1) div 2" by simp
qed


fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

value "itrev [1,2,3::nat] []"

lemma "itrev xs [] = rev xs"
  apply (induction xs)
  sorry

lemma "itrev xs [x] = (itrev xs []) @ [x]"
  apply (induction xs)
  apply (auto)
  sorry

lemma "itrev xs ys = (rev xs) @ ys"
proof (induction xs arbitrary : ys)
  case Nil
  show "itrev [] ys = rev [] @ ys" by simp
next  
  case ind : (Cons a xs)
  have "itrev (a # xs) ys = itrev xs (a # ys)" by simp
  also have "itrev xs (a # ys) = (rev xs) @ (a # ys)" by (auto simp add : ind.IH)
  also have "(rev xs) @ (a # ys) = rev (a # xs) @ ys" by simp
  finally show "itrev (a # xs) ys = rev (a # xs) @ ys" by simp
qed


lemma "itrev xs ys = (rev xs) @ ys"
  apply (induction xs arbitrary : ys)
   apply (auto)
  done

  


text{*
\endexercise


\exercise
Starting from the type @{text "'a tree"} defined in the text, define
a function that collects all values in a tree in a list, in any order,
without removing duplicates.
*}
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []"
| "contents (Node T1 x T2) = x # (contents T1) @ (contents T2)"

value "contents t1"

text{*
Then define a function that sums up all values in a tree of natural numbers
*}

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node T1 x T2) = x + (sum_tree T1) + (sum_tree T2)"

fun sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list [] = 0"
| "sum_list (x#xs) = x + sum_list xs"

value "sum_tree t1"
value "sum_list [1,2,3]"

text{* and prove *}

lemma sum_list_aux : "sum_list (l1 @ l2) = sum_list l1 + sum_list l2"
  apply (induction l1)
   apply (auto)
  done

lemma "sum_tree t = sum_list (contents t)"
  apply (induction t rule : sum_tree.induct)
   apply (auto simp add : sum_list_aux)
  done

lemma "sum_tree t = sum_list (contents t)"
proof (induction t)
  case Tip
  have "sum_tree Tip = 0" by simp
  also have "Chapter2.sum_list (contents Tip) = 0" by simp
  finally show ?case by simp
next
  case ind : (Node T1 x T2)
  have "sum_tree (Node T1 x T2) = x + (sum_tree T1) + (sum_tree T2)" by simp
  also have "... = x + (Chapter2.sum_list (contents T1)) + (Chapter2.sum_list (contents T2))" 
    by (simp add : ind.IH)
  also have "... = Chapter2.sum_list (contents (Node T1 x T2))" by (simp add : sum_list_aux)
  finally show "sum_tree (Node T1 x T2) = Chapter2.sum_list (contents (Node T1 x T2))" by simp
qed
 
text{*
\endexercise

\exercise
Define a new type @{text "'a tree2"} of binary trees where values are also
stored in the leaves of the tree.  Also reformulate the
@{text mirror} function accordingly. Define two functions *}

datatype 'a tree2 = Tip2 'a | Node2 "'a tree2" 'a "'a tree2"

fun "mirror2" :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror2 (Tip2 x) = Tip2 x"
| "mirror2 (Node2 (t1 :: 'a tree2) x t2) = Node2 (mirror2 t2) x (mirror2 t1)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip2 x) = [x]"
| "pre_order (Node2 t1 x t2) = (pre_order t1) @ [x] @ (pre_order t2)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip2 x) = [x]"
| "post_order (Node2 t1 x t2) = (post_order t2) @ [x] @ (post_order t1)"

text{*
that traverse a tree and collect all stored values in the respective order in
a list. Prove *}

lemma "pre_order (mirror2 t) = post_order t"
  apply (induction t)
   apply (auto)
  done

lemma "pre_order (mirror2 t) = post_order t"
proof (induction t)
  case Tip2
  show ?case by simp
next
  case ind : (Node2 t1 x t2)
  show ?case by (auto simp add : ind.IH)
qed

text{*
\endexercise

\exercise
Define a recursive function
*}

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse _ [] = []"
| "intersperse a (x # xs) = [x,a] @ (intersperse a xs)"

text{*
such that @{text "intersperse a [x\<^sub>1, ..., x\<^sub>n] = [x\<^sub>1, a, x\<^sub>2, a, ..., a, x\<^sub>n]"}.
Prove
*}

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
   apply (auto)
  done

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
proof (induction xs)
  case Nil
  show ?case by simp 
next
  case ind : (Cons a xs)
  show ?case by (auto simp add : ind.IH)
qed

text{*
\endexercise


\exercise
Write a tail-recursive variant of the @{text add} function on @{typ nat}:
*}

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

text{*
Tail-recursive means that in the recursive case, @{const itadd} needs to call
itself directly: \mbox{@{term"itadd (Suc m) n"}} @{text"= itadd \<dots>"}.
Prove
*}

lemma "itadd m n = add m n"
  by (induction m arbitrary : n) auto

lemma "itadd m n = add m n"
proof (induction m arbitrary : n)
  case 0
  show ?case by simp
next
  case ind : (Suc m)
  have "itadd (Suc m) n = itadd m (Suc n)" by simp
  also have "... = add m (Suc n)" by (simp add : ind.IH)
  also have "add m (Suc n) = add (Suc m) n" by simp
  finally show "itadd (Suc m) n = add (Suc m) n" by simp
qed

text{*
\endexercise


\exercise\label{exe:tree0}
Define a datatype @{text tree0} of binary tree skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function that counts the number of all nodes (inner nodes and leaves)
in such a tree:
*}

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1"
| "nodes (Node t1 t2) = 1 + nodes t1 + nodes t2"

text {*
Consider the following recursive function:
*}

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

text {*
Experiment how @{text explode} influences the size of a binary tree
and find an equation expressing the size of a tree after exploding it
(\noquotes{@{term [source] "nodes (explode n t)"}}) as a function
of @{term "nodes t"} and @{text n}. Prove your equation.
You may use the usual arithmetic operations including the exponentiation
operator ``@{text"^"}''. For example, \noquotes{@{prop [source] "2 ^ 2 = 4"}}.

Hint: simplifying with the list of theorems @{thm[source] algebra_simps}
takes care of common algebraic properties of the arithmetic operators.
\endexercise
*}

lemma "nodes (explode n t) = 2^n * (nodes t) + 2^n - 1"
  apply (induction n arbitrary : t)
   apply (auto simp add : algebra_simps)
  done

lemma "nodes (explode n t) = 2^n * (nodes t) + 2^n - 1"
proof (induction n arbitrary : t)
  case 0
  show ?case by simp
next
  case ind : (Suc n)
  show ?case by (simp add : algebra_simps ind.IH)
qed
  
text{*

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
*}

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text{*
Define a function @{text eval} that evaluates an expression at some value:
*}

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var a = a"
| "eval (Const k) _ = k"
| "eval (Add e1 e2) a = (eval e1) a + (eval e2) a"
| "eval (Mult e1 e2) a = (eval e1) a * (eval e2) a"

value "eval (Add (Mult (Const 2) Var) (Const 3)) 5 = 2*i+3"

text{*
For example, @{prop"eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"}.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function @{text evalp} that evaluates a polynomial at a given value:
*}

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] _ = 0"
| "evalp (c#cs) k = c + k * (evalp cs k)"

value "evalp [4,2,-1,3] 1"

text{*
Define a function @{text coeffs} that transforms an expression into a polynomial.
This will require auxiliary functions.
*}

fun add_intlist_intlist :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "add_intlist_intlist [] ys = ys"
| "add_intlist_intlist xs [] = xs"
| "add_intlist_intlist (x#xs) (y#ys) = (x+y)#(add_intlist_intlist xs ys)"

fun mult_int_intlist :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "mult_int_intlist _ [] = []"
| "mult_int_intlist x (y#ys) = (x*y) # (mult_int_intlist x ys)"

fun mult_intlist_intlist :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mult_intlist_intlist [] ys = ys"
| "mult_intlist_intlist (x#xs) ys =
   add_intlist_intlist (mult_int_intlist x ys) (0#(mult_intlist_intlist xs ys))" 

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0,1]"
| "coeffs (Const c) = [c]"
| "coeffs (Add e1 e2) = add_intlist_intlist (coeffs e1) (coeffs e2)"
| "coeffs (Mult e1 e2) = mult_intlist_intlist (coeffs e1) (coeffs e2)"

text{*
Prove that @{text coeffs} preserves the value of the expression:
*}

lemma "evalp (add_intlist_intlist xs ys) x = evalp xs x + evalp ys x"
  apply (induction xs arbitrary:x)
   apply (simp_all)
  apply (induction ys)
  apply (simp_all)

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
  apply (induction e arbitrary:x)
  apply (simp_all)

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
proof (induction e arbitrary:x)
  case Var
  show ?case by simp
next
  case (Const x)
  show ?case by simp
next
  case ind_add : (Add e1 e2)
  have "evalp (coeffs (Add e1 e2)) x = evalp (add_intlist_intlist (coeffs e1) (coeffs e2)) x" by simp
  


text{*
Hint: consider the hint in Exercise~\ref{exe:tree0}.
\endexercise
*}

end

