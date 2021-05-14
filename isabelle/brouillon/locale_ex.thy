theory Calculus
  imports Main
begin

(* locale  exos*)
locale partial_order = 
  fixes 
    le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) 
  assumes
    refl [intro, simp] : "\<And>x. x \<sqsubseteq> x" and 
    anti_sym [intro] : "\<And>x y. \<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y" and
    trans [trans] : "\<And>x y z. \<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

  (*print_locales: lists the names of all locales of the currnet theory *)
print_locales
  (*print_locale n : prints the parameters and assumptions of locale n *)
print_locale partial_order
  (*print_locale! n : additionally outputs the conclusions that are stored in the locale *)
print_locale! partial_order
  (* partial_order_def : predicate introduicd by the locale declaration *)
thm partial_order_def
  (* each conclusion has a foundational theorem as counterpart in the theory*)
thm partial_order.trans
  (**)

definition (in partial_order) less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50) where
  "(x \<sqsubset> y) = (x \<sqsubseteq> y \<and> x \<noteq> y)"

print_locale partial_order
print_locale! partial_order
thm partial_order_def
thm partial_order.less_def

lemma (in partial_order) less_le_trans [trans]: "\<lbrakk> x \<sqsubset> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  unfolding less_def by (blast intro : trans)

context partial_order
begin
  
definition is_inf where
  "is_inf x y i = ( i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i ))"
  
definition is_sup where
  "is_sup x y s = (   x \<sqsubseteq> s \<and> y \<sqsubseteq> s \<and> (\<forall>z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> s \<sqsubseteq> z ))"

theorem is_inf_uniq : " \<lbrakk> is_inf x y a; is_inf x y b \<rbrakk> \<Longrightarrow> a = b "
proof-
  assume "is_inf x y a" "is_inf x y b"
  show "a = b"
  proof-
    from `is_inf x y a` have H1 : "a \<sqsubseteq> x \<and> a \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> a)"
      by (simp add : is_inf_def)
    from `is_inf x y b` have H2 : "b \<sqsubseteq> x \<and> b \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> b)"
      by (simp add : is_inf_def)
    from H1 H2 have "b \<sqsubseteq> a" by simp
    from H1 H2 have "a \<sqsubseteq> b" by simp
    from `a \<sqsubseteq> b` `b \<sqsubseteq> a` show "a = b" by (rule anti_sym)
  qed
qed

theorem is_sup_uniq : " \<lbrakk> is_sup x y a; is_sup x y b \<rbrakk> \<Longrightarrow> a = b "
  by (simp add : is_sup_def anti_sym)
end

(* Section 3 *)

locale lattice = partial_order +
  assumes 
    ex_inf : "\<exists>inf. is_inf x y inf" and
    ex_sup : "\<exists>sup. is_sup x y sup"
begin
  definition meet (infixl "\<sqinter>" 70) where "x \<sqinter> y = (THE z. is_inf x y z)"
definition join (infixl "\<squnion>" 70) where "x \<squnion> y = (THE z. is_sup x y z)"


(**************************************
***************************************
  ***************************************)
  
lemma meet_left_1 : "x \<sqinter> y \<sqsubseteq> x"
  (* sledgehammer *)
  by (metis ex_inf is_inf_uniq meet_def partial_order.is_inf_def partial_order_axioms the_equality)

find_theorems name: the_equality

lemma meet_left_2: "x \<sqinter> y \<sqsubseteq> x "
  unfolding meet_def is_inf_def
proof -
  fix x y
  obtain i where ix: "i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i)"
    using ex_inf unfolding is_inf_def by blast
  then have "\<And>z. ((z \<sqsubseteq> x) \<and> (z \<sqsubseteq> y) \<and> (\<forall>w. (w \<sqsubseteq> x) \<and> (w \<sqsubseteq> y) \<longrightarrow> w \<sqsubseteq> z)) \<Longrightarrow> z = i"
    using is_inf_uniq unfolding is_inf_def by blast 
  then have "i = (THE i. i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i))"
    using the_equality[of _ i] is_inf_uniq ix unfolding is_inf_def by (smt (verit,best)) 
  then show \<open>(THE i. i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i)) \<sqsubseteq> x\<close>
    using ix by blast 
qed



(**************************************
***************************************
***************************************)

end

locale total_order = partial_order + 
  assumes total : "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

lemma (in total_order) less_total : "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
proof(rule ccontr)
  assume H0 : "\<not>(x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x)"
  from H0 have H1 : "\<not>(x \<sqsubset> y) \<and> x \<noteq> y \<and> \<not>(y \<sqsubset> x)" by blast
  from H1 have "x \<noteq> y" by simp
  from H1 have H2 : "\<not>(x \<sqsubset> y) \<and> \<not>(y \<sqsubset> x)" by simp
  from H2 have H3 : "\<not>(x \<sqsubseteq> y \<and> x \<noteq> y) \<and> \<not>(y \<sqsubseteq> x \<and> y \<noteq> x)" by (simp add : less_def)
  from H3 have H4 : "(\<not>(x \<sqsubseteq> y) \<and> \<not>(y \<sqsubseteq> x)) \<or> \<not>(x \<noteq> y)" by blast
  from H4 show False 
  proof (rule disjE)
    assume "\<not> x \<noteq> y"
    from `\<not>(x\<noteq>y)` have "x = y" by simp
    from `x \<noteq> y` `x = y` show False by (rule notE)
  next
    assume H : "\<not> x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x" 
    from total have H' : "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by simp
    from H H' show False by blast
  qed
qed

lemma "x \<or> \<not>x"
proof (rule ccontr)
  assume "\<not>(x \<or> \<not>x)"
  then have "\<not>x \<and> x" by simp
  then have "x" by (rule conjE)
  then have "x \<or> \<not>x" by (rule disjI1)
  from `\<not>(x \<or> \<not>x)` this show False by (rule notE)
qed

lemma "x \<or> \<not>x"
proof-
  have "\<not>(x \<or> \<not>x) \<Longrightarrow> False"
  proof-
    assume "\<not>(x \<or> \<not>x)"
    then have "\<not>x \<and> x" by simp
    then have "x" by (rule conjE)
    then have "x \<or> \<not>x" by (rule disjI1)
    from `\<not>(x \<or> \<not>x)` this show False by (rule notE)
  qed
  from this show "x \<or> \<not>x" by (rule ccontr)
qed

lemma (in total_order) "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
proof-
  have "\<not>(x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x) \<Longrightarrow> False" 
  proof-
    assume H0 : "\<not>(x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x)"
    from H0 have H1 : "\<not>(x \<sqsubset> y) \<and> x \<noteq> y \<and> \<not>(y \<sqsubset> x)" by blast
    from H1 have "x \<noteq> y" by simp
    from H1 have H2 : "\<not>(x \<sqsubset> y) \<and> \<not>(y \<sqsubset> x)" by simp
    from H2 have H3 : "\<not>(x \<sqsubseteq> y \<and> x \<noteq> y) \<and> \<not>(y \<sqsubseteq> x \<and> y \<noteq> x)" by (simp add : less_def)
    from H3 have H4 : "(\<not>(x \<sqsubseteq> y) \<and> \<not>(y \<sqsubseteq> x)) \<or> \<not>(x \<noteq> y)" by blast
    from H4 show False 
    proof (rule disjE)
      assume "\<not> x \<noteq> y"
      from `\<not>(x\<noteq>y)` have "x = y" by simp
      from `x \<noteq> y` `x = y` show False by (rule notE)
    next
      assume H : "\<not> x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x" 
      from total have H' : "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by simp
      from H H' show False by blast
    qed
  qed
  from `\<not> (x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x) \<Longrightarrow> False`
  show "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x" by (rule ccontr)
qed

locale distrib_lattice = lattice + 
  assumes
    meet_distr : "x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"

  
lemma (in distrib_lattice) join_distr:
  "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  sorry

sublocale total_order \<subseteq> lattice
proof unfold_locales
  fix x y
  from total have "is_inf x y (if x \<sqsubseteq> y then x else y)" by (auto simp add : is_inf_def)
  then show "\<exists>inf. is_inf x y inf" by (rule exI)
next
  fix x y 
  from total have "is_sup x y (if x \<sqsubseteq> y then y else x)" by (auto simp add : is_sup_def)
  then show "\<exists>sup. is_sup x y sup" by (rule exI)
qed

sublocale total_order \<subseteq> distrib_lattice
  sorry

lemma "\<And>x::nat. x \<le> x"
  by (metis Orderings.order_class.order.refl)

lemma "\<And>x::nat. x \<le> x"
  apply (auto simp add : Orderings.order_class.order.refl)
  sorry

lemma "(x::nat) \<le> x"
proof-
  from le_refl[of x] show "x \<le> x" by simp
qed

(* question pourquoi cette preuve ne marche pas*)
lemma "\<And>x::nat. x \<le> x"
proof-
  fix x
  from le_refl[of x] have "x \<le> x" by auto
(*
Failed to apply initial proof method\<^here>:
using this:
  x \<le> x
goal (1 subgoal):
 1. x \<le> x
*)
  then show ?thesis by auto
  oops

  print_locale partial_order


(* section 5.1 *)
interpretation int : partial_order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
  by unfold_locales auto

(* section 5.2 *)
interpretation int : partial_order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
  rewrites "int.less x y = (x < y)"
proof -
  show "partial_order ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
    by unfold_locales auto
  show "partial_order.less ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool) x y = (x < y)"
    unfolding partial_order.less_def [OF \<open>partial_order (\<le>)\<close>]
    by auto
qed

(* section 5.3 *)
interpretation int : partial_order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
  rewrites "int.less x y = (x < y)"
proof -
  show "partial_order ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
    by unfold_locales auto
  then interpret int : partial_order "(\<le>) :: [int, int] \<Rightarrow> bool" by assumption
  show "int.less x y = (x < y)"
    unfolding int.less_def
    by auto
qed

(* section 5.4 *)
interpretation int : lattice "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
  rewrites int_min_eq : "int.meet x y = min x y"
  and int_max_eq : "int.join x y = max x y"
proof - 
  show "lattice ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
    apply unfold_locales
     apply (unfold int.is_inf_def int.is_sup_def)
    by arith+
  then interpret int : lattice "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool" by assumption
  show "int.meet x y =  min x y"
    by (bestsimp simp : int.meet_def int.is_inf_def)
  show "int.join x y =  max x y"
    by (bestsimp simp : int.join_def int.is_sup_def)
qed


locale order_preserving = 
  po_le : partial_order le  + po_le' : partial_order le'
  for le (infixl "\<sqsubseteq>" 50) and le' (infixl "\<lesssim>" 50) +
  fixes \<phi>
  assumes hom_le : "x \<sqsubseteq> y \<Longrightarrow> \<phi> x \<lesssim> \<phi> y"



print_locale order_preserving
print_locale! order_preserving

notation (in order_preserving) po_le'.less (infixl "<" 50)
print_locale! order_preserving


(* section 6.1  default instantiations *)

(* section 6.2 implicit  parameters *)
(* in a locale declarationm the expression partial_order is short for
    partial_order le for le (infixl "\<sqsubseteq>" 50)   *)

locale lattice_hom = 
  le : lattice + le' : lattice le' for le' (infixl "\<lesssim>" 50) +
fixes \<phi>
assumes 
  hom_meet : "\<phi> (x \<sqinter> y) = le'.meet (\<phi> x) (\<phi> y)"
  and
  hom_join : "\<phi> (x \<squnion> y) = le'.join (\<phi> x) (\<phi> y)"

context lattice_hom
begin
  notation le'.meet (infixl "\<sqinter>''" 50)
  notation le'.join (infixl "\<squnion>''" 50)
end

locale lattice_hom_2 = 
  le : lattice le + le' : lattice le' 
  for le (infixl "\<sqsubseteq>" 50) and le' (infixl "\<lesssim>" 50) +
fixes \<phi>
assumes 
  hom_meet : "\<phi> (x \<sqinter> y) = le'.meet (\<phi> x) (\<phi> y)"
  and
  hom_join : "\<phi> (x \<squnion> y) = le'.join (\<phi> x) (\<phi> y)"

(* section 7 Conditional interpretation*)

locale non_negative =
  fixes n :: int
  assumes non_neg : "0 \<le> n"

sublocale non_negative \<subseteq> order_preserving "(\<le>)" "(\<le>)" "\<lambda>i. n * i"


end