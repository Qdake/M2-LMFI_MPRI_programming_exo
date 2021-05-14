theory structured_proofs_in_Isar_HOL
imports Main "Saturation_Framework.Calculus"
begin
(* notes*)

(* deux ! pour entrer \<And> *)

(* section 2: Logic *)
(* section 2.1 : Propositional logic *)

(* introduction rules*)
lemma "A \<longrightarrow> A"
proof (rule impI)
  assume a: "A" 
  show "A" by (rule a) (* ! ? what is (rule a ) *)
qed
(* Command "proof" automatically tries to select an introduction rule based on the goal 
    and a predefined list of rules *)

(* in the following proof, "impI" is automatically applied *)
lemma "A \<longrightarrow> A"
proof
  assume a: A
  show A by (rule a)
qed

(*  Trivial proofs, in particular those by assumption, should be trivial to perform. 
    Proof "." does just that (and a bit more). Thus naming of assumptions is often superfluous.*)

lemma "A \<longrightarrow> A"
proof 
  assume a : "A"
  from \<open> A \<close> show "A" .
qed

(* To hide proofs by assumption further, "by (method)" first applies method and then tries
  to solve all remaining subgoals by assumption:*)

lemma "A \<longrightarrow> A \<and> A"
proof (rule impI)
  assume "A"
  from \<open>A\<close> \<open>A\<close> show "A \<and> A" by (rule conjI)
qed
  

(* Elimination rules *)
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB : "A \<and> B"
  show "B \<and> A"
  proof (rule conjE[OF AB])
    assume "A" "B"
    from \<open>B\<close> \<open>A\<close> show ?thesis by (rule conjI)
  qed
qed

(*
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from AB show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed
*)

(* 
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  from this show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed 
*)


(* 
?thesis always stands for the "current goal" 
*)

(* an alternative proff that operates purely by forward reasoning:*)
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume ab : "A \<and> B"
  from ab have a: "A" ..
  from ab have b: "B" ..
  from b a show "B \<and> A" ..
qed

(* with details*)
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof (rule impI)
  assume ab : "A \<and> B"
  from ab have a: "A" by (rule conjE)
  from ab have b: "B" by (rule conjE)
  from b a show "B \<and> A" by (rule conjI)
qed

lemma "\<not>(A \<or> B) \<longrightarrow> \<not>A \<or> \<not>B"
proof (rule impI)
  assume "\<not>(A \<or> B)"
  have "\<not>A"
  proof (rule notI)
    assume A 
    from this have "A \<or> B" by (rule disjI1)
    from \<open>\<not>(A \<or> B)\<close> \<open>A \<or> B\<close> show False by (rule notE)
  qed
  from \<open>\<not>A\<close> show "\<not>A \<or> \<not>B" by (rule disjI1)
qed


lemma "\<not>(A \<and> B) \<longrightarrow> \<not>A \<or> \<not>B"
proof
  (* \<turnstile> A \<or> \<not>A *)
  have "A \<or> \<not>A"
  proof (rule ccontr)
    assume "\<not>(A \<or> \<not>A)"
    have "\<not>A"    (*   ! ! on ne peut pas utiliser from this have "\<not>A" car proof (rule notI)  *)
    proof (rule notI)
      assume "A"
      from this have "A \<or> \<not>A" by (rule disjI1)
      from \<open>\<not>(A \<or> \<not>A)\<close> \<open>A \<or> \<not>A\<close> show False by (rule notE)
    qed
    from \<open>\<not>A\<close> have "A \<or> \<not>A" by (rule disjI2)
    from \<open>\<not>(A \<or> \<not>A)\<close> \<open>A \<or> \<not>A\<close> show False by (rule notE)
  qed

  (* \<turnstile> A \<or> \<not>A   \<not>(A \<and> B), A \<turnstile> \<not>A \<or> \<not>B    \<not>(A \<and> B), B \<turnstile> \<not>A \<or> \<not>B
    -----------------------------------------
         \<not>(A \<and> B) \<turnstile> \<not>A \<or> \<not>B  *)
  assume "\<not>(A \<and> B)"
  from \<open>A \<or> \<not>A\<close> show "\<not>A \<or> \<not>B" 
  proof (rule disjE)
    assume "A"
    have "\<not>B"
    proof (rule notI)
      assume "B"
      from \<open>A\<close> \<open>B\<close> have "A \<and> B" by (rule conjI)
      from \<open>\<not>(A \<and> B)\<close> \<open>A \<and> B\<close> show False by (rule notE)
    qed
    from \<open>\<not>B\<close> show ?thesis by (rule disjI2)
  next
    assume "\<not>A"
    from this show ?thesis by (rule disjI1)
  qed
qed


lemma "\<not>(A \<and> B) \<longrightarrow> \<not>A \<or> \<not>B"
proof (rule impI)
  assume H1 : "\<not>(A \<and> B)"
  show "\<not>A \<or> \<not>B"
  proof (rule ccontr)
    assume H2 : "\<not>(\<not>A \<or> \<not>B)"
    have "\<not>A"
    proof (rule notI)
      assume "A"
      have "\<not>B"
      proof (rule notI)
        assume "B"
        from \<open>A\<close> \<open>B\<close> have not_H1 : "A \<and> B" by (rule conjI)
        from H1 not_H1 show False by (rule notE)
      qed
      from \<open>\<not>B\<close> have not_H2 : "\<not>A \<or> \<not>B" by (rule disjI2)
      from H2 not_H2 show False by (rule notE)
    qed
    from \<open>\<not>A\<close> have not_H2_2 : "\<not>A \<or> \<not>B" by (rule disjI1)
    from H2 not_H2_2 show False by (rule notE)
  qed
qed

lemma "\<not>(A \<and> B) \<longrightarrow> \<not>A \<or> \<not>B"
proof (rule impI)
  assume H1 : "\<not>(A \<and> B)"
  show "\<not>A \<or> \<not>B"
  proof (rule ccontr)
    assume H2 : "\<not>(\<not>A \<or> \<not>B)"
    have "\<not>A"
    proof (rule notI)
      assume "A"
      have "\<not>B"
      proof (rule notI)
        assume "B"
        with \<open>A\<close> have "A \<and> B" by (rule conjI)   (*   with facts = from facts this  *)
        with H1 show False by (rule notE)
      qed
      then have not_H2 : "\<not>A \<or> \<not>B" by (rule disjI2)
      with H2 show False by (rule notE)
    qed
    then have not_H2_2 : "\<not>A \<or> \<not>B" by (rule disjI1)
    with H2 show False by (rule notE)
  qed
qed

lemma "A \<and> B \<Longrightarrow> B \<and> A"
proof (rule conjI)
  assume "A \<and> B" thus "B" by (rule conjE)  (* thus = then show = from this show *)
next
  assume "A \<and> B" thus "A" by (rule conjE)
qed

lemma "large_A \<and> large_B \<Longrightarrow> large_B \<and> large_A"
      (is "?AB \<Longrightarrow> ?B \<and> ?A")
proof (rule conjI)
  assume "?AB" thus "?B" by (rule conjE)
next 
  assume "?AB" thus "?A" by (rule conjE)
qed
      
lemma 
  assumes AB : "large_A \<and> large_B"
  shows "large_B \<and> large_A" (is "?B \<and> ?A")
proof (rule conjI)
  from AB show "?B" by (rule conjE)
next 
  from AB show "?A" by (rule conjE)
qed

lemma 
  assumes AB : "large_A \<and> large_B"
  shows "large_B \<and> large_A" (is "?B \<and> ?A")
  using AB
proof 
  assume "?B" "?A" thus ?thesis by (rule conjI)
qed

lemma
  assumes AB : "A \<or> B" 
  shows "B \<or> A"
proof-
  from AB show ?thesis
  proof (rule disjE)
    assume "A" 
    then show ?thesis by (rule disjI2) (* then = from this *)
  next
    assume "B"
    then show ?thesis by (rule disjI1) (* then = from this *)
  qed
qed


(* section 2.4 Predicate calculus *)
lemma
  assumes P : "\<forall>x. P x" 
  shows "\<forall>x. P (f x)"
proof (rule allI)
  fix x
  from P show "P (f x)" by (rule allE)
qed

lemma 
  assumes Pf : "\<exists>x. P(f x)" 
  shows "\<exists>y. P y"
proof -
  show ?thesis using Pf 
  (* = from Pf show ?thesis *)
  proof (rule exE)
    fix x
    assume "P (f x)"
    then show ?thesis by (rule exI)
  qed
qed

lemma assumes Pf : "\<exists>x. P (f x)" shows "\<exists>y. P y"
proof -
  from Pf obtain x where "P (f x)" by (rule exE)
  thus ?thesis by (rule exI)
qed

(* a tautology *)
lemma 
  assumes ex : "\<exists>x. \<forall>y. P x y"
  shows "\<forall>y. \<exists>x. P x y"
proof-
  from ex show ?thesis
  proof (rule exE)
    fix x
    assume "\<forall>y. P x y"
    show ?thesis
    proof (rule allI)
      fix y
      from \<open>\<forall>y. P x y\<close> have "P x y" by (rule allE)
      then show "\<exists>x. P x y" by (rule exI)
    qed
  qed
qed

lemma 
  assumes ex : "\<exists>x. \<forall>y. P x y"
  shows "\<forall>y. \<exists>x. P x y"
proof(rule allI)
  from ex obtain x where "\<forall>y. P x y" by (rule exE)
  fix y
  from \<open>\<forall>y. P x y\<close> have "P x y" by (rule allE)
  then show "\<exists>x. P x y" by (rule exI)
qed

(* section 2.5 Making bigger steps *)
theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{ x. x \<notin> f x }"
  show "?S \<notin> range f "
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof cases
      assume "y \<in> ?S"
      hence "y \<notin> f y" by simp
      hence "y \<notin> ?S" by (simp add:fy)
(*      from \<open>y \<in> ?S\<close>  \<open>y \<notin> ?S\<close> show False by autod*)
    from \<open>y \<in> ?S\<close>  \<open>y \<notin> ?S\<close> show False by contradiction
    next
      assume "y \<notin> ?S"
      hence "y \<in> f y" by simp
      hence "y \<in> ?S" by (simp add:fy)
(*      from \<open>y \<in> ?S\<close>  \<open>y \<notin> ?S\<close> show False by autod*)
    from \<open>y \<in> ?S\<close>  \<open>y \<notin> ?S\<close> show False by contradiction
    qed
  qed
qed

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  by best

lemma "\<forall>x y. A x y \<and> B x y \<longrightarrow> C x y"
proof -
  { fix x y 
    assume "A x y" "B x y"
    have "C x y" sorry}
  thus ?thesis by blast
qed

(* section 2.6 *)
(* Combining proof styles *)
lemma "A \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> B"
proof (rule impI)
  assume "A"
  show "(A \<longrightarrow> B) \<longrightarrow> B"
  proof (rule impI)
    assume "A \<longrightarrow> B" 
    have "B \<Longrightarrow> B" by blast
    from \<open>A \<longrightarrow>B\<close> \<open>A\<close> this show "B" by (rule impE)
  qed
qed

lemma "A \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> B"
proof (rule impI)
  assume a: "A"
  show "(A \<longrightarrow> B) \<longrightarrow> B"
    apply(rule impI)
    apply(erule impE)
    apply(rule a)
    apply assumption
    done
qed

lemma "\<not>A \<or> A"
proof cases
  assume "A" thus ?thesis by (rule disjI2)
next
  assume "\<not>A" thus ?thesis by (rule disjI1)
qed

lemma "\<not>A \<or> A"
proof (cases "A")
  case True thus ?thesis by (rule disjI2)
next  
  case False thus ?thesis by (rule disjI1)
qed

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis by simp
qed

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume Nil: "xs = []" 
  from this show ?thesis by simp
next
  fix x xs'
  assume Cons: " xs = x # xs'"
  thus ?thesis by simp
qed

(* Section 3.2 Structural induction *)
lemma "2 * (\<Sum>i::nat = 0..n. i) = n * (n + 1)" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n
  assume "?P n"
  from this show "?P (Suc n)" by simp
qed

lemma "2 * (\<Sum>i::nat = 0..n. i) = (n::nat) * (n + 1)" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n 
  assume "?P n"
  thus "?P (Suc n)" by simp
qed

lemma "2 * (\<Sum>i::nat = 0 .. n. i) = (n::nat) * (n + 1)"
proof (induction n)
  case 0 show ?case by simp
next 
  case Suc thus ?case by simp
qed

lemma 
  fixes n::nat
  shows "n < n * n + 1"
proof (7657
  case 0 show ?case by simp
next
  case (Suc i) thus "Suc i < Suc i * Suc i + 1" by simp
qed

(* Section 3.3 Induction formulae involving \<And> or \<Longrightarrow> *)
lemma 
  assumes A : "(\<And>(n::nat). (\<And>(m::nat). m < n \<Longrightarrow> P m) \<Longrightarrow> P n)"
  shows "P (n::nat)" (is "?Q n")
proof (rule A)
  show "\<And>m. m < n \<Longrightarrow> P m"
  proof (induct n)
    show "\<And>m. m < 0 \<Longrightarrow> P m"
    proof-
      fix m 
      show "m < 0 \<Longrightarrow> P m"
      proof -
        assume "m < 0"
        from this show "P m" by simp
      qed
    qed
  next
    show "\<And>n m. \<lbrakk>\<And>m. m < n \<Longrightarrow> P m; m < Suc n\<rbrakk> \<Longrightarrow> P m"
    proof -
      fix n 
      fix m
      show "\<lbrakk>\<And>m. m < n \<Longrightarrow> P m; m < Suc n\<rbrakk> \<Longrightarrow> P m"
      proof -
        assume IH : "\<And>k. k < n \<Longrightarrow> P k"
        and "m < Suc n"
        show "P m"
        proof cases
          assume "m = n"
          show "P m"
          proof -   (* passer par \<And>k. k < m \<Longrightarrow> P k  *)
            from A IH have "P n" by simp
            from this \<open>m = n\<close> show "P m" by simp
            (* ou 
            { fix k
              assume "k < m"
              have "P k"
              proof-
                from \<open>k < m\<close> \<open>m = n\<close> have "k < n" by simp
                from this IH show "P k" by simp
              qed
            }
            from this have "\<And>k. k < m \<Longrightarrow> P k" by simp
            from A this show "P m" by simp
          qed  *)
          qed
        next
          assume "m \<noteq> n"
          from this \<open>m < Suc n\<close> have "m < n" by arith
          from this IH show "P m" by simp
        qed
      qed
    qed
  qed
qed
    
(* 3.4 reflexive transitive closure of a relation *)

consts rtc :: "(’a * ’a) set \<Rightarrow> (’a * ’a) set"
refl: "(x,x) \<in> r*"
step: "[ (x,y) \<in> r; (y,z) \<in> r* ] \<Longrightarrow> (x,z) \<in> r*"


  (* les example qui ne marchent pas *)

(*
lemma "A \<longrightarrow> A"
proof
  assume "A"
  show "A" .  (* ? *)
qed
*)
(*
lemma "A \<longrightarrow> A \<and> A"
proof
  assume "A"
  show "A \<and> A" by (rule conjI)
qed 
*)


(*
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from AB show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed
*)

(* 
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  from this show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed 
*)


end