theory drinker
imports Main
begin


lemma
  fixes n::nat
  shows "(\<Sum>i=(0::nat)..n. i) = n * ( n + 1 ) div 2"
proof (induct n)
  case 0
  have "\<Sum>{(0::nat)..0} = 0" by simp
  also have " (0::nat) = 0 * (0 + 1) div 2" by simp
  finally show ?case .
next  
  case (Suc n)
  have "\<Sum> {(0::nat)..Suc n} = \<Sum> {(0::nat)..n} + (Suc n)" by simp
  also have "... = ((n::nat) * ( n + 1 ) div 2) + (Suc n)" by (simp add: Suc.hyps)
  also have "... = ( n * (n + 1) + 2 * (n + 1)) div 2" by simp 
  also have "... = (Suc n * (Suc n + 1)) div 2" by simp
  finally show ?case .
qed


qed
    


(*  = Suc n * (Suc n + 1) div 2
  *)
(*
  Here is another example of classical reasoning: 
  the Drinker's Principle says
    that for some person, if he is drunk, everybody else is drunk!

  We first prove a classical part of de-Morgan's law.
*)

lemma de_Morgan:
  assumes "\<not> (\<forall>x. P x)"
  shows "\<exists>x. \<not> P x"
proof-
  assume "\<not> (\<exists>x. \<not> P x)"
  have "\<forall>x. P x"
  proof-
    fix x 
    have "P x"
    proof-
      assume "\<not> P x"
      then have "\<exists>x. \<not> P x" ..
      from \<open>\<not> (\<exists>x. \<not> P x)\<close> \<open>\<exists>x. \<not> P x\<close> have False ..
      
    qed
  qed
  with \<open>\<not> (\<forall>x. P x)\<close> show ?thesis by contradiction
qed



lemma de_Morgan:
  assumes 0 : "\<not> (\<forall>x. P x)"
  shows "\<exists>x. \<not> P x"
proof (rule classical)
  assume "A" "B"
  then have "A\<and>B" ..

  fix x
  assume "\<not> (\<exists>x. \<not> P x)"
  have "False"
  proof cases
    assume "\<not> P x"
    then have "\<exists>x. \<not> P x" ..
    with \<open>\<not> (\<exists>x. \<not> P x)\<close> show ?thesis ..
  next
    assume "P x"
    then have "\<forall>x. P x" by blast
    with \<open>\<not> (\<forall>x. P x)\<close> show ?thesis ..

    proof-
      from this show ?thesis ..

lemma "\<And>Drunk::(Humain\<Rightarrow>bool). \<exists>x. (Drunk x \<longrightarrow> (\<forall>y. Drunk y))"

end
