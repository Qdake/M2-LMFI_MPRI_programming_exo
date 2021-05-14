theory "slides_cours_isabelle_s_tourret"
imports Main
begin

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof (rule notI)
  assume a : "surj f"
  (*from this have b: "\<forall>y. \<exists>x. f x = y" by blast*)
  from `surj f` have b : "\<forall>y. \<exists>x. y = f x" by (simp add: surj_def)
  from b have c : "\<exists>x. f x = {y. y \<notin> f y}" by blast
  from c show False by blast
qed

(*
lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs ) \<or>
      (\<exists> ys zs. xs = ys @ zs \<and> length ys = lenght zs + 1)"
proof (induction xs)
  let ?ys = "[]"
  let ?zs = "[]"
  have "[] = ?ys @ ?zs \<and> length ?ys = length ?zs" by simp
  then have "\<exists> ys zs. [] = ys @ zs \<and> length ys = length zs" by blast
  from this show "(\<exists>ys zs. [] = ys @ zs \<and> length ys = length zs) \<or>
    (\<exists>ys zs. [] = ys @ zs \<and> length ys = lenght zs + 1)" by (rule disjI1)
next
  fix a
  fix xs_
  assume xs
  assume IH : "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
       (\<exists>ys zs. xs = ys @ zs \<and> length ys = lenght zs + 1)"

 \<And>a xs.
       (\<exists>ys cb zs. xs = ys @ zs \<and> length ys = length zs) \<or>
       (\<exists>ys zs. xs = ys @ zs \<and> length ys = lenght zs + 1) \<Longrightarrow>
       (\<exists>ys zs. a # xs = ys @ zs \<and> length ys = length zs) \<or>
       (\<exists>ys zs. a # xs = ys @ zs \<and> length ys = lenght zs + 1
*)

end