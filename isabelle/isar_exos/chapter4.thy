theory chapter4
imports Main
begin

type_synonym vname = string
(* expression arithemetique*)
(*    5 + 7      *)
(*    Plus (N 5) (N 7)     *)
datatype aexp = 
  N int       
  |V vname
  |Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n"
| "aval (V x) s = s x"
| "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(* boolean expressions *)
datatype bexp = 
  Bc bool 
  |Not bexp
  |And bexp bexp
  |Less aexp aexp

datatype com =
  SKIP  
  |Assign vname aexp 
  |Seq com com  
  |If bexp com com
  |While bexp com

(*theorem "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q" 
  apply (rule conjI)
   apply (assumption)
  apply (assumption)
  done*)
theorem "\<forall>x. \<exists>y. x = y"
  apply (rule allI)
  apply (rule exI)
  apply (rule refl)
  done

theorem "\<forall>x. \<exists>y. x = y"
  apply (rule allI)
方法      apply (rule refl)

  
  

end