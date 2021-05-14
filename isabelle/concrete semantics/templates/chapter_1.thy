theory chapter_1
imports Main
begin
notepad
begin
  fix x
  fix x::'a

  fix a b
  assume "a = b"

  define x::'a where "x = t"

  let ?f = "\<lambda>x. x"
  term "?f ?f"
end

notepad
begin

  assume a:A

  have b:B sorry

  note c = a b

end

notepad
begin

  assume a:A
  note a

  assume A
  note this

  assume A

  (*  \<And>x. B x  *)
  (*  note <B a>  *)
  (*  note <B b>  *)

end

(*  Manipulating facts  *)
notepad 
begin

  (* assume a: \<And>x. B x *)
  (* note a
     note a [of b]
     note a [where x = b]  *)

  assume 1: A
  assume 2: "A \<Longrightarrow> C"
  note 2 [OF 1]
  note 1 [THEN 2]

end

[58, 59, 37, 63, 62, 60



end