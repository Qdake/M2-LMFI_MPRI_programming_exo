let __EXPRESSION_TO_BE_COMPLETED__ : Z.t = Z.zero

let __CODE_TO_BE_COMPLETED__ : unit = ()

exception TripleFound

let no_3_consecutive_zeros_version_1 (a: (Z.t) array) : bool =
  try
    (let o = Z.sub (Z.of_int (Array.length a)) (Z.of_string "3") in
     let o1 = Z.zero in
     let rec for_loop_to i =
       if Z.leq i o
       then begin
         if
           Z.equal a.(Z.to_int i) Z.zero && Z.equal a.(Z.to_int (Z.add i
                                                                 Z.one))
                                            Z.zero && Z.equal a.(Z.to_int 
                                                      (Z.add i
                                                       (Z.of_string "2")))
                                                      Z.zero
         then raise TripleFound;
         for_loop_to (Z.succ i)
       end
     in for_loop_to o1);
    true
  with
  | TripleFound -> false

let no_3_consecutive_zeros_version_2 (a: (Z.t) array) : bool =
  Z.lt (Z.of_int (Array.length a)) (Z.of_string "3") || (let last2 =
                                                           ref a.(Z.to_int Z.zero) in
                                                         let last1 =
                                                           ref a.(Z.to_int Z.one) in
                                                         try
                                                           (let o =
                                                              Z.sub (Z.of_int (Array.length a))
                                                              Z.one in
                                                            let o1 =
                                                              Z.of_string "2" in
                                                            let rec for_loop_to1 i1 =
                                                              if Z.leq i1 o
                                                              then begin
                                                                (let v =
                                                                   a.(Z.to_int i1) in
                                                                 if
                                                                   Z.equal v
                                                                   Z.zero && 
                                                                   Z.equal !last1
                                                                   Z.zero && 
                                                                   Z.equal !last2
                                                                   Z.zero
                                                                 then 
                                                                 raise TripleFound;
                                                                 last2 :=
                                                                   !last1;
                                                                 last1 := v);
                                                                for_loop_to1 (Z.succ i1)
                                                              end
                                                            in for_loop_to1 o1);
                                                           true
                                                         with
                                                         | TripleFound ->
                                                             false)

let no_3_consecutive_zeros_version_3 (a: (Z.t) array) : bool =
  let count_zeros = ref Z.zero in
  try
    (let o = Z.sub (Z.of_int (Array.length a)) Z.one in let o1 = Z.zero in
     let rec for_loop_to2 i2 =
       if Z.leq i2 o
       then begin
         if Z.equal a.(Z.to_int i2) Z.zero
         then
           if Z.equal !count_zeros (Z.of_string "2")
           then raise TripleFound
           else count_zeros := Z.add !count_zeros Z.one
         else count_zeros := Z.zero;
         for_loop_to2 (Z.succ i2)
       end
     in for_loop_to2 o1);
    true
  with
  | TripleFound -> false

let count_number_of (e: Z.t) (a: (Z.t) array) : Z.t =
  let n = ref Z.zero in
  (let o = Z.sub (Z.of_int (Array.length a)) Z.one in let o1 = Z.zero in
   let rec for_loop_to3 i3 =
     if Z.leq i3 o
     then begin
       if Z.equal a.(Z.to_int i3) e then n := Z.add !n Z.one;
       for_loop_to3 (Z.succ i3)
     end
   in for_loop_to3 o1);
  !n

let same_number_of_zeros_and_ones (a: (Z.t) array) : bool =
  Z.equal (count_number_of Z.zero a) (count_number_of Z.one a)

exception DiffFound

let check_identical_sub_arrays (a: (Z.t) array) (o1: Z.t) (o2: Z.t) (l: Z.t) :
  bool =
  try
    (let o = Z.sub l Z.one in let o3 = Z.zero in
     let rec for_loop_to4 k =
       if Z.leq k o
       then begin
         if not (Z.equal a.(Z.to_int (Z.add o1 k)) a.(Z.to_int (Z.add o2 k)))
         then raise DiffFound;
         for_loop_to4 (Z.succ k)
       end
     in for_loop_to4 o3);
    true
  with
  | DiffFound -> false

let __EXPRESSION_TO_BE_COMPLETED__1 : Z.t = Z.zero

let __CODE_TO_BE_COMPLETED__1 : unit = ()

type elem =
  | Zero
  | One
  | Empty

let eq (x: elem) (y: elem) : bool =
  match (x, y) with
  | ((Empty, Empty) | ((One, One) | (Zero, Zero))) -> true
  | _ -> false

type takuzu_grid = elem array

let column_start_index (n: Z.t) : Z.t = Z.rem n (Z.of_string "8")

let row_start_index (n: Z.t) : Z.t =
  Z.mul (Z.of_string "8") (Z.div n (Z.of_string "8"))

let acc (g: elem array) (start: Z.t) (incr: Z.t) (k1: Z.t) : elem =
  g.(Z.to_int (Z.add start (Z.mul incr k1)))

exception Invalid

let check_rule_1_for_chunk (g: elem array) (start: Z.t) (incr: Z.t) : unit =
  let count_zeros = ref Z.zero in
  let count_ones = ref Z.zero in
  let o = Z.of_string "7" in
  let o1 = Z.zero in
  let rec for_loop_to5 i4 =
    if Z.leq i4 o
    then begin
      begin match acc g start incr i4 with
      | Zero ->
        if Z.equal !count_zeros (Z.of_string "2")
        then raise Invalid
        else
          begin
            count_zeros := Z.add !count_zeros Z.one; count_ones := Z.zero
          end
      | One ->
        if Z.equal !count_ones (Z.of_string "2")
        then raise Invalid
        else
          begin
            count_ones := Z.add !count_ones Z.one; count_zeros := Z.zero
          end
      | Empty -> count_zeros := Z.zero; count_ones := Z.zero
      end;
      for_loop_to5 (Z.succ i4)
    end
  in for_loop_to5 o1

let rec num_occ (e: elem) (g: elem array) (start: Z.t) (incr: Z.t) (l: Z.t) :
  Z.t =
  if Z.equal l Z.zero
  then Z.zero
  else
    begin match eq (acc g start incr (Z.sub l Z.one)) e with
    | true -> Z.add Z.one (num_occ e g start incr (Z.sub l Z.one))
    | false -> num_occ e g start incr (Z.sub l Z.one)
    end

let count_number_of1 (e: elem) (g: elem array) (start: Z.t) (incr: Z.t) : 
  Z.t =
  let n = ref Z.zero in
  (let o = Z.of_string "7" in let o1 = Z.zero in
   let rec for_loop_to6 i5 =
     if Z.leq i5 o
     then begin
       if eq (acc g start incr i5) e then n := Z.add !n Z.one;
       for_loop_to6 (Z.succ i5)
     end
   in for_loop_to6 o1);
  !n

let check_rule_2_for_chunk (g: elem array) (start: Z.t) (incr: Z.t) : unit =
  if Z.gt (count_number_of1 Zero g start incr) (Z.of_string "4")
  then raise Invalid;
  if Z.gt (count_number_of1 Zero g start incr) (Z.of_string "4")
  then raise Invalid

exception DiffFound1

let check_identical_chunks (g: elem array) (start1: Z.t) (start2: Z.t)
                           (incr: Z.t) : bool =
  try
    (let o = Z.of_string "7" in let o1 = Z.zero in
     let rec for_loop_to7 i6 =
       if Z.leq i6 o
       then begin
         begin match (acc g start1 incr i6, acc g start2 incr i6) with
         | (Zero, Zero) -> ()
         | (One, One) -> ()
         | _ -> raise DiffFound1
         end;
         for_loop_to7 (Z.succ i6)
       end
     in for_loop_to7 o1);
    true
  with
  | DiffFound1 -> false

let check_rule_3_for_column (g: elem array) (start: Z.t) : unit =
  let o = Z.of_string "7" in
  let o1 = Z.zero in
  let rec for_loop_to8 i7 =
    if Z.leq i7 o
    then begin
      if not (Z.equal i7 start)
      then begin match check_identical_chunks g start i7 (Z.of_string "8")
           with
      | true -> raise Invalid
      | false -> ()
      end;
      for_loop_to8 (Z.succ i7)
    end
  in for_loop_to8 o1

let check_rule_3_for_row (g: elem array) (start: Z.t) : unit =
  let o = Z.of_string "63" in
  let o1 = Z.zero in
  let rec for_loop_to9 i8 =
    if Z.leq i8 o
    then begin
      if Z.equal (Z.rem i8 (Z.of_string "8")) Z.zero
      then begin
        if not (Z.equal i8 start)
        then begin match check_identical_chunks g start i8 Z.one with
        | true -> raise Invalid
        | false -> ()
        end end;
      for_loop_to9 (Z.succ i8)
    end
  in for_loop_to9 o1

let check_at_cell (g: elem array) (n: Z.t) : unit =
  let col_start = column_start_index n in
  let row_start = row_start_index n in
  check_rule_1_for_chunk g col_start (Z.of_string "8");
  check_rule_1_for_chunk g row_start Z.one;
  check_rule_2_for_chunk g col_start (Z.of_string "8");
  check_rule_2_for_chunk g row_start Z.one;
  check_rule_3_for_column g col_start;
  check_rule_3_for_row g row_start

let check_cell_change (g: elem array) (n: Z.t) (e: elem) : unit =
  g.(Z.to_int n) <- e; check_at_cell g n

exception SolutionFound

let rec solve_aux (g: elem array) (n: Z.t) : unit =
  if Z.equal n (Z.of_string "64") then raise SolutionFound;
  match g.(Z.to_int n) with
  | (Zero | One) ->
    begin try check_at_cell g n; solve_aux g (Z.add n Z.one) with
    | Invalid -> ()
    end
  | Empty ->
    begin try check_cell_change g n Zero; solve_aux g (Z.add n Z.one) with
    | Invalid -> ()
    end;
    begin try check_cell_change g n One; solve_aux g (Z.add n Z.one) with
    | Invalid -> ()
    end;
    g.(Z.to_int n) <- Empty

exception NoSolution

let solve (g: elem array) : unit =
  try solve_aux g Z.zero; raise NoSolution with
  | SolutionFound -> ()

let empty (_: unit) : elem array =
  let a = Array.make (Z.to_int (Z.of_string "64")) Empty in solve a; a

let example1 (_: unit) : elem array =
  let a = Array.make (Z.to_int (Z.of_string "64")) Empty in
  a.(Z.to_int (Z.of_string "2")) <- Zero;
  a.(Z.to_int (Z.of_string "5")) <- One;
  a.(Z.to_int (Z.of_string "8")) <- One;
  a.(Z.to_int (Z.of_string "22")) <- Zero;
  a.(Z.to_int (Z.of_string "25")) <- Zero;
  a.(Z.to_int (Z.of_string "27")) <- Zero;
  a.(Z.to_int (Z.of_string "28")) <- Zero;
  a.(Z.to_int (Z.of_string "30")) <- Zero;
  a.(Z.to_int (Z.of_string "41")) <- Zero;
  a.(Z.to_int (Z.of_string "42")) <- Zero;
  a.(Z.to_int (Z.of_string "44")) <- Zero;
  a.(Z.to_int (Z.of_string "50")) <- Zero;
  a.(Z.to_int (Z.of_string "52")) <- One;
  a.(Z.to_int (Z.of_string "56")) <- One;
  a.(Z.to_int (Z.of_string "62")) <- Zero;
  a.(Z.to_int (Z.of_string "63")) <- Zero;
  solve a;
  a

let example2 (_: unit) : elem array =
  let a = Array.make (Z.to_int (Z.of_string "64")) Empty in
  a.(Z.to_int (Z.of_string "4")) <- Zero;
  a.(Z.to_int (Z.of_string "8")) <- One;
  a.(Z.to_int (Z.of_string "13")) <- Zero;
  a.(Z.to_int (Z.of_string "14")) <- One;
  a.(Z.to_int (Z.of_string "22")) <- One;
  a.(Z.to_int (Z.of_string "25")) <- One;
  a.(Z.to_int (Z.of_string "28")) <- One;
  a.(Z.to_int (Z.of_string "33")) <- One;
  a.(Z.to_int (Z.of_string "46")) <- Zero;
  a.(Z.to_int (Z.of_string "47")) <- Zero;
  a.(Z.to_int (Z.of_string "52")) <- One;
  a.(Z.to_int (Z.of_string "55")) <- Zero;
  a.(Z.to_int (Z.of_string "57")) <- Zero;
  a.(Z.to_int (Z.of_string "58")) <- Zero;
  a.(Z.to_int (Z.of_string "60")) <- One;
  solve a;
  a

let example3 (_: unit) : elem array =
  let a = Array.make (Z.to_int (Z.of_string "64")) Empty in
  a.(Z.to_int Z.one) <- Zero;
  a.(Z.to_int (Z.of_string "3")) <- Zero;
  a.(Z.to_int (Z.of_string "7")) <- Zero;
  a.(Z.to_int (Z.of_string "12")) <- One;
  a.(Z.to_int (Z.of_string "18")) <- One;
  a.(Z.to_int (Z.of_string "23")) <- Zero;
  a.(Z.to_int (Z.of_string "25")) <- One;
  a.(Z.to_int (Z.of_string "37")) <- One;
  a.(Z.to_int (Z.of_string "40")) <- Zero;
  a.(Z.to_int (Z.of_string "46")) <- Zero;
  a.(Z.to_int (Z.of_string "51")) <- One;
  a.(Z.to_int (Z.of_string "53")) <- Zero;
  a.(Z.to_int (Z.of_string "54")) <- Zero;
  a.(Z.to_int (Z.of_string "57")) <- Zero;
  a.(Z.to_int (Z.of_string "60")) <- One;
  solve a;
  a

let example4 (_: unit) : elem array =
  let a = Array.make (Z.to_int (Z.of_string "64")) Empty in
  a.(Z.to_int Z.one) <- One;
  a.(Z.to_int (Z.of_string "2")) <- One;
  a.(Z.to_int (Z.of_string "5")) <- One;
  a.(Z.to_int (Z.of_string "7")) <- Zero;
  a.(Z.to_int (Z.of_string "9")) <- Zero;
  a.(Z.to_int (Z.of_string "11")) <- Zero;
  a.(Z.to_int (Z.of_string "21")) <- One;
  a.(Z.to_int (Z.of_string "23")) <- Zero;
  a.(Z.to_int (Z.of_string "34")) <- Zero;
  a.(Z.to_int (Z.of_string "38")) <- One;
  a.(Z.to_int (Z.of_string "40")) <- Zero;
  a.(Z.to_int (Z.of_string "44")) <- Zero;
  a.(Z.to_int (Z.of_string "47")) <- Zero;
  a.(Z.to_int (Z.of_string "53")) <- One;
  a.(Z.to_int (Z.of_string "55")) <- One;
  a.(Z.to_int (Z.of_string "56")) <- Zero;
  solve a;
  a

let example5 (_: unit) : elem array =
  let a = Array.make (Z.to_int (Z.of_string "64")) Empty in
  a.(Z.to_int (Z.of_string "7")) <- Zero;
  a.(Z.to_int (Z.of_string "15")) <- One;
  a.(Z.to_int (Z.of_string "21")) <- Zero;
  a.(Z.to_int (Z.of_string "24")) <- Zero;
  a.(Z.to_int (Z.of_string "39")) <- Zero;
  a.(Z.to_int (Z.of_string "45")) <- One;
  a.(Z.to_int (Z.of_string "46")) <- One;
  a.(Z.to_int (Z.of_string "50")) <- One;
  a.(Z.to_int (Z.of_string "54")) <- One;
  a.(Z.to_int (Z.of_string "56")) <- One;
  a.(Z.to_int (Z.of_string "59")) <- Zero;
  a.(Z.to_int (Z.of_string "60")) <- Zero;
  solve a;
  a

let example6 (_: unit) : elem array =
  let a = Array.make (Z.to_int (Z.of_string "64")) Empty in
  a.(Z.to_int Z.zero) <- One;
  a.(Z.to_int (Z.of_string "2")) <- One;
  a.(Z.to_int (Z.of_string "7")) <- One;
  a.(Z.to_int (Z.of_string "11")) <- One;
  a.(Z.to_int (Z.of_string "20")) <- Zero;
  a.(Z.to_int (Z.of_string "30")) <- One;
  a.(Z.to_int (Z.of_string "32")) <- One;
  a.(Z.to_int (Z.of_string "37")) <- Zero;
  a.(Z.to_int (Z.of_string "47")) <- Zero;
  a.(Z.to_int (Z.of_string "50")) <- One;
  a.(Z.to_int (Z.of_string "53")) <- Zero;
  a.(Z.to_int (Z.of_string "54")) <- One;
  a.(Z.to_int (Z.of_string "57")) <- Zero;
  a.(Z.to_int (Z.of_string "58")) <- Zero;
  a.(Z.to_int (Z.of_string "62")) <- One;
  solve a;
  a

