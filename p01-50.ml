(* p01 *)
let rec last l =
    match l with
    | e::[] -> Some e
    | e::l -> last l
    | _ -> None
    ;;

(* p02 *)
let rec last_two l =
    match l with
    | e1::e2::[]-> Some (e1,e2)
    | e::l' -> last_two l'
    | _ -> None
    ;;

(* p03 *)
let rec at k l =
    match k,l with
    | 0,_ -> None   
    | 1,e::_ -> Some e
    | k,[] -> None   (* k>=2*)
    | k,e::l -> at (k-1) l;;

(* p04 *)
let rec length l =
    match l with
    | [] -> 0
    | e::l -> 1 + length l;;
let length_tail_rec l =
    let rec aux l k =
        match l with
        | [] -> k
        | e::l -> aux l k+1 
    in aux l 0;;
    
(* p05 *) 
let rev l =
    let rec aux lo lr =
        match lo with   
        | [] -> lr  
        | e::l -> aux l (e::lr)
    in aux l [];;

(* p06 *) 
let is_palindrome l = rev l = l;;

(* p07 *)
type 'a node =
| One of 'a
| Many of 'a node list;;

let flatten l =
    let rec aux lo lr =             
        match lo with   
        | [] -> lr
        | One e :: l -> aux l (e::lr)
        | Many l1 :: l2 -> aux l2 (aux l1 lr)
    in List.rev (aux l []);;

(* p08 *)
let compress l =
    let rec aux lo lr =
        match lo,lr with 
        | [],_ -> lr
        | e::l,[] -> aux l (e::[])
        | e1::l,e2::_ -> if e1 = e2 then aux l lr
                                    else aux l (e1::lr)
    in aux (rev l) [];;  

(* p09 *) 
let pack l = 
    let rec aux lo lr =
        let insert e l =
            match l with    
            | [] -> [e]::l
            | el::l-> if e = List.hd el then let l'=e::el in l'::l 
                                        else [e]::el::l
    in
        match lo,lr with
        | [],_    -> List.rev lr
        | e::l,[] -> aux l [[e]]
        | e::l,l' -> aux l (insert e l')
    in aux l [];;

(* p10 *)
let encode l =
    let
        rec aux l = 
            match l with   
            | [] -> []
            | e::l' -> ((List.length e),List.hd e) :: (aux l')
    in
        aux (pack l);;
         
        
(* p11 *)
type 'a rle =
|One of 'a
|Many of int * 'a;;

let encode2 l =
    let
        rec aux l = 
            let 
                aux_aux e =
                    match List.length e with
                    | 1 -> One (List.hd e)
                    | k -> Many (k,(List.hd e))
            in
                match l with   
                | [] -> []
                | e::l' -> (aux_aux e) :: (aux l')
    in
        aux (pack l);;

(* p12 *)
let decode l =
    let rec aux l =
        let res e = 
            let rec rep x k =
                match k with    
                |0 -> []
                |k -> x::(rep x (k-1))
            in
            match e with   
            | One x -> [x]
            | Many (k,x) -> rep x k
        in
        match l with
        | [] -> []
        | e::l -> List.append (res e) (aux l)
    in
        aux l;; 
        
(* p13 *)
let rec encode3 l =
    match l with
    | [] -> []
    | e::l' ->  let aux e en =
                    match en with
                    |One e' -> if e <> e' then [One e; en]
                                          else [Many (2,e)]
                    |Many (k,e') -> if e <> e' then [One e; en]
                                               else [Many (k+1,e')]
                and l'' = encode3 l'
                in match l'' with
                    |[] -> (One e)::l''
                    |en::l''' -> List.append (aux e en) l''';;

(* p14 *)
let duplicate l =
    let rec aux lo lr =
        match lo with   
        |[] -> List.rev lr
        |e::l -> aux l (e::e::lr)
    in aux l [];;

(* p15 *)
let replicate l k= 
    let rec aux lo lr =
        let rec rep e k r=
            match k with 
            |0 -> r
            |k' -> rep e (k'-1) (e::r)
        in
        match lo with   
        | [] -> List.rev lr
        | e::l -> aux l (List.append (rep e k []) lr)
    in aux l [];;

(* p16 *)
let drop l k =
    let rec aux l k i lr =
        match l,i with    
        |[],_ -> List.rev lr
        |_::l,1 -> aux l k k lr
        |e::l,i -> aux l k (i-1) (e::lr)
    in aux l k k [];;

(* p17 *)
let split l k =
    let rec aux l2 k l1 =
        match l2,k with
        | [],_ -> [List.rev l1;[]]
        | _,0 -> [List.rev l1;l2]
        | e::l, k -> aux l (k-1) (e::l1)
    in aux l k [];;

(* p18 *)
let slice l a b =
    List.nth (split (List.hd (split l (b+1))) a) 1;;

(* p19 *)
let rotate l k = 
    let k' = (k + (List.length l)) mod (List.length l)
    in 
        let l' = split l k' in
            List.append (List.nth l' 1) (List.nth l' 0);;

(* p20 *)
let rec remove_at k l = 
    match l,k with
    | [],_ -> []
    | e::l,0 -> l
    | e::l,k -> e::(remove_at (k-1) l);;

(* p21 *)
let rec insert_at e k l =
    match k,l with
    | 0,_ -> e::l
    | _,[] -> [e]
    | k,x::l -> x::(insert_at e (k-1) l);;

(* p22 *)
let rec range a b =
    if a = b then [b]
             else if a < b then a::(range (a+1) b)
                           else a::(range (a-1) b);;

(* p23 *)
let rec rand_select l k =
    match k with 
    | 0 -> []
    | k -> (List.nth l ( Random.int (List.length l) ) )::(rand_select l (k-1));;

(* p24 *)
let rec remove x l =
  match l with
  | [] -> []
  | e::l -> if e = x then remove x l
                    else e::(remove x l)
;;
let lotto_select k m =
    let rec aux k l =
        match k with    
        |0 -> []
        |k -> let r = List.nth l (Random.int (List.length l)) in
                r :: (aux (k-1) (remove r l))
    and l = range 1 m 
    in aux k l;; 

(* p25 *)
let permutation l = 
    let rec aux k l =
        match k with    
        |0 -> []
        |k -> let r = List.nth l (Random.int (List.length l)) in
                r :: (aux (k-1) (remove r l))
    in aux (List.length l) l;; 

(* p26 *)
let extract k l = 
    let rec extract_aux k ps l=
        match k with 
        | 0 -> [List.rev ps]
        | k -> match l with
               | [] -> [] 
               | x::l -> List.append (extract_aux (k-1) (x::ps) l) (extract_aux k ps l)
    in
        extract_aux k [] l;;

let extract_rec k l =
    match k with   
    | 0 -> [[]]
    | k -> match l with
           | [] -> []
           | x::l -> (extract_rec k l) (extract_rec (k-1) l)


let extract_rec k l = 
    let rec extract_aux k ps lis_1 lis_2 =
        match k with 
        | 0 -> [List.rev ps]
        | k -> match l with
               | [] -> [] 
               | x::l -> List.append (extract_aux (k-1) (x::ps) l) (extract_aux k ps l)
    in
        extract_aux k [] l;;



let extract_2 k l = 
    let rec extract_aux k ps nps l=
        match k with 
        | 0 -> [ [ (List.rev ps); nps @ l] ]
        | k -> match l with
               | [] -> [] 
               | x::l -> let with_x = extract_aux (k-1) (x::ps) nps l 
                         and without_x = extract_aux k ps (x::nps) l in
                                List.append with_x without_x
    in
        extract_aux k [] [] l;;
(* p27 *)
let aux_elt ((x::xs,lis),sol) = 
    let lt = extract_2 x lis in
        List.map (fun [x;y] -> ((xs,y),x::sol)) lt;;
let test = aux_elt ((2::[],["a";"b";"c"]),[]);;

let rec aux l =
    match l with
    | [] -> []
    | e::l -> let ((sizes,_),_) = e in
                if sizes = [] then e::(aux l)
                              else let lt = aux_elt e in
                                        aux (lt @ (aux l));;
let test = aux [((2::[],["a";"b";"c"]),[])];;

let group lis sizes = let sol_raw = aux [((sizes,lis),[])] in
                        List.map (fun (x,y)->y) sol_raw;;

(* p28 *)

(* bubble_sort*)
let rec bubble_sort l =
    let rec bubble l =
        match l with
        | [] -> []
        | [x] -> [x]
        | x::l -> let (y::l') = bubble l in
                    if x < y then x::y::l'
                                else y::x::l'
    in match l with
       | [] -> []
       | [x] -> [x]
       | _ -> let (x::l') = bubble l in x::(bubble_sort l');;           
(* an order *)
let compare_length x y = (List.length x) < (List.length y);;
(* sort with an order as argument *)
let rec sort lis comp =
    let rec bubble lis = 
    match lis with 
    | [] -> []
    | [x] -> [x]
    | x::l -> let (y::l') = bubble l in
                    if comp x y then x::y::l'
                                          else y::x::l'
    in
    match lis with 
    | [] -> []
    | _ -> let (x::l) = bubble lis in
            x::(sort l comp);;
(* sort according to length of elents which are strings*)
let length_sort l = sort l compare_length;;
(* an order *)
let compare_frequency l lx ly =
    let lens = List.map List.length l in    
        let stat_fr = encode (bubble_sort lens) in  
    let rec find_freq x l =
                match l with 
                | [] -> 0
                | e::l' -> match e with
                            | (f,z) -> if z = x then f
                                                else find_freq x l' 
    in  (find_freq (List.length lx) stat_fr) < (find_freq (List.length ly) stat_fr);;
(* sort according to frequency of length *)
let frequency_sort l = sort l (compare_frequency l);;


(* p 31 *)

let is_prime n =
    let rec aux n k =
        match k with    
        | 1 -> true
        | k -> match n mod k with
                | 0 -> false
                | _ -> aux n (k-1)
    in match n with
       | n when n <= 1 -> false
       | n -> aux n (n-1);;

(* p32 *)
let rec gcd m n =
    match n with
    | 0 -> m
    | _ -> if m < n then gcd n m 
                    else gcd (m-n) n;;

(* p33 *) 
let coprime m n = gcd m n = 1;;

(* p34 *)
let phi m =
    let rec aux m k =
        match k with
        | 0 -> 0
        | k -> match coprime m k with   
                |true -> 1 + (aux m (k-1))
                |false -> aux m (k-1)
    in 
        match m with
        | 0 -> 0
        | _ -> aux m (m-1);;

(* p35 *)
let factors n =
    let 
        rec aux n k res = if k > n then res
                               else if not (is_prime k) then aux n (k+1) res
                                                     else if n mod k = 0 then aux (n/k) k (k::res)
                                                                         else aux n (k+1) res
    in
        match n with
        | 0 | 1 -> []
        | n -> aux n 2 [];;

(* p36 *)
let factors_2 n =
    let encode k res =
        match res with
        | [] -> (k,1)::res
        | (((e,t)::res) as p) -> if e = k then (e,t+1)::res 
                                 else (k,1)::p
    in
        let 
            rec aux n k res = if k > n then res
                                else if not (is_prime k) then aux n (k+1) res
                                                        else if n mod k = 0 then aux (n/k) k (encode k res)
                                                                            else aux n (k+1) res
    in
        match n with
        | 0 | 1 -> []
        | n -> aux n 2 [];;

(* p37 *)
let rec pow_int a b =
    match b with 
    | 0 -> 1
    | b -> a * (pow_int a (b-1));;

let phi_improved n =
    let lis_prim_fac = factors_2 n in
        List.fold_left (fun a (p,m) -> (p-1) * (pow_int p (m-1)) * a) 1 lis_prim_fac;;

(* p38 *) 
let timeit f x = 
    let st = Sys.time() in 
        let _ = f x in
            Printf.printf "Execution time : %fs\n" (Sys.time() -. st);;

(* p39*)
let all_primes a b = 
    let rec aux b res = 
        match b with
        | k when k < a -> res
        | k -> let res' = (if is_prime k then [k] else []) @ res 
               in aux (k-1) res'
    in aux b [];; 

(* p40 *)
let goldbach n = 
    let lis_prim = all_primes 2 n in
        let rec aux l =
            match l with    
            | [] -> (0,0)
            | x::l -> let l' = List.filter (fun y -> x + y = n) lis_prim in
                        match l' with
                        | [] -> aux l
                        | y::_-> (x,y)
    in
        aux lis_prim;;

(* p41 *) 
let rec even n = 
    match n with
    |0 -> true
    |1 -> false
    |k -> even (k-2);;
let goldbach_list a b =
    let rec aux b res = 
        match b with
        | k when k < a -> res
        | k -> let res' = (k,goldbach k)::res
                in aux (b-2) res'
    in 
        if even b then aux b []
                  else aux (b-1) [];;

let goldbach_limit a b c =
    let lis = goldbach_list a b in
        List.filter (fun (_,(x,y)) -> x>c && y>c) lis;;

(* Logic and Codes*)
type bool_expr = 
    |Var of string 
    |Not of bool_expr
    |And of bool_expr * bool_expr
    |Or of bool_expr * bool_expr;;
And(Or(Var "a", Var "b"), And(Var "a", Var "b"));;

(* p46 & p47 & p48*)
let rec assignation k =
    match k with   
    | 0 -> [[]]
    | k -> let partial = assignation (k-1) in
              ( List.map (fun a -> true::a) partial ) @ ( List.map (fun a -> false::a) partial );;
let init_lis_vars lis_nom =
    List.map (fun x -> Var x) lis_nom;;
let test = init_lis_vars ["a";"b";"c";"d"];;

let rec eval_expr expr s =
    match expr with
    |Var x -> s (Var x)
    |Not expr -> (not (eval_expr expr s))
    |And (expr1,expr2) -> ((eval_expr expr1 s) && (eval_expr expr2 s))
    |Or (expr1,expr2) -> ((eval_expr expr1 s) || (eval_expr expr2 s));;

let rec eval_var lis_vars lis_values =
    match lis_vars,lis_values with
    |[],_ -> fun x -> false
    |var::lis_vars,value::lis_values -> fun x -> if x = var then value 
                                                            else (eval_var lis_vars lis_values) x 
    |_,_ -> fun x -> true (* impossible*);;
let test = eval_var (init_lis_vars ["a";"b";"c";"d"]) [true;false;true;false];;
let table lis_nom expr = 
    let lis_vars = init_lis_vars lis_nom in
        let lis_all_assignations = assignation (List.length lis_vars) in
            List.map (fun x -> (x,(eval_expr expr (eval_var lis_vars x)))) lis_all_assignations;;

(* p49 *)
let rec gray n = 
    match n with
    | 1 -> ["0";"1"]
    | n -> let l = gray (n-1) in
                (List.map (fun x -> String.concat "" ["0";x]) l) @ (List.map (fun x -> String.concat "" ["1";x]) (List.rev l));;

(* p50 *) 
type huffman_node =
| Leaf 
| Node of string * string * int * huffman_node * huffman_node;;(* code, symbol, frequence, left_tree, right_tree*)


let rec huffman_tree_weight t = 
    match t with
    | Leaf -> 0
    | Node (_,_,k,_,_) -> k;; 

let compare_huffman_tree_weight t1 t2 = (huffman_tree_weight t1) - (huffman_tree_weight t2) ;;

let nodes fs = List.map (fun (s,fs) -> Node("",s,fs,Leaf,Leaf)) fs 

let rec huffman_tree nodes =  
    let nodes_sorted = List.sort compare_huffman_tree_weight nodes 
        in match nodes_sorted with
        | [node] -> node
        | ( Node(_,s,w,lt,rt) as node1 )::( Node(_,s2,w2,lt2,rt2) as node2)::tail -> 
            let weight = w + w2  (*(huffman_tree_weight node1) + (huffman_tree_weight node2) *)
                                in huffman_tree (Node("","",weight,Node("0",s,w,lt,rt), Node("1",s2,w2,lt2,rt2) )::tail)
        | _ -> Leaf;;

let rec gen_code t code_of_parent_node = 
    match t with
    | Leaf -> []
    | Node(c, s, _, lt,rt) -> let code_of_this_node = (String.concat "" [code_of_parent_node;c]) in
                                if s = "" then ((gen_code lt code_of_this_node ) @ (gen_code rt code_of_this_node))
                                          else (s,code_of_this_node)::( (gen_code lt  code_of_this_node ) @ (gen_code rt code_of_this_node) );;

let huffman fs =
    gen_code (huffman_tree (nodes fs)) "";;






