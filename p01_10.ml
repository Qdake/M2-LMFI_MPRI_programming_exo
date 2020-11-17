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