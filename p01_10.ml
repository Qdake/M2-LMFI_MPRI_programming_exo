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
        