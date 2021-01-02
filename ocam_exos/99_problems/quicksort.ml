(* quicksort *) 

let split l k = (* split the list l into two lists (l1,l2) in which l1 contains the k first elemtns of l*)
    let rec aux l k l2 =
        match l,k with
        |_,0 -> l2,l
        |[],_ -> [],[] (* impossible*)
        |x::tail,k -> aux tail (k-1) (x::l2)
    in aux l k [];;

let partition (lis:'a list) (pivot:'a) (mesure:'a->int) =
    let rec aux lis lis_le lis_gt =
        match lis with
        | [] -> lis_le,lis_gt
        | x::tail -> if (mesure x) < (mesure pivot) then aux tail (x::lis_le) lis_gt    (* take the first elements as pivot*)
                                        else aux tail lis_le (x::lis_gt)
    in aux lis [] [];;

let rec quicksort (lis:'a list) (mesure:'a->int) =
    match lis with
    | [] -> []
    | _ -> let nb_elts_in_first_list = Random.int (List.length lis) in
            let (l1,l2) = split lis nb_elts_in_first_list in
                let pivot = List.hd l2 in
                    let (l3,l4) = partition (l1 @ (List.tl l2)) pivot mesure in
                        List.append (quicksort l3 mesure) (pivot::(quicksort l4 mesure));;
    
(* fuzzing *)
let random_list k m =   (* k random ints between 0 and m-1*)
    let rec aux k lis = 
        match k with 
        | 0 -> lis
        | k -> aux (k-1) ((Random.int m) :: lis)
    in aux k [];;

let rec test lis = 
    match lis with
    | [] -> true
    | [x] -> true
    | x::((y::tail) as l) -> (x <= y) && (test l) ;;

let rec fuzzing k = (* k test ;  n random ints between 0-(m-1) at a time, where n and m are two random ints less than k *)
    let rec aux t k= 
        let n = Random.int k in
            let m = Random.int k in
                match t with
                | 0 -> true
                | t -> let lis = random_list n m in
                        let lis_sorted = quicksort lis (fun x -> x) in
                            (test lis_sorted) && (aux (t-1) k)
    in aux k k;;

fuzzing 1000;; (* 10000 tests; each list has n ints between 0 and (m-1) where n and m are two random ints less than 10000*)