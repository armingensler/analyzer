open Prelude
open Cil
open Pretty

let exp_to_string e = sprint 80 (Cil.d_exp () e)
let lval_to_string e = sprint 80 (Cil.d_lval () e)
  
let makeUniformList n x = 
  let rec recfun i acc = if i = 0 then acc else recfun (i - 1) (x :: acc) in
  recfun n []

let get_list_index x xs =
  let (n, _) = List.find (fun (i,y) -> y = x) @@ List.mapi (fun i y -> (i,y)) xs in
  n

    
(* from mCP.ml : BEGIN *)

(** [assoc_split_eq (=) 1 [(1,a);(1,b);(2,x)] = ([a,b],[(2,x)])] *)
let assoc_split_eq (=) (k:'a) (xs:('a * 'b) list) : ('b list) * (('a * 'b) list) =
  let rec f a b = function
    | [] -> a, b
    | (k',v)::xs when k=k' -> f (v::a) b xs
    | x::xs -> f a (x::b) xs
  in
  f [] [] xs

let assoc_split k xs = assoc_split_eq (=) k xs
  
(** [group_assoc_eq (=) [(1,a);(1,b);(2,x);(2,y)] = [(1,[a,b]),(2,[x,y])]] *)
let group_assoc_eq eq (xs: ('a * 'b) list) : ('a * ('b list)) list  =
  let rec f a = function
    | [] -> a
    | (k,v)::xs ->
      let a', b = assoc_split_eq eq k xs in
      f ((k,v::a')::a) b
  in f [] xs

(** [group_assoc [(1,a);(1,b);(2,x);(2,y)] = [(1,[a,b]),(2,[x,y])]] *)
let group_assoc xs = group_assoc_eq (=) xs

(* from mCP.ml : END *)
