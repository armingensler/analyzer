open Prelude
open Cil
open Pretty

let exp_to_string e = sprint 80 (Cil.d_exp () e)
let lval_to_string e = sprint 80 (Cil.d_lval () e)
  
let is_prefix prefix str = 
  String.length str > String.length prefix && String.sub str 0 (String.length prefix) = prefix
    
let list_opt_map f xs =
  List.map Option.get @@ List.filter Option.is_some @@ List.map f xs
    
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
