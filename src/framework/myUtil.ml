open Prelude
open Cil
open Pretty

(* from mCP.ml : BEGIN *)

(** [assoc_split_eq (=) 1 [(1,a);(1,b);(2,x)] = ([a,b],[(2,x)])] *)
let assoc_split_eq (=) (k:'a) (xs:('a * 'b) list) : ('b list) * (('a * 'b) list) =
  let rec f a b = function
    | [] -> a, b
    | (k',v)::xs when k=k' -> f (v::a) b xs
    | x::xs -> f a (x::b) xs
  in
  f [] [] xs
  
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
