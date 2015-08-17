open Prelude
open Cil
open Pretty
open Analyses
open GobConfig
open MyUtil

let pp_vars = ["GOBLINT_PP_VAR__FLAG_A"; "GOBLINT_PP_VAR__FLAG_B"; "GOBLINT_PP_VAR__FLAG_C"]
let num_pp_vars = List.length pp_vars

type mySingleFlagState =
  | FS_True
  | FS_False
  | FS_Both

let fs_to_string fs =
  let single_to_string x = 
    match x with
    | FS_True -> "T"
    | FS_False -> "F"
    | FS_Both -> "*" 
  in
  String.concat "" @@ List.map single_to_string fs

type 'd myTree = 
  | MyTree_TF of 'd myTree * 'd myTree
  | MyTree_Both of 'd myTree
  | MyTree_Leaf of 'd option

exception PathResultSplit of int

module MyTree
=
struct
  
  (* Creates a tree of given depth contzaining only of Both nodes a given leaf value. *)
  let rec make_both_tree depth leaf =
    if depth <= 0 then MyTree_Leaf leaf else MyTree_Both (make_both_tree (depth - 1) leaf)
    
  (* Creates a tree representing a single defined value .*)
  let single d = 
    make_both_tree num_pp_vars (Some d)
    
  (* Creates a tree which has a leaf value at a given path and is empty otherwise. *)
  let rec make_path_tree path leaf = 
    match path with
    | (FS_True :: xs) -> MyTree_TF (make_path_tree xs leaf, make_both_tree (List.length xs) None)
    | (FS_False :: xs) -> MyTree_TF (make_both_tree (List.length xs) None, make_path_tree xs leaf)
    | (FS_Both :: xs) -> MyTree_Both (make_path_tree xs leaf)
    | [] -> MyTree_Leaf leaf
  
  (* Returns the leaf at a given path. *)
  let rec get tree path =
    match (tree, path) with
    | (MyTree_TF (t, f), true::xs) -> get t xs
    | (MyTree_TF (t, f), false::xs) -> get f xs
    | (MyTree_TF (t, f), []) -> failwith "MyTreePrintable.get with too short fs"
    | (MyTree_Both tf, x::xs) -> get tf xs
    | (MyTree_Both tf, []) -> failwith "MyTreePrintable.get with too short fs"
    | (MyTree_Leaf leaf, []) -> leaf
    | (MyTree_Leaf leaf, _) -> failwith "MyTreePrintable.get with too long fs"
    
  (* Returns the leaf at a given path. If the path is ambiguous a PathResultSplit exception is raised. *)
  let get_or_raise tree path =
    let rec impl tree path i =
      match (tree, path) with
      | (MyTree_TF (t, f), FS_True::xs) -> impl t xs (i + 1)
      | (MyTree_TF (t, f), FS_False::xs) -> impl f xs (i + 1)
      | (MyTree_TF (t, f), FS_Both::xs) -> raise (PathResultSplit i)
      | (MyTree_TF (t, f), []) -> failwith "MyTreePrintable.get with too short fs"
      | (MyTree_Both tf, x::xs) -> impl tf xs (i + 1)
      | (MyTree_Both tf, []) -> failwith "MyTreePrintable.get with too short fs"
      | (MyTree_Leaf leaf, []) -> leaf
      | (MyTree_Leaf leaf, _) -> failwith "MyTreePrintable.get with too long fs"
    in impl tree path 0
  
  (* Combines all leaves with the function f starting wittzh the value x. *)
  let fold f x tree =
    let rec impl acc tree path =
      begin match tree with
      | MyTree_TF (t, f) -> 
        let acc' = impl acc t (path @ [FS_True]) in
        impl acc' f (path @ [FS_False])
      | MyTree_Both tf -> impl acc tf (path @ [FS_Both])
      | MyTree_Leaf leaf -> f acc leaf path
      end in
    impl x tree []
  
  (* Returns if a function is true for all leaf values. *)
  let for_all f tree =
    let rec impl tree path =
      begin match tree with
      | MyTree_TF (t, f) -> impl t (path @ [FS_True]) && impl f (path @ [FS_False])
      | MyTree_Both tf -> impl tf (path @ [FS_Both])
      | MyTree_Leaf leaf -> f leaf path
      end in
    impl tree []
  
  (* Returns if a function is true for at least one leaf value. *)
  let exists f tree =
    let rec impl tree path =
      begin match tree with
      | MyTree_TF (t, f) -> impl t (path @ [FS_True]) || impl f (path @ [FS_False])
      | MyTree_Both tf -> impl tf (path @ [FS_Both])
      | MyTree_Leaf leaf -> f leaf path
      end in
    impl tree []
    
  (* Returns if all leafes specified by the path exist, i.e. are not None. *)
  let rec contains tree path =
    match (tree, path) with
    | (MyTree_TF (t, f), FS_True::xs) -> contains t xs
    | (MyTree_TF (t, f), FS_False::xs) -> contains f xs
    | (MyTree_TF (t, f), FS_Both::xs) -> contains t xs && contains f xs
    | (MyTree_TF (t, f), []) -> failwith "MyTreePrintable.contains with too short fs"
    | (MyTree_Both tf, x::xs) -> contains tf xs
    | (MyTree_Both tf, []) -> failwith "MyTreePrintable.contains with too short fs"
    | (MyTree_Leaf leaf, x::xs) -> failwith "MyTreePrintable.contains with too long fs"
    | (MyTree_Leaf leaf, []) -> Option.is_some leaf
  
  (* Transforms all leaves by applying a function. *)
  let map f tree =
    let rec impl tree path =
      begin match tree with
      | MyTree_TF (t, f) -> MyTree_TF (impl t (path @ [FS_True]), impl f (path @ [FS_False]))
      | MyTree_Both tf -> MyTree_Both (impl tf (path @ [FS_Both]))
      | MyTree_Leaf leaf -> MyTree_Leaf (f leaf path)
      end in
    impl tree []
  
  (* Transforms all leaves which are not NONE by applying a function. *)
  let mapSome f tree = 
    map (fun leaf path -> if Option.is_some leaf then f (Option.get leaf) path else None) tree
  
  (* Transforms all leaves by applying a function. *)
  let to_list f tree =
    let rec impl tree path =
      begin match tree with
      | MyTree_TF (t, f) -> impl t (path @ [FS_True]) @ impl f (path @ [FS_False])
      | MyTree_Both tf -> impl tf (path @ [FS_Both])
      | MyTree_Leaf leaf -> [f leaf path]
      end in
    impl tree []
  
  (* Transforms all non empty leaves by applying a function. *)
  let to_some_list f tree =
    let rec impl tree path =
      begin match tree with
      | MyTree_TF (t, f) -> impl t (path @ [FS_True]) @ impl f (path @ [FS_False])
      | MyTree_Both tf -> impl tf (path @ [FS_Both])
      | MyTree_Leaf (Some leaf) -> [f leaf path]
      | MyTree_Leaf None -> []
      end in
    impl tree []

  (* Executes f for each pair of values in both trees. *)
  let iter_2 f xtree ytree : unit =
    let rec impl xtree ytree path =
      match (xtree, ytree) with
      | (MyTree_TF (xt, xf), MyTree_TF (yt, yf)) -> impl xt yt (path @ [FS_True]); impl xf yf (path @ [FS_False])
      | (MyTree_TF (xt, xf), MyTree_Both ytf) -> impl xt ytf (path @ [FS_True]); impl xf ytf (path @ [FS_False])
      | (MyTree_Both xtf, MyTree_TF (yt, yf)) -> impl xtf yt (path @ [FS_True]); impl xtf yf (path @ [FS_False])
      | (MyTree_Both xtf, MyTree_Both ytf) -> impl xtf ytf (path @ [FS_Both])
      | (MyTree_Leaf xleaf, MyTree_Leaf yleaf) -> f xleaf yleaf path
      | (MyTree_Leaf xleaf, _) -> failwith "Called MyTree.iter_2 with inconsistent tree height."
      | (_, MyTree_Leaf yleaf) -> failwith "Called MyTree.iter_2 with inconsistent tree height."
    in
    impl xtree ytree []

  (* Returns if f is true for each pair of values in both trees. *)
  let for_all_2 f xtree ytree =
    let rec impl xtree ytree path =
      match (xtree, ytree) with
      | (MyTree_TF (xt, xf), MyTree_TF (yt, yf)) -> impl xt yt (path @ [FS_True]) && impl xf yf (path @ [FS_False])
      | (MyTree_TF (xt, xf), MyTree_Both ytf) -> impl xt ytf (path @ [FS_True]) && impl xf ytf (path @ [FS_False])
      | (MyTree_Both xtf, MyTree_TF (yt, yf)) -> impl xtf yt (path @ [FS_True]) && impl xtf yf (path @ [FS_False])
      | (MyTree_Both xtf, MyTree_Both ytf) -> impl xtf ytf (path @ [FS_Both])
      | (MyTree_Leaf xleaf, MyTree_Leaf yleaf) -> f xleaf yleaf path
      | (MyTree_Leaf xleaf, _) -> failwith "Called MyTree.for_all_2 with inconsistent tree height."
      | (_, MyTree_Leaf yleaf) -> failwith "Called MyTree.for_all_2 with inconsistent tree height."
    in
    impl xtree ytree []

  (* Returns a new tree by combining each pair of values in both trees with f. *)
  let map_2 f xtree ytree =
    let rec impl xtree ytree path =
      match (xtree, ytree) with
      | (MyTree_TF (xt, xf), MyTree_TF (yt, yf)) -> MyTree_TF (impl xt yt (path @ [FS_True]), impl xf yf (path @ [FS_False]))
      | (MyTree_TF (xt, xf), MyTree_Both ytf) -> MyTree_TF (impl xt ytf (path @ [FS_True]), impl xf ytf (path @ [FS_False]))
      | (MyTree_Both xtf, MyTree_TF (yt, yf)) -> MyTree_TF (impl xtf yt (path @ [FS_True]), impl xtf yf (path @ [FS_False]))
      | (MyTree_Both xtf, MyTree_Both ytf) -> MyTree_Both (impl xtf ytf (path @ [FS_Both]))
      | (MyTree_Leaf xleaf, MyTree_Leaf yleaf) -> MyTree_Leaf (f xleaf yleaf path)
      | (MyTree_Leaf xleaf, _) -> failwith "Called MyTree.map_2 with inconsistent tree height."
      | (_, MyTree_Leaf yleaf) -> failwith "Called MyTree.map_2 with inconsistent tree height."
    in
    impl xtree ytree []
    
  let rec zip_strict xtree ytree =
    match (xtree, ytree) with
    | (MyTree_TF (xt, xf), MyTree_TF (yt, yf)) -> MyTree_TF (zip_strict xt yt, zip_strict xf yf)
    | (MyTree_TF (xt, xf), MyTree_Both ytf) -> MyTree_TF (zip_strict xt ytf, zip_strict xf ytf)
    | (MyTree_Both xtf, MyTree_TF (yt, yf)) -> MyTree_TF (zip_strict xtf yt, zip_strict xtf yf)
    | (MyTree_Both xtf, MyTree_Both ytf) -> MyTree_Both (zip_strict xtf ytf)
    | (MyTree_Leaf (Some xleaf), MyTree_Leaf (Some yleaf)) -> MyTree_Leaf (Some (xleaf, yleaf))
    | (MyTree_Leaf (Some xleaf), MyTree_Leaf None) -> MyTree_Leaf None
    | (MyTree_Leaf None, MyTree_Leaf (Some yleaf)) -> MyTree_Leaf None
    | (MyTree_Leaf None, MyTree_Leaf None) -> MyTree_Leaf None
    | (MyTree_Leaf xleaf, _) -> failwith "Called MyTree.zip_strict with inconsistent tree height."
    | (_, MyTree_Leaf yleaf) -> failwith "Called MyTree.zip_strict with inconsistent tree height."
  
end

module MyTreePrintable (L:Printable.S)
= 
struct
  
  type t = L.t myTree
  
  include MyTree
  
  let rec short i d = 
    match d with
    | MyTree_TF (t, f) -> "[ T -> " ^ short i t ^ ", F -> " ^ short i f ^ "]"
    | MyTree_Both tf -> "[ * -> " ^ short i tf ^ "]"
    | MyTree_Leaf (Some leaf) -> "(" ^ L.short i leaf ^ ")"
    | MyTree_Leaf None -> "NONE"
    
  let name () = "MyTreePrintable" ^ (L.name ())
  
  include Printable.PrintSimple (struct type t' = t let short = short let name = name end)
  
  let compare = Pervasives.compare
  
  let rec equal x y = 
    match (x, y) with
    | (MyTree_TF (xtrue, xfalse), MyTree_TF (ytrue, yfalse)) -> equal xtrue ytrue && equal xfalse yfalse 
    | (MyTree_Both xboth, MyTree_Both yboth) -> equal xboth yboth
    | (MyTree_Leaf (Some xleaf), MyTree_Leaf (Some yleaf)) -> L.equal xleaf yleaf
    | (MyTree_Leaf None, MyTree_Leaf None) -> true
    | _ -> false
  
  let rec hash d =
    match d with
    | MyTree_TF (t, f) -> hash t * 7 + hash f * 13 + 17
    | MyTree_Both both -> hash both * 7 + 23
    | MyTree_Leaf (Some leaf) -> L.hash leaf * 3
    | MyTree_Leaf None -> 31

  (* Simplifies the root node of the tree by merging TF nodes with identical children into a
     single Both node. *)
  let rec simplify_nonrec tree =
    match tree with
    | MyTree_TF (t, f) when equal t f -> MyTree_Both t
    | _ -> tree
    
  (* Simplifies the tree by merging TF nodes with identical children into a single Both node.
     This is done recursively to the whole tree. *)
  let rec simplify tree =
    match tree with
    | MyTree_TF (t, f) -> 
      let st = simplify t in
      let sf = simplify f in
      if equal st sf then MyTree_Both st else MyTree_TF (st, sf)
    | MyTree_Both tf -> MyTree_Both (simplify tf)
    | MyTree_Leaf leaf -> MyTree_Leaf leaf
  
  (* Sets all leaves of the tree for which the variable[pos] <> value to None. *) 
  let restrict pos value (tree : t) =
    let rec impl tree i =
      if i < pos then begin
        match tree with
        | MyTree_TF (t, f) -> simplify_nonrec @@ MyTree_TF (impl t (i + 1), impl f (i + 1))
        | MyTree_Both tf -> MyTree_Both (impl tf (i + 1))
        | MyTree_Leaf leaf -> failwith "Called MyTreePrintable.restrict with inconsistent tree height."
      end else begin
        match tree with
        | MyTree_TF (t, f) -> 
          if value 
          then simplify_nonrec @@ MyTree_TF (t, make_both_tree (num_pp_vars - pos - 1) None) 
          else simplify_nonrec @@ MyTree_TF (make_both_tree (num_pp_vars - pos - 1) None, f)
        | MyTree_Both tf -> 
          if value 
          then simplify_nonrec @@ MyTree_TF (tf, make_both_tree (num_pp_vars - pos - 1) None) 
          else simplify_nonrec @@ MyTree_TF (make_both_tree (num_pp_vars - pos - 1) None, tf)
        | MyTree_Leaf leaf -> MyTree_Leaf leaf
      end
    in
    impl tree 0
  
  (* Returns a string showing all mappings in this tree without the actual tree structure. *)
  let to_content_string tree =
    let f leaf path = 
      match leaf with
      | None -> fs_to_string path ^ " -> NONE"
      | Some x -> fs_to_string path ^ " -> (" ^ L.short 80 x ^ ")" 
    in
    "[" ^ (String.concat ", " @@ to_list f tree) ^ "]"
  
end

module MyTreeDom (L:Lattice.S)
= 
struct
  
  include MyTreePrintable (L)
  include Lattice.StdCousot (* ??? *)
  
  let leq xtree ytree =
    
    (* Returns if d is <= than all leaves of ytree at path. *)
    let rec leq_than_all_at_path tree d path = 
      match tree with
      
      | MyTree_TF (t, f) ->
        begin match path with
        | FS_True::xs -> leq_than_all_at_path t d xs
        | FS_False::xs -> leq_than_all_at_path f d xs
        | FS_Both::xs -> leq_than_all_at_path t d xs && leq_than_all_at_path f d xs
        | [] -> failwith "Called MyTreeDom.leq with inconsistent tree heights."
        end
        
      | MyTree_Both tf ->
        begin match path with
        | FS_True::xs -> leq_than_all_at_path tf d xs
        | FS_False::xs -> leq_than_all_at_path tf d xs
        | FS_Both::xs -> leq_than_all_at_path tf d xs
        | [] -> failwith "Called MyTreeDom.leq with inconsistent tree heights."
        end        
      
      | MyTree_Leaf leaf -> 
        begin match path with
        | [] -> Option.is_some leaf && L.leq d (Option.get leaf)
        | _ -> failwith "Called MyTreeDom.leq with inconsistent tree heights."
        end
      
    in
    let f leaf path = Option.is_none leaf || leq_than_all_at_path ytree (Option.get leaf) path in
    for_all f xtree
    
  let rec join x y = 
    match (x, y) with
    | (MyTree_Leaf (Some xleaf), MyTree_Leaf (Some yleaf)) -> MyTree_Leaf (Some (L.join xleaf yleaf))
    | (MyTree_Leaf (Some xleaf), MyTree_Leaf None) -> MyTree_Leaf (Some xleaf)
    | (MyTree_Leaf None, MyTree_Leaf (Some yleaf)) -> MyTree_Leaf (Some yleaf)
    | (MyTree_Leaf None, MyTree_Leaf None) -> MyTree_Leaf None
    | (MyTree_Leaf xleaf, _) -> failwith "Called MyTreeDom.join with inconsistent tree heights."
    | (_, MyTree_Leaf yleaf) -> failwith "Called MyTreeDom.join with inconsistent tree heights."
    | (MyTree_TF (xt, xf), MyTree_TF (yt, yf)) -> simplify_nonrec @@ MyTree_TF (join xt yt, join xf yf)
    | (MyTree_TF (xt, xf), MyTree_Both ytf) -> simplify_nonrec @@ MyTree_TF (join xt ytf, join xf ytf)
    | (MyTree_Both xtf, MyTree_TF (yt, yf)) -> simplify_nonrec @@ MyTree_TF (join xtf yt, join xtf yf)
    | (MyTree_Both xtf, MyTree_Both ytf) -> MyTree_Both (join xtf ytf)
    
  let rec meet x y = 
    match (x, y) with
    | (MyTree_Leaf (Some xleaf), MyTree_Leaf (Some yleaf)) -> MyTree_Leaf (Some (L.meet xleaf yleaf))
    | (MyTree_Leaf (Some xleaf), MyTree_Leaf None) -> MyTree_Leaf None
    | (MyTree_Leaf None, MyTree_Leaf (Some yleaf)) -> MyTree_Leaf None
    | (MyTree_Leaf None, MyTree_Leaf None) -> MyTree_Leaf None    
    | (MyTree_Leaf xleaf, _) -> failwith "Called MyTreeDom.meet with inconsistent tree heights."
    | (_, MyTree_Leaf yleaf) -> failwith "Called MyTreeDom.meet with inconsistent tree heights."
    | (MyTree_TF (xt, xf), MyTree_TF (yt, yf)) -> simplify_nonrec @@ MyTree_TF (meet xt yt, meet xf yf)
    | (MyTree_TF (xt, xf), MyTree_Both ytf) -> simplify_nonrec @@ MyTree_TF (meet xt ytf, meet xf ytf)
    | (MyTree_Both xtf, MyTree_TF (yt, yf)) -> simplify_nonrec @@ MyTree_TF (meet xtf yt, meet xtf yf)
    | (MyTree_Both xtf, MyTree_Both ytf) -> MyTree_Both (meet xtf ytf)
    
  let bot () = make_both_tree num_pp_vars None
  
  let is_bot tree = for_all (fun leaf fs -> Option.is_none leaf) tree
    
  let top () = make_both_tree num_pp_vars (Some (L.top ()))
  
  let is_top tree = for_all (fun leaf fs -> Option.is_some leaf && L.is_top (Option.get leaf)) tree
  
  let rec joined_fs_path tree path =
    match (tree, path) with
    | (MyTree_TF (t, f), FS_True::xs) -> joined_fs_path t xs
    | (MyTree_TF (t, f), FS_False::xs) -> joined_fs_path f xs
    | (MyTree_TF (t, f), FS_Both::xs) -> L.join (joined_fs_path t xs) (joined_fs_path f xs)
    | (MyTree_TF (t, f), []) -> failwith "MyTreePrintable.get with too short fs"
    | (MyTree_Both tf, x::xs) -> joined_fs_path tf xs
    | (MyTree_Both tf, []) -> failwith "MyTreePrintable.get with too short fs"
    | (MyTree_Leaf (Some leaf), []) -> leaf
    | (MyTree_Leaf None, []) -> L.bot ()
    | (MyTree_Leaf leaf, _) -> failwith "MyTreePrintable.get with too long fs"
    
  let make_from_list xs =
    List.fold_left join (bot ()) @@ List.map (fun (path, d) -> make_path_tree path (Some d)) xs
    
end

module TestPrintable : Printable.S = MyTreePrintable (Printable.Unit)
module TestLattice : Lattice.S = MyTreeDom (Lattice.Unit)

module PpFlagDependent (S:Spec)
  : Spec with module D = MyTreeDom (S.D)
          and module G = MyTreeDom (S.G)
          and module C = MyTreePrintable (S.C)
=
struct
  
  module D = MyTreeDom (S.D)
  module G = MyTreeDom (S.G)
  module C = MyTreePrintable (S.C)
  
  let child_ctx child_d (path : mySingleFlagState list) (ctx : (D.t, G.t) Analyses.ctx) 
    (spawn_acc : (mySingleFlagState list * varinfo * S.D.t) list ref) 
    (split_acc : (mySingleFlagState list * S.D.t * exp * bool) list ref)
    (sideg_acc : (mySingleFlagState list * varinfo * S.G.t) list ref)
    (assign_acc : (mySingleFlagState list * string option * lval * exp) list ref) =
    
    let rec ask q = S.query ctx' q
    and global v = Option.default (S.G.bot ()) @@ G.get_or_raise (ctx.global v) path
    
    and spawn v d = spawn_acc := (path, v, d) :: !spawn_acc
    and split d e b = split_acc := (path, d, e, b) :: !split_acc
    and sideg v g = sideg_acc := (path, v, g) :: !sideg_acc
    and assign ?name lv e = failwith "\"assign\" should not be propagated to this module becasue it is already handeled in MCP." (*assignAcc := (i, name, lv, e) :: !assignAcc*)
    
    and ctx' = { 
        ask = ask
      ; local = child_d
      ; global = global
      ; presub = ctx.presub
      ; postsub = ctx.postsub
      ; spawn = spawn
      ; split = split
      ; sideg = sideg
      ; assign = assign
    }
    in
    
    ctx'

  let name = S.name^" pp_flag_dependent"
  
  (*
  module T = MyTreeDom (IntDomain.Lifted)
  let tree_test () =
    print_endline "";
    print_endline "-> tree_test.start";
    print_endline "";
    
    let t = T.single (IntDomain.Lifted.bot ()) in
    print_endline ("t = " ^ T.to_content_string t);
    
    let t1 = T.map (fun leaf path -> Option.map (fun x -> IntDomain.Lifted.of_int 1L) leaf) @@ T.restrict t 1 true in
    print_endline ("t1 = " ^ T.to_content_string t1);
    let t2 = T.map (fun leaf path -> Option.map (fun x -> IntDomain.Lifted.of_int 2L) leaf) @@ T.restrict t 0 false in
    print_endline ("t2 = " ^ T.to_content_string t2);
    let joined = T.join t1 t2 in
    print_endline ("joined = " ^ T.to_content_string joined);
    let met = T.meet t1 t2 in
    print_endline ("meet = " ^ T.to_content_string met);
    print_endline "";
    
    let tt = T.map (fun leaf path -> Option.map (fun x -> IntDomain.Lifted.of_int 10L) leaf) @@ T.restrict t 1 true in
    print_endline ("tt = " ^ T.to_content_string tt);
    let tf = T.map (fun leaf path -> Option.map (fun x -> IntDomain.Lifted.of_int 10L) leaf) @@ T.restrict t 1 false in
    print_endline ("tf = " ^ T.to_content_string tf);
    let joined = T.join tt tf in
    print_endline ("joined = " ^ T.to_content_string joined);
    let met = T.meet tt tf in
    print_endline ("met = " ^ T.to_content_string met);
    
    let redundant = MyTree_TF ( 
      MyTree_Both (MyTree_TF (MyTree_Leaf None, MyTree_Leaf (Some (IntDomain.Lifted.of_int 100L)))),   
      MyTree_Both (MyTree_TF (MyTree_Leaf None, MyTree_Leaf (Some (IntDomain.Lifted.of_int 100L))))
      ) in
    print_endline ("redundant = " ^ T.to_content_string redundant); 
    let simplified = T.simplify redundant in
    print_endline ("simplified = " ^ T.to_content_string (T.simplify simplified));
    
    let t100 = T.single (IntDomain.Lifted.of_int 100L) in
    print_endline ("t100 = " ^ T.to_content_string t100);
    let t200 = T.single (IntDomain.Lifted.of_int 200L) in
    print_endline ("t200 = " ^ T.to_content_string t200); 
    print_endline ("t100 <= t200 = " ^ (string_of_bool @@ T.leq t100 t200));
    print_endline "";
    
    let t1 = T.simplify @@ MyTree_TF ( 
      MyTree_Both (MyTree_TF (MyTree_Leaf None, MyTree_Leaf None)),   
      MyTree_Both (MyTree_TF (MyTree_Leaf None, MyTree_Leaf (Some (IntDomain.Lifted.of_int 200L))))
      ) in
    print_endline ("t1 = " ^ T.to_content_string t1);
    let t2 = T.simplify @@ MyTree_TF ( 
      MyTree_Both (MyTree_TF (MyTree_Leaf None, MyTree_Leaf (Some (IntDomain.Lifted.of_int 100L)))),   
      MyTree_Both (MyTree_TF (MyTree_Leaf None, MyTree_Leaf (Some (IntDomain.Lifted.of_int 200L))))
      ) in
    print_endline ("t2 = " ^ T.to_content_string t2);
    print_endline ("t1 <= t2 = " ^ (string_of_bool @@ T.leq t1 t2));
    print_endline "";
    
    let t1 = T.simplify @@ MyTree_TF ( 
      MyTree_Both (MyTree_TF (MyTree_Leaf None, MyTree_Leaf None)),   
      MyTree_Both (MyTree_TF (MyTree_Leaf None, MyTree_Leaf (Some (IntDomain.Lifted.of_int 200L))))
      ) in
    print_endline ("t1 = " ^ T.to_content_string t1);
    let t2 = T.simplify @@ MyTree_TF ( 
      MyTree_Both (MyTree_Both (MyTree_Leaf (Some (IntDomain.Lifted.of_int 100L)))),   
      MyTree_Both (MyTree_Both (MyTree_Leaf None))
      ) in
    print_endline ("t2 = " ^ T.to_content_string t2);
    let f x y path = 
      match (x, y) with
      | (Some x, Some y) -> print_endline (fs_to_string path ^ " -> (" ^ IntDomain.Lifted.short 80 x ^ ", " ^ IntDomain.Lifted.short 80 y ^ ")")
      | (Some x, None) -> print_endline (fs_to_string path ^ " -> (" ^ IntDomain.Lifted.short 80 x ^ ", NONE)")
      | (None, Some y) -> print_endline (fs_to_string path ^ " -> (NONE, " ^ IntDomain.Lifted.short 80 y ^ ")")
      | (None, None) -> print_endline (fs_to_string path ^ " -> (NONE, NONE)")
    in
    T.iter_2 f t1 t2;
    print_endline "";    
     
    print_endline "";
    print_endline "-> tree_test.end";
    print_endline ""
  *)

  let init () = (*tree_test();*) S.init ()
  let finalize () = S.finalize ()
  
  let startstate v = D.single @@ S.startstate v
  let exitstate v = D.single @@ S.exitstate v
  let otherstate v = D.single @@ S.otherstate v
  let morphstate v ds = D.simplify @@ D.mapSome (fun d path -> Some (S.morphstate v d)) ds
  
  let should_join (xs : D.t) (ys : D.t) = 
    print_endline "should_join";
    let f x y path = 
      match (x, y) with
      | (Some x, Some y) -> S.should_join x y
      | (None, None) -> true
      | _ -> false
    in
    D.for_all_2 f xs ys
  
  let val_of ds = D.simplify @@ C.map (fun leaf path -> Option.map (fun d -> S.val_of d) leaf) ds
  let context ds = C.simplify @@ D.map (fun leaf path -> Option.map (fun d -> S.context d) leaf) ds
  
  let call_descr func ds = 
    print_endline "call_descr";
    let leaves = D.to_some_list (fun leaf path -> leaf) ds in
    let head = List.hd leaves in (* ??? *)
    S.call_descr func head (* ??? *)
    
  let do_spawn ctx (xs : (mySingleFlagState list * varinfo * S.D.t) list) =
    let spawn_one (v : varinfo) (ds : (mySingleFlagState list * S.D.t) list) =
      let join_vals (path, d) = path, List.fold_left S.D.join (S.D.bot ()) d in
      let make_tree (path, d) = D.make_path_tree path (Some d) in
      let joined = List.fold_left (D.join) (D.bot ()) @@ List.map make_tree @@ List.map join_vals @@ group_assoc ds in
      ctx.spawn v joined
    in
    if not (get_bool "exp.single-threaded") then
      List.iter (uncurry spawn_one) @@ group_assoc_eq Basetype.Variables.equal @@ List.map (fun (fs, v, d) -> (v, (fs, d))) xs
  
  let do_split ctx (xs : (mySingleFlagState list * S.D.t * exp * bool) list) =
    let split_one (e, v) ys =
      let grouped = group_assoc ys in
      let num = List.max @@ List.map (fun (path, ds) -> List.length ds) grouped in
      let get_nth n = 
        let nth = List.map (fun (path, ds) -> (path, List.nth ds n)) @@ List.filter (fun (path, ds) -> List.length ds > n) grouped in
        D.make_from_list nth
      in
      List.iter (fun d -> ctx.split d e v) @@ List.map get_nth @@ List.of_enum (0 -- (num - 1))
    in
    List.iter (uncurry split_one) @@ group_assoc @@ List.map (fun (path, d, e, v) -> ((e, v), (path, d))) xs
     
  let do_sideg ctx (xs : (mySingleFlagState list * varinfo * S.G.t) list) =
    let spawn_one v (ds : (mySingleFlagState list * S.G.t) list) = 
      let join_vals (path, d) = path, List.fold_left S.G.join (S.G.bot ()) d in
      let make_tree (path, d) = G.make_path_tree path (Some d) in
      let joined = List.fold_left (G.join) (G.bot ()) @@ List.map make_tree @@ List.map join_vals @@ group_assoc ds in
      ctx.sideg v joined
    in
    List.iter (uncurry spawn_one) @@ group_assoc_eq Basetype.Variables.equal @@ List.map (fun (fs, v, g) -> (v, (fs, g))) xs
    
  let do_assign ctx (xs : (mySingleFlagState list * string option * lval * exp) list) =
    if List.length xs > 0 then failwith "This should never be called." else ()
    
  (* Maps each non-empty tree leaf to a new leaf using the function f. 
     Automatically splits a TF node if a PathResultSplit exception is caught. *)
  let execute_for_each_child f d = 
    
    let rec impl tree path i =
      begin match tree with
      | MyTree_TF (t, f) -> 
          let rt = impl t (path @ [FS_True]) (i + 1) in
          let rf = impl f (path @ [FS_False]) (i + 1) in
          MyTree_TF (rt, rf)
      | MyTree_Both tf -> 
        begin 
          try MyTree_Both (impl tf (path @ [FS_Both]) (i + 1)) 
          with PathResultSplit split_idx when split_idx = i -> impl (MyTree_TF (tf, tf)) path i
        end
      | MyTree_Leaf (Some leaf) -> MyTree_Leaf (Some (f leaf path))
      | MyTree_Leaf None -> MyTree_Leaf None
      end 
    in
    
    impl d [] 0
    
  let sync ctx : (D.t * (varinfo * G.t) list)  =
    print_endline "sync";
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    (* execute child function for all children *)
    let handle_child d path = S.sync (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) in
    let result = execute_for_each_child handle_child ctx.local in
    
    let dtree = D.simplify @@ D.mapSome (fun (x, y) path -> Some x) result in
    let gtree = D.mapSome (fun (x, y) path -> Some y) result in
    
    (* get all varinfos in gtree *)
    let varinfo_collector leaf path = 
      match leaf with
      | None -> []
      | Some d -> List.map fst d
    in
    let varinfos = List.unique ~eq:Basetype.Variables.equal @@ List.flatten @@ D.to_list varinfo_collector gtree in
    
    (* get tree for each varinfo *)
    let get_varinfo_tree (var : varinfo) =
      let join_all gs = List.fold_left S.G.join (S.G.bot ()) gs in
      let joined leaf path = Some (join_all @@ List.map snd @@ List.filter (fun (v, g) -> Basetype.Variables.equal v var) leaf) in
      G.simplify @@ D.mapSome joined gtree
    in
    let g_result = List.map (fun v -> v, get_varinfo_tree v) varinfos in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    (dtree, g_result)
    
  let query ctx q =
    print_endline "query";
    
    let spawnAcc = ref [] in
    let splitAcc = ref [] in
    let sidegAcc = ref [] in
    let assignAcc = ref [] in
    
    let handle_child d path = S.query (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) q in
    let resultTree = execute_for_each_child handle_child ctx.local in
    
    let join_leaf acc leaf path =
      match leaf with
      | Some d -> Queries.Result.join acc d
      | None -> acc 
    in
    let result = MyTree.fold join_leaf (Queries.Result.bot ()) resultTree in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
    
  let assign ctx lv e =
    print_endline "assign";
    
    (* BEGIN logging *)
    (*let flags = flag_dom_from_ctx ctx in
    print_endline ("assign: " ^ lval_to_string lv ^ " = " ^ exp_to_string e ^ " (flags = " ^ FlatBoolListDomain.short 80 flags ^ ")");
    let possible_flag_values = List.filter (fun s -> FlatBoolListDomain.is_possible_value s flags) flag_states in
    print_endline ("  #possible_flag_states = " ^ string_of_int (List.length possible_flag_values));
    List.iter (fun s -> print_endline ("  " ^ flag_state_to_string s)) possible_flag_values;*)
    (* END logging *)
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child d path = S.assign (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) lv e in
    let result = D.simplify @@ execute_for_each_child handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
    
  let is_pp_var var = 
    (*is_prefix "GOBLINT_PP_VAR__" var.vname*)
    List.exists (fun x -> x = var.vname) pp_vars
  
  let get_simple_var_expr e tv =
    match e with
    | Lval (Var var, NoOffset) -> Some (var, tv)
    | UnOp (LNot, (Lval (Var var, NoOffset)), _) -> Some (var, not tv)
    | _ -> None
  
  let branch ctx e tv =
    print_endline "branch";
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child d path = S.branch (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) e tv in
    let result = D.simplify @@ execute_for_each_child handle_child ctx.local in
    
    (* If a branch on a flag variable is discovered, remove domain entries not consistent with it. *)
    let result = match get_simple_var_expr e tv with
      | Some (var, value) when is_pp_var var -> 
        let idx = Option.get @@ List.index_of var.vname pp_vars in
        print_endline ("simple variable branch: [" ^ var.vname ^ "@" ^ string_of_int idx ^ " == " ^ string_of_bool value ^ "]");
        D.restrict idx value result
      | _ -> result
    in 
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
  
  let body ctx f =
    print_endline "body";
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child d path = S.body (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) f in
    let result = D.simplify @@ execute_for_each_child handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result

  let return ctx r f =
    print_endline "return";
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child d path = S.return (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) r f in
    let result = D.simplify @@ execute_for_each_child handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result

  let intrpt ctx =
    print_endline "intrpt";
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child d path = S.intrpt (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) in
    let result = D.simplify @@ execute_for_each_child handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result

  let special ctx r f args =
    print_endline "special";
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child d path = S.special (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) r f args in
    let result = D.simplify @@ execute_for_each_child handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
  
  let enter ctx r f args =
    print_endline "enter";
    
    let str_r = Option.map_default lval_to_string "<None>" r in
    let str_f = f.vname in
    let str_args = String.concat " , " @@ List.map exp_to_string args in
    print_endline ("enter: " ^ str_r ^ " = " ^ str_f ^ "(" ^ str_args  ^ ")");
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child d path = S.enter (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) r f args in
    let result = execute_for_each_child handle_child ctx.local in
    
    let num = List.max @@ MyTree.to_some_list (fun ds path -> List.length ds) result in
    
    let treelist = MyTree.to_some_list (fun ds path -> (path, ds)) result in
    
    let get_nth n = 
      let nth = List.map (fun (path, ds) -> (path, List.nth ds n)) @@ List.filter (fun (path, ds) -> List.length ds > n) treelist in
      let nth_1 = List.map (fun (path, (ds_1, ds_2)) -> (path, ds_1)) nth in
      let nth_2 = List.map (fun (path, (ds_1, ds_2)) -> (path, ds_2)) nth in
      (D.simplify @@ D.make_from_list nth_1, D.simplify @@ D.make_from_list nth_2)
    in
    let result = List.map get_nth @@ List.of_enum (0 -- (num - 1)) in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
  
  let combine ctx r fe f args fun_d =
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (ld, fd) path = S.combine (child_ctx ld path ctx spawnAcc splitAcc sidegAcc assignAcc) r fe f args fd in
    let result = D.simplify @@ execute_for_each_child handle_child @@ D.zip_strict ctx.local fun_d in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
  
end
