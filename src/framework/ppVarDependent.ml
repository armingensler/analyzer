open Prelude
open Cil
open Pretty
open Analyses
open GobConfig
open MyUtil

type varState =
  | VarState_True
  | VarState_False
  | VarState_Both

let varstate_to_string vs = 
  match vs with
    | VarState_True -> "T"
    | VarState_False -> "F"
    | VarState_Both -> "*" 
  
let varstates_to_string vs =
  String.concat "" @@ List.map varstate_to_string vs

type 'd varTree = 
  | VarTree_TF of 'd varTree * 'd varTree
  | VarTree_Both of 'd varTree
  | VarTree_Leaf of 'd option

exception PathResultSplit of int

module type CilFile = 
sig
  val file : Cil.file
end
  
module type TreeHeight = 
sig
  val height : int
end

module VarTree (H:TreeHeight)
=
struct 
  
  (* Creates a tree of given depth contzaining only of Both nodes a given leaf value. *)
  let rec make_both_tree depth leaf =
    if depth <= 0 then VarTree_Leaf leaf else VarTree_Both (make_both_tree (depth - 1) leaf)
    
  (* Creates a tree representing a single defined value .*)
  let single d = 
    make_both_tree H.height (Some d)
    
  (* Creates a tree which has a leaf value at a given path and is empty otherwise. *)
  let rec make_path_tree path leaf = 
    match path with
    | (VarState_True :: xs) -> VarTree_TF (make_path_tree xs leaf, make_both_tree (List.length xs) None)
    | (VarState_False :: xs) -> VarTree_TF (make_both_tree (List.length xs) None, make_path_tree xs leaf)
    | (VarState_Both :: xs) -> VarTree_Both (make_path_tree xs leaf)
    | [] -> VarTree_Leaf leaf
    
  (* Returns the leaf at a given path. If the path is ambiguous a PathResultSplit exception is raised. *)
  let get_or_raise tree path =
    let rec impl tree path i =
      match (tree, path) with
      | (VarTree_TF (t, f), VarState_True::xs) -> impl t xs (i + 1)
      | (VarTree_TF (t, f), VarState_False::xs) -> impl f xs (i + 1)
      | (VarTree_TF (t, f), VarState_Both::xs) -> raise (PathResultSplit i)
      | (VarTree_TF (t, f), []) -> failwith "VarTreePrintable.get with too short fs"
      | (VarTree_Both tf, x::xs) -> impl tf xs (i + 1)
      | (VarTree_Both tf, []) -> failwith "VarTreePrintable.get with too short fs"
      | (VarTree_Leaf leaf, []) -> leaf
      | (VarTree_Leaf leaf, _) -> failwith "VarTreePrintable.get with too long fs"
    in impl tree path 0
  
  (* Combines all leaves with the function f starting wittzh the value x. *)
  let fold f x tree =
    let rec impl acc tree path =
      begin match tree with
      | VarTree_TF (t, f) -> 
        let acc' = impl acc t (path @ [VarState_True]) in
        impl acc' f (path @ [VarState_False])
      | VarTree_Both tf -> impl acc tf (path @ [VarState_Both])
      | VarTree_Leaf leaf -> f acc leaf path
      end in
    impl x tree []
  
  (* Returns if a function is true for all leaf values. *)
  let for_all f tree =
    let rec impl tree path =
      begin match tree with
      | VarTree_TF (t, f) -> impl t (path @ [VarState_True]) && impl f (path @ [VarState_False])
      | VarTree_Both tf -> impl tf (path @ [VarState_Both])
      | VarTree_Leaf leaf -> f leaf path
      end in
    impl tree []
  
  (* Transforms all leaves by applying a function. *)
  let map f tree =
    let rec impl tree path =
      begin match tree with
      | VarTree_TF (t, f) -> VarTree_TF (impl t (path @ [VarState_True]), impl f (path @ [VarState_False]))
      | VarTree_Both tf -> VarTree_Both (impl tf (path @ [VarState_Both]))
      | VarTree_Leaf leaf -> VarTree_Leaf (f leaf path)
      end in
    impl tree []
  
  (* Transforms all leaves which are not NONE by applying a function. *)
  let mapSome f tree = 
    map (fun leaf path -> if Option.is_some leaf then f (Option.get leaf) path else None) tree
  
  (* Creates a list of all leaves (including NONE) transformed by some function. *)
  let to_list f tree =
    let rec impl tree path =
      begin match tree with
      | VarTree_TF (t, f) -> impl t (path @ [VarState_True]) @ impl f (path @ [VarState_False])
      | VarTree_Both tf -> impl tf (path @ [VarState_Both])
      | VarTree_Leaf leaf -> [f leaf path]
      end in
    impl tree []
  
  (* Creates a list of all non NONE leaves transformed by some function. *)
  let to_some_list f tree =
    let rec impl tree path =
      begin match tree with
      | VarTree_TF (t, f) -> impl t (path @ [VarState_True]) @ impl f (path @ [VarState_False])
      | VarTree_Both tf -> impl tf (path @ [VarState_Both])
      | VarTree_Leaf (Some leaf) -> [f leaf path]
      | VarTree_Leaf None -> []
      end in
    impl tree []
    
  (* Returns if f is true for each pair of values in both trees. *)
  let for_all_2 f xtree ytree =
    let rec impl xtree ytree path =
      match (xtree, ytree) with
      | (VarTree_TF (xt, xf), VarTree_TF (yt, yf)) -> impl xt yt (path @ [VarState_True]) && impl xf yf (path @ [VarState_False])
      | (VarTree_TF (xt, xf), VarTree_Both ytf) -> impl xt ytf (path @ [VarState_True]) && impl xf ytf (path @ [VarState_False])
      | (VarTree_Both xtf, VarTree_TF (yt, yf)) -> impl xtf yt (path @ [VarState_True]) && impl xtf yf (path @ [VarState_False])
      | (VarTree_Both xtf, VarTree_Both ytf) -> impl xtf ytf (path @ [VarState_Both])
      | (VarTree_Leaf xleaf, VarTree_Leaf yleaf) -> f xleaf yleaf path
      | (VarTree_Leaf xleaf, _) -> failwith "Called VarTree.for_all_2 with inconsistent tree height."
      | (_, VarTree_Leaf yleaf) -> failwith "Called VarTree.for_all_2 with inconsistent tree height."
    in
    impl xtree ytree []
    
  let rec zip xtree ytree =
    match (xtree, ytree) with
    | (VarTree_TF (xt, xf), VarTree_TF (yt, yf)) -> VarTree_TF (zip xt yt, zip xf yf)
    | (VarTree_TF (xt, xf), VarTree_Both ytf) -> VarTree_TF (zip xt ytf, zip xf ytf)
    | (VarTree_Both xtf, VarTree_TF (yt, yf)) -> VarTree_TF (zip xtf yt, zip xtf yf)
    | (VarTree_Both xtf, VarTree_Both ytf) -> VarTree_Both (zip xtf ytf)
    | (VarTree_Leaf (Some xleaf), VarTree_Leaf (Some yleaf)) -> VarTree_Leaf (Some (xleaf, yleaf))
    | (VarTree_Leaf (Some xleaf), VarTree_Leaf None) -> VarTree_Leaf None
    | (VarTree_Leaf None, VarTree_Leaf (Some yleaf)) -> VarTree_Leaf None
    | (VarTree_Leaf None, VarTree_Leaf None) -> VarTree_Leaf None
    | (VarTree_Leaf xleaf, _) -> failwith "Called VarTree.zip_strict with inconsistent tree height."
    | (_, VarTree_Leaf yleaf) -> failwith "Called VarTree.zip_strict with inconsistent tree height."
  
end

module VarTreePrintable (H:TreeHeight) (L:Printable.S)
= 
struct
  
  type t = L.t varTree
  
  include VarTree (H)
  
  let rec short i d = 
    match d with
    | VarTree_TF (t, f) -> "[ T -> " ^ short i t ^ ", F -> " ^ short i f ^ "]"
    | VarTree_Both tf -> "[ * -> " ^ short i tf ^ "]"
    | VarTree_Leaf (Some leaf) -> "(" ^ L.short i leaf ^ ")"
    | VarTree_Leaf None -> "NONE"
    
  let name () = "VarTreePrintable" ^ (L.name ())
  
  include Printable.PrintSimple (struct type t' = t let short = short let name = name end)
  
  let compare = Pervasives.compare
  
  let rec equal x y = 
    match (x, y) with
    | (VarTree_TF (xtrue, xfalse), VarTree_TF (ytrue, yfalse)) -> equal xtrue ytrue && equal xfalse yfalse 
    | (VarTree_Both xboth, VarTree_Both yboth) -> equal xboth yboth
    | (VarTree_Leaf (Some xleaf), VarTree_Leaf (Some yleaf)) -> L.equal xleaf yleaf
    | (VarTree_Leaf None, VarTree_Leaf None) -> true
    | _ -> false
  
  let rec hash d =
    match d with
    | VarTree_TF (t, f) -> hash t * 7 + hash f * 13 + 17
    | VarTree_Both both -> hash both * 7 + 23
    | VarTree_Leaf (Some leaf) -> L.hash leaf * 3
    | VarTree_Leaf None -> 31

  (* Simplifies the root node of the tree by merging TF nodes with identical children into a
     single Both node. *)
  let rec simplify_nonrec tree =
    match tree with
    | VarTree_TF (t, f) when equal t f -> VarTree_Both t
    | _ -> tree
    
  (* Simplifies the tree by merging TF nodes with identical children into a single Both node.
     This is done recursively to the whole tree. *)
  let rec simplify tree =
    match tree with
    | VarTree_TF (t, f) -> 
      let st = simplify t in
      let sf = simplify f in
      if equal st sf then VarTree_Both st else VarTree_TF (st, sf)
    | VarTree_Both tf -> VarTree_Both (simplify tf)
    | VarTree_Leaf leaf -> VarTree_Leaf leaf
  
  (* Sets all leaves of the tree for which the variable[pos] <> value to None. *) 
  let restrict pos value (tree : t) =
    let rec impl tree i =
      if i < pos then begin
        match tree with
        | VarTree_TF (t, f) -> simplify_nonrec @@ VarTree_TF (impl t (i + 1), impl f (i + 1))
        | VarTree_Both tf -> VarTree_Both (impl tf (i + 1))
        | VarTree_Leaf leaf -> failwith "Called VarTreePrintable.restrict with inconsistent tree height."
      end else begin
        match tree with
        | VarTree_TF (t, f) -> 
          if value 
          then simplify_nonrec @@ VarTree_TF (t, make_both_tree (H.height - pos - 1) None) 
          else simplify_nonrec @@ VarTree_TF (make_both_tree (H.height - pos - 1) None, f)
        | VarTree_Both tf -> 
          if value 
          then simplify_nonrec @@ VarTree_TF (tf, make_both_tree (H.height - pos - 1) None) 
          else simplify_nonrec @@ VarTree_TF (make_both_tree (H.height - pos - 1) None, tf)
        | VarTree_Leaf leaf -> VarTree_Leaf leaf
      end
    in
    impl tree 0
  
  (* Returns a string showing all mappings in this tree without the actual tree structure. *)
  let to_content_string tree =
    let f leaf path = 
      match leaf with
      | None -> varstates_to_string path ^ " -> NONE"
      | Some x -> varstates_to_string path ^ " -> (" ^ L.short 80 x ^ ")" 
    in
    "[" ^ (String.concat ", " @@ to_list f tree) ^ "]"
  
end

module VarTreeDom (H:TreeHeight) (L:Lattice.S)
= 
struct
  
  include VarTreePrintable (H) (L)
  include Lattice.StdCousot (* ??? *)
  
  let leq xtree ytree =
    
    (* Returns if d is <= than all leaves of ytree at path. *)
    let rec leq_than_all_at_path tree d path = 
      match tree with
      
      | VarTree_TF (t, f) ->
        begin match path with
        | VarState_True::xs -> leq_than_all_at_path t d xs
        | VarState_False::xs -> leq_than_all_at_path f d xs
        | VarState_Both::xs -> leq_than_all_at_path t d xs && leq_than_all_at_path f d xs
        | [] -> failwith "Called VarTreeDom.leq with inconsistent tree heights."
        end
        
      | VarTree_Both tf ->
        begin match path with
        | VarState_True::xs -> leq_than_all_at_path tf d xs
        | VarState_False::xs -> leq_than_all_at_path tf d xs
        | VarState_Both::xs -> leq_than_all_at_path tf d xs
        | [] -> failwith "Called VarTreeDom.leq with inconsistent tree heights."
        end        
      
      | VarTree_Leaf leaf -> 
        begin match path with
        | [] -> Option.is_some leaf && L.leq d (Option.get leaf)
        | _ -> failwith "Called VarTreeDom.leq with inconsistent tree heights."
        end
      
    in
    let f leaf path = Option.is_none leaf || leq_than_all_at_path ytree (Option.get leaf) path in
    for_all f xtree
    
  let rec join x y = 
    match (x, y) with
    | (VarTree_Leaf (Some xleaf), VarTree_Leaf (Some yleaf)) -> VarTree_Leaf (Some (L.join xleaf yleaf))
    | (VarTree_Leaf (Some xleaf), VarTree_Leaf None) -> VarTree_Leaf (Some xleaf)
    | (VarTree_Leaf None, VarTree_Leaf (Some yleaf)) -> VarTree_Leaf (Some yleaf)
    | (VarTree_Leaf None, VarTree_Leaf None) -> VarTree_Leaf None
    | (VarTree_Leaf xleaf, _) -> failwith "Called VarTreeDom.join with inconsistent tree heights."
    | (_, VarTree_Leaf yleaf) -> failwith "Called VarTreeDom.join with inconsistent tree heights."
    | (VarTree_TF (xt, xf), VarTree_TF (yt, yf)) -> simplify_nonrec @@ VarTree_TF (join xt yt, join xf yf)
    | (VarTree_TF (xt, xf), VarTree_Both ytf) -> simplify_nonrec @@ VarTree_TF (join xt ytf, join xf ytf)
    | (VarTree_Both xtf, VarTree_TF (yt, yf)) -> simplify_nonrec @@ VarTree_TF (join xtf yt, join xtf yf)
    | (VarTree_Both xtf, VarTree_Both ytf) -> VarTree_Both (join xtf ytf)
    
  let rec meet x y = 
    match (x, y) with
    | (VarTree_Leaf (Some xleaf), VarTree_Leaf (Some yleaf)) -> VarTree_Leaf (Some (L.meet xleaf yleaf))
    | (VarTree_Leaf (Some xleaf), VarTree_Leaf None) -> VarTree_Leaf None
    | (VarTree_Leaf None, VarTree_Leaf (Some yleaf)) -> VarTree_Leaf None
    | (VarTree_Leaf None, VarTree_Leaf None) -> VarTree_Leaf None    
    | (VarTree_Leaf xleaf, _) -> failwith "Called VarTreeDom.meet with inconsistent tree heights."
    | (_, VarTree_Leaf yleaf) -> failwith "Called VarTreeDom.meet with inconsistent tree heights."
    | (VarTree_TF (xt, xf), VarTree_TF (yt, yf)) -> simplify_nonrec @@ VarTree_TF (meet xt yt, meet xf yf)
    | (VarTree_TF (xt, xf), VarTree_Both ytf) -> simplify_nonrec @@ VarTree_TF (meet xt ytf, meet xf ytf)
    | (VarTree_Both xtf, VarTree_TF (yt, yf)) -> simplify_nonrec @@ VarTree_TF (meet xtf yt, meet xtf yf)
    | (VarTree_Both xtf, VarTree_Both ytf) -> VarTree_Both (meet xtf ytf)
    
  let bot () = make_both_tree H.height None
  
  let is_bot tree = for_all (fun leaf fs -> Option.is_none leaf) tree
    
  let top () = make_both_tree H.height (Some (L.top ()))
  
  let is_top tree = for_all (fun leaf fs -> Option.is_some leaf && L.is_top (Option.get leaf)) tree
  
  let rec joined_fs_path tree path =
    match (tree, path) with
    | (VarTree_TF (t, f), VarState_True::xs) -> joined_fs_path t xs
    | (VarTree_TF (t, f), VarState_False::xs) -> joined_fs_path f xs
    | (VarTree_TF (t, f), VarState_Both::xs) -> L.join (joined_fs_path t xs) (joined_fs_path f xs)
    | (VarTree_TF (t, f), []) -> failwith "VarTreePrintable.get with too short fs"
    | (VarTree_Both tf, x::xs) -> joined_fs_path tf xs
    | (VarTree_Both tf, []) -> failwith "VarTreePrintable.get with too short fs"
    | (VarTree_Leaf (Some leaf), []) -> leaf
    | (VarTree_Leaf None, []) -> L.bot ()
    | (VarTree_Leaf leaf, _) -> failwith "VarTreePrintable.get with too long fs"
    
  let make_from_list xs =
    List.fold_left join (bot ()) @@ List.map (fun (path, d) -> make_path_tree path (Some d)) xs
    
end

module PpVarDependent (F:CilFile) (S:Spec)
  : Spec with type D.t = S.D.t varTree
          and type G.t = S.G.t varTree
          and type C.t = S.C.t varTree
=
struct
  
  let pp_vars =
    let get_global_varname g = 
      match g with
      | Cil.GVarDecl (var, lov) -> [var.vname]
      | Cil.GVar (var, init, loc) -> [var.vname]
      | _ -> []
    in
    let is_pp_varname n = is_prefix "GOBLINT_PP_VAR__" n in
    List.filter is_pp_varname @@ List.flatten @@ List.map get_global_varname @@ F.file.globals
  
  module H = struct let height = List.length pp_vars end
  
  module D = VarTreeDom (H) (S.D)
  module G = VarTreeDom (H) (S.G)
  module C = VarTreePrintable (H) (S.C)
  module T = VarTree (H)

  let exp_to_string e = sprint 80 (Cil.d_exp () e)
  let lval_to_string e = sprint 80 (Cil.d_lval () e)
  
  let child_ctx child_d (path : varState list) (ctx : (D.t, G.t) Analyses.ctx) 
    (spawn_acc : (varState list * varinfo * S.D.t) list ref) 
    (split_acc : (varState list * S.D.t * exp * bool) list ref)
    (sideg_acc : (varState list * varinfo * S.G.t) list ref)
    (assign_acc : (varState list * string option * lval * exp) list ref) =
    
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

  let name = S.name^" PpVarDependent"
  
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
    
    let redundant = VarTree_TF ( 
      VarTree_Both (VarTree_TF (VarTree_Leaf None, VarTree_Leaf (Some (IntDomain.Lifted.of_int 100L)))),   
      VarTree_Both (VarTree_TF (VarTree_Leaf None, VarTree_Leaf (Some (IntDomain.Lifted.of_int 100L))))
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
    
    let t1 = T.simplify @@ VarTree_TF ( 
      VarTree_Both (VarTree_TF (VarTree_Leaf None, VarTree_Leaf None)),   
      VarTree_Both (VarTree_TF (VarTree_Leaf None, VarTree_Leaf (Some (IntDomain.Lifted.of_int 200L))))
      ) in
    print_endline ("t1 = " ^ T.to_content_string t1);
    let t2 = T.simplify @@ VarTree_TF ( 
      VarTree_Both (VarTree_TF (VarTree_Leaf None, VarTree_Leaf (Some (IntDomain.Lifted.of_int 100L)))),   
      VarTree_Both (VarTree_TF (VarTree_Leaf None, VarTree_Leaf (Some (IntDomain.Lifted.of_int 200L))))
      ) in
    print_endline ("t2 = " ^ T.to_content_string t2);
    print_endline ("t1 <= t2 = " ^ (string_of_bool @@ T.leq t1 t2));
    print_endline "";
    
    let t1 = T.simplify @@ VarTree_TF ( 
      VarTree_Both (VarTree_TF (VarTree_Leaf None, VarTree_Leaf None)),   
      VarTree_Both (VarTree_TF (VarTree_Leaf None, VarTree_Leaf (Some (IntDomain.Lifted.of_int 200L))))
      ) in
    print_endline ("t1 = " ^ T.to_content_string t1);
    let t2 = T.simplify @@ VarTree_TF ( 
      VarTree_Both (VarTree_Both (VarTree_Leaf (Some (IntDomain.Lifted.of_int 100L)))),   
      VarTree_Both (VarTree_Both (VarTree_Leaf None))
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
  
  let init () = 
    List.iter (fun n -> print_endline ("PP_VAR: " ^ n)) pp_vars;
    (*tree_test();*) 
    S.init ()
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
    
  let do_spawn ctx (xs : (varState list * varinfo * S.D.t) list) =
    let spawn_one (v : varinfo) (ds : (varState list * S.D.t) list) =
      let join_vals (path, d) = path, List.fold_left S.D.join (S.D.bot ()) d in
      let make_tree (path, d) = D.make_path_tree path (Some d) in
      let joined = List.fold_left (D.join) (D.bot ()) @@ List.map make_tree @@ List.map join_vals @@ group_assoc ds in
      ctx.spawn v joined
    in
    if not (get_bool "exp.single-threaded") then
      List.iter (uncurry spawn_one) @@ group_assoc_eq Basetype.Variables.equal @@ List.map (fun (fs, v, d) -> (v, (fs, d))) xs
  
  let do_split ctx (xs : (varState list * S.D.t * exp * bool) list) =
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
     
  let do_sideg ctx (xs : (varState list * varinfo * S.G.t) list) =
    let spawn_one v (ds : (varState list * S.G.t) list) = 
      let join_vals (path, d) = path, List.fold_left S.G.join (S.G.bot ()) d in
      let make_tree (path, d) = G.make_path_tree path (Some d) in
      let joined = List.fold_left (G.join) (G.bot ()) @@ List.map make_tree @@ List.map join_vals @@ group_assoc ds in
      ctx.sideg v joined
    in
    List.iter (uncurry spawn_one) @@ group_assoc_eq Basetype.Variables.equal @@ List.map (fun (fs, v, g) -> (v, (fs, g))) xs
    
  let do_assign ctx (xs : (varState list * string option * lval * exp) list) =
    if List.length xs > 0 then failwith "This should never be called." else ()
    
  (* Maps each non-empty tree leaf to a new leaf using the function f. 
     Automatically splits a TF node if a PathResultSplit exception is caught. *)
  let execute_for_each_child f d = 
    
    let rec impl tree path i =
      begin match tree with
      | VarTree_TF (t, f) -> 
          let rt = impl t (path @ [VarState_True]) (i + 1) in
          let rf = impl f (path @ [VarState_False]) (i + 1) in
          VarTree_TF (rt, rf)
      | VarTree_Both tf -> 
        begin 
          try VarTree_Both (impl tf (path @ [VarState_Both]) (i + 1)) 
          with PathResultSplit split_idx when split_idx = i -> impl (VarTree_TF (tf, tf)) path i
        end
      | VarTree_Leaf (Some leaf) -> VarTree_Leaf (Some (f leaf path))
      | VarTree_Leaf None -> VarTree_Leaf None
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
    let result = T.fold join_leaf (Queries.Result.bot ()) resultTree in
    
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
    
  let branch ctx e tv =
    print_endline "branch";
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child d path = S.branch (child_ctx d path ctx spawnAcc splitAcc sidegAcc assignAcc) e tv in
    let result = D.simplify @@ execute_for_each_child handle_child ctx.local in
    
    let simple_var_expr =
      match e with
      | Lval (Var var, NoOffset) -> Some (var.vname, true)
      | UnOp (LNot, (Lval (Var var, NoOffset)), _) -> Some (var.vname, false)
      | _ -> None
    in
    
    (* If a branch on a flag variable is discovered, remove domain entries not consistent with it. *)
    let result =
      match simple_var_expr with
      | None -> result
      | Some (var, negated) ->
        begin match List.index_of var pp_vars with
        | None -> result
        | Some idx ->
          print_endline ("simple variable branch: [" ^ var ^ "@" ^ string_of_int idx ^ " == " ^ string_of_bool (tv = negated) ^ "]");
          D.restrict idx (tv = negated) result
        end
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
    
    let num = List.max @@ T.to_some_list (fun ds path -> List.length ds) result in
    
    let treelist = T.to_some_list (fun ds path -> (path, ds)) result in
    
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
    let result = D.simplify @@ execute_for_each_child handle_child @@ D.zip ctx.local fun_d in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
  
end
