open Prelude
open Cil
open Pretty
open Analyses
open GobConfig
open MyUtil

let pp_vars = ["GOBLINT_PP_VAR__FLAG_A"; "GOBLINT_PP_VAR__FLAG_B"; "GOBLINT_PP_VAR__FLAG_C"]
let num_pp_vars = List.length pp_vars

let flag_states = 
  let rec make n =
    if n = 0 then [[]] else 
      let f xs = [ true :: xs; false :: xs ] in
      List.flatten @@ List.map f @@ make (n - 1)
  in
  make num_pp_vars
  
let num_flag_states = List.length flag_states

let flag_state_to_string fstate =
  let bool_to_string b = if b then "T" else "F" in 
  String.concat "" @@ List.map bool_to_string fstate

module MyPrintable (L:Printable.S)
: Printable.S with type t = (bool list * L.t) list
=
struct
  
  type t = (bool list * L.t) list
  
  let short i ds = 
    let elm_to_string (fs, d) = flag_state_to_string fs ^ " -> " ^ L.short i d in
    "[" ^ (String.concat ", " @@ List.map elm_to_string ds) ^ "]"
    
  let name () = "MyDom" ^ (L.name ())
  
  include Printable.PrintSimple (struct type t' = t let short = short let name = name end)
  
  let compare = Pervasives.compare
  
  let equal = 
    let fs_equal = List.for_all2 (fun x y -> x = y) in
    let elm_equal (fs1, d1) (fs2, d2) = fs_equal fs1 fs2 && L.equal d1 d2 in
    List.for_all2 elm_equal
  
  let hash =
    let bool_to_hash b = if b then 2 else 3 in 
    let fs_to_hash = List.fold_left (fun xs x -> xs + bool_to_hash x) 12345 in
    let elm_to_string (fs, d) = fs_to_hash fs + L.hash d * 17 in
    List.fold_left (fun xs x -> xs + elm_to_string x) 996699
  
  
end

module MyDom (L:Lattice.S)
: Lattice.S with type t = (bool list * L.t) list
=
struct  
  
  include MyPrintable (L)
  include Lattice.StdCousot
  
  let leq xs ys = 
    List.for_all (fun (fs, d) -> List.mem_assoc fs ys && L.leq d (List.assoc fs ys)) xs 
  
  (* join element-wise *)
  let join xs ys =
    let grouped = MyUtil.group_assoc (xs @ ys) in
    let join_all ds = List.fold_left L.join (L.bot ()) ds in
    List.map (fun (fs, ds) -> fs, join_all ds) grouped
    
  (* meet element-wise, only fstates in both arguments are kept *)
  let meet xs ys = 
    List.concat @@ List.map (fun (fs, x) -> if List.mem_assoc fs ys then [(fs, L.meet x (List.assoc fs ys))] else []) xs
  
  let bot () = []
  
  let is_bot d = List.length d = 0
  
  let top () = List.map (fun fs -> (fs, L.top ())) flag_states
  
  let is_top d = (List.length d = num_flag_states) && List.for_all (fun (f,x) -> x = L.top ()) d
  
end

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

module MyTreePrintable (L:Printable.S)
: Printable.S with type t = L.t myTree
= 
struct
  
  type t = L.t myTree
  
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
  
end

module MyTreeDom (L:Lattice.S)
: 
sig
  include Lattice.S with type t = L.t myTree
  val simplify : L.t myTree -> L.t myTree
  val map : (L.t option -> mySingleFlagState list -> L.t option) -> L.t myTree -> L.t myTree
  val restrict : L.t myTree -> int -> bool -> L.t myTree
  val single : L.t -> L.t myTree
  val to_content_string : L.t myTree -> string
end
= 
struct
  
  include MyTreePrintable (L)
  include Lattice.StdCousot (* ??? *)
  
  (* Returns a tree of given depth contzaining only of Both nodes a given leaf value. *)
  let rec make_both_tree depth leaf =
    if depth = 0 then MyTree_Leaf leaf else MyTree_Both (make_both_tree (depth - 1) leaf)
  
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
    
  (* Returns the leaf at a given path. *)
  let rec get tree path =
    match (tree, path) with
    | (MyTree_TF (t, f), true::xs) -> get t xs
    | (MyTree_TF (t, f), false::xs) -> get f xs
    | (MyTree_TF (t, f), []) -> failwith "MyTreeDom.get with too short fs"
    | (MyTree_Both tf, x::xs) -> get tf xs
    | (MyTree_Both tf, []) -> failwith "MyTreeDom.get with too short fs"
    | (MyTree_Leaf leaf, []) -> leaf
    | (MyTree_Leaf leaf, _) -> failwith "MyTreeDom.get with too long fs"
    
  (* Returns if all leafes specified by the path exist, i.e. are not None. *)
  let rec contains tree path =
    match (tree, path) with
    | (MyTree_TF (t, f), FS_True::xs) -> contains t xs
    | (MyTree_TF (t, f), FS_False::xs) -> contains f xs
    | (MyTree_TF (t, f), FS_Both::xs) -> contains t xs && contains f xs
    | (MyTree_TF (t, f), []) -> failwith "MyTreeDom.contains with too short fs"
    | (MyTree_Both tf, x::xs) -> contains tf xs
    | (MyTree_Both tf, []) -> failwith "MyTreeDom.contains with too short fs"
    | (MyTree_Leaf leaf, x::xs) -> failwith "MyTreeDom.contains with too long fs"
    | (MyTree_Leaf leaf, []) -> Option.is_some leaf

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
  
  (* Transforms all leaves by applying a function. *)
  let map f tree =
    let rec impl tree path =
      begin match tree with
      | MyTree_TF (t, f) -> MyTree_TF (impl t (path @ [FS_True]), impl f (path @ [FS_False]))
      | MyTree_Both tf -> MyTree_Both (impl tf (path @ [FS_Both]))
      | MyTree_Leaf leaf -> MyTree_Leaf (f leaf path)
      end in
    simplify @@ impl tree []
  
  (* Transforms all leaves by applying a function. *)
  let to_list f tree =
    let rec impl tree path =
      begin match tree with
      | MyTree_TF (t, f) -> impl t (path @ [FS_True]) @ impl f (path @ [FS_False])
      | MyTree_Both tf -> impl tf (path @ [FS_Both])
      | MyTree_Leaf leaf -> [f leaf path]
      end in
    impl tree []
  
  (* Sets all leaves of the tree for which the variable[pos] <> value to None. *) 
  let restrict tree pos value =
    let rec impl tree i =
      if i < pos then begin
        match tree with
        | MyTree_TF (t, f) -> simplify_nonrec @@ MyTree_TF (impl t (i + 1), impl f (i + 1))
        | MyTree_Both tf -> MyTree_Both (impl tf (i + 1))
        | MyTree_Leaf leaf -> failwith "Called MyTreeDom.restrict with inconsistent tree height."
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
    
  let single d = make_both_tree num_pp_vars (Some d)
    
  let bot () = make_both_tree num_pp_vars None
  
  let is_bot tree = for_all (fun leaf fs -> Option.is_none leaf) tree
    
  let top () = make_both_tree num_pp_vars (Some (L.top ()))
  
  let is_top tree = for_all (fun leaf fs -> Option.is_some leaf && L.is_top (Option.get leaf)) tree
  
  (* Returns a string showing all mappings in this tree without the actual tree structure. *)
  let to_content_string tree =
    let f leaf path = 
      match leaf with
      | None -> fs_to_string path ^ " -> NONE"
      | Some x -> fs_to_string path ^ " -> (" ^ L.short 80 x ^ ")" 
    in
    "[" ^ (String.concat ", " @@ to_list f tree) ^ "]"
  
end

module PpFlagDependent (S:Spec)
  : Spec with module D = MyDom (S.D)
          and module G = MyDom (S.G)
          and module C = MyPrintable (S.C)
=
struct
  
  module D = MyDom (S.D)
  module G = MyDom (S.G)
  module C = MyPrintable (S.C)
  
  let child_ctx fs (ctx : (D.t, G.t) Analyses.ctx) 
    (spawnAcc : (bool list * varinfo * S.D.t) list ref) 
    (splitAcc : (bool list * S.D.t * exp * bool) list ref)
    (sidegAcc : (bool list * varinfo * S.G.t) list ref)
    (assignAcc : (bool list * string option * lval * exp) list ref) =
    
    let child_dom = List.assoc fs ctx.local in
    
    let rec ask q = S.query ctx' q
    and global v = List.assoc fs @@ ctx.global v
    
    and spawn v d = spawnAcc := (fs, v, d) :: !spawnAcc
    and split d e b = splitAcc := (fs, d, e, b) :: !splitAcc
    and sideg v g = sidegAcc := (fs, v, g) :: !sidegAcc
    and assign ?name lv e = failwith "\"assign\" should not be propagated to this module becasue it is already handeled in MCP." (*assignAcc := (i, name, lv, e) :: !assignAcc*)
    
    and ctx' = { 
        ask = ask
      ; local = child_dom
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
    
  let fstates_from_ctx ctx = 
    let (fs, _) = List.split ctx.local in
    fs

  let name = S.name^" pp_flag_dependent"
  
  module T = MyTreeDom (IntDomain.Lifted)
    
  (*
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
     
    print_endline "";
    print_endline "-> tree_test.end";
    print_endline ""
  *)

  let init () = 
    (*tree_test();*)
    print_endline "-> PpFlagDependent.init";
    S.init ()
    
  let finalize () = 
    print_endline "-> PpFlagDependent.finalize";
    S.finalize ()
  
  let startstate v =
    let s = S.startstate v in
    List.map (fun fs -> fs, s) flag_states
  
  let exitstate v =
    let s = S.exitstate v in
    List.map (fun fs -> fs, s) flag_states
  
  let otherstate v =
    let s = S.otherstate v in
    List.map (fun fs -> fs, s) flag_states
  
  let morphstate v ds =
    List.map (fun (fs, d) -> fs, S.morphstate v d) ds
  
  let should_join xs ys = 
    let grouped = MyUtil.group_assoc (xs @ ys) in 
    let f (fs, ds) = begin
      match ds with
      | [x ; y] -> S.should_join x y
      | _ -> true
    end in
    List.for_all f grouped
  
  let val_of ds = List.map (fun (fs, d) -> fs, S.val_of d) ds
  let context ds = List.map (fun (fs, d) -> fs, S.context d) ds
  
  let call_descr func ds = 
    let (a,b) = List.hd ds in
    S.call_descr func b (* ??? *)
    
  let do_spawn ctx (xs : (bool list * varinfo * S.D.t) list) =
    let spawn_one (v : Cil.varinfo) (ds : (bool list * S.D.t) list) =
      let join_vals (fs, d) = fs, List.fold_left S.D.join (S.D.bot ()) d in
      ctx.spawn v @@ List.map join_vals @@ group_assoc ds
    in
    if not (get_bool "exp.single-threaded") then
      List.iter (uncurry spawn_one) @@ group_assoc_eq Basetype.Variables.equal @@ List.map (fun (fs, v, d) -> (v, (fs, d))) xs
    
  (* TODO *)
  let do_split ctx (xs : (bool list * S.D.t * exp * bool) list) =
    ()
     
  let do_sideg ctx (xs : (bool list * varinfo * S.G.t) list) =
    let spawn_one v (ds : (bool list * S.G.t) list) = 
      let join_vals (fs, d) = fs, List.fold_left S.G.join (S.G.bot ()) d in
      ctx.sideg v @@ List.map join_vals @@ group_assoc ds
    in
    List.iter (uncurry spawn_one) @@ group_assoc_eq Basetype.Variables.equal @@ List.map (fun (fs, v, g) -> (v, (fs, g))) xs
    
  let do_assign ctx (xs : (bool list * string option * lval * exp) list) =
    if List.length xs > 0 then failwith "This should never be called." else ()
    
  let sync ctx =
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (fs, d) = 
      let (d', g') = S.sync (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc) in
      ((fs, d'), (fs, g')) in
    let (ds, gs) = List.split @@ List.map handle_child ctx.local in
    let flattened = List.flatten @@ List.map (fun (fs, xs) -> List.map (fun (v, g) -> (v, (fs, g))) xs) gs in
    let grouped = group_assoc flattened in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    (ds, grouped)
    
  let query ctx q =
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (fs, d) = S.query (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc) q in
    let result = List.fold_left Queries.Result.join (Queries.Result.bot ()) @@ List.map handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
    
  let assign ctx lv e =
    
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
    
    let handle_child (fs, d) = (fs, S.assign (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc) lv e) in
    let result = List.map handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
  
  let is_pp_var var = 
    let prefix = "GOBLINT_PP_VAR__" in
    String.length var.vname > String.length prefix && String.sub var.vname 0 (String.length prefix) = prefix
  
  let get_simple_var_expr e tv =
    match e with
    | Lval (Var var, NoOffset) -> Some (var, tv)
    | UnOp (LNot, (Lval (Var var, NoOffset)), _) -> Some (var, not tv)
    | _ -> None

  let branch ctx e tv =
    
    let changed_flag = match get_simple_var_expr e tv with
      (* If a branch on a flag variable is discovered, change flag state accordingly. *)
      | Some (var, value) when List.exists (fun x -> x = var.vname) pp_vars -> 
        let idx = get_list_index var.vname pp_vars in
        print_endline ("simple variable branch: [" ^ var.vname ^ "@" ^ string_of_int idx ^ " == " ^ string_of_bool value ^ "]");
        Some (idx, value)
      (* Otherwise leave flag state unchanged. *)
      | _ -> None
    in    
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (fs, d) = 
      let dd = S.branch (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc) e tv in
      let ignore = begin 
        match changed_flag with
        | None -> false
        | Some (idx, value) -> List.nth fs idx <> value
      end in
      if ignore then [] else [(fs, dd)] in
    let result = List.flatten @@ List.map handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    result
  
  let body ctx f =
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (fs, d) = (fs, S.body (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc) f) in
    let result = List.map handle_child ctx.local in
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result

  let return ctx r f =
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (fs, d) = (fs, S.return (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc) r f) in
    let result = List.map handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result

  let intrpt ctx =
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (fs, d) = (fs, S.intrpt (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc)) in
    let result = List.map handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result

  let special ctx r f args =
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (fs, d) = (fs, S.special (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc) r f args) in
    let result = List.map handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result

  (* TODO *)
  let enter ctx r f args =
    
    let str_r = Option.map_default lval_to_string "<None>" r in
    let str_f = f.vname in
    let str_args = String.concat " , " @@ List.map exp_to_string args in
    print_endline ("enter: " ^ str_r ^ " = " ^ str_f ^ "(" ^ str_args  ^ ")");
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    (*
    let handle_child (fs, (d : S.D.t)) = 
      let rd = S.enter (child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc) r f args in
      (fs, rd) in
    let child_results = List.map handle_child ctx.local in
    
    let aa = List.map (fun (fs, ds) -> fs, (List.map (fun (a,b) -> a) ds)) child_results in
    let bb = List.map (fun (fs, ds) -> fs, (List.map (fun (a,b) -> b) ds)) child_results in
    
    let sp (fs, x) = 0 in
    let mapped = List.map sp child_results in
    *)
    
    (*
    let flags = flag_dom_from_ctx ctx in
    let child_combine i fstate = 
      if FlatBoolListDomain.is_possible_value fstate flags 
        then S.enter (conv i ctx) r f args
        else [(S.D.bot (), S.D.bot ())] (* use [] here ??? *)
    in
    let child_results = List.mapi child_combine flag_states in
    *)
    
    (*List.map (fun (x,y) -> (x, flags), (y, flags)) @@ S.enter (conv ctx) r f args*)
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    [ctx.local, ctx.local] (* dummy code !!! *)
  
  let combine ctx r fe f args fund =
    
    let spawnAcc = ref [] in 
    let splitAcc = ref [] in 
    let sidegAcc = ref [] in 
    let assignAcc = ref [] in 
    
    let handle_child (fs, d) = 
      let ctx' = child_ctx fs ctx spawnAcc splitAcc sidegAcc assignAcc in
      let child_fund = if List.mem_assoc fs fund then List.assoc fs fund else S.D.bot () in (* realy use bot here ??? *)
      (fs, S.combine ctx' r fe f args child_fund) in
    let result = List.map handle_child ctx.local in
    
    do_spawn ctx (!spawnAcc);
    do_split ctx (!splitAcc);
    do_sideg ctx (!sidegAcc);
    do_assign ctx (!assignAcc);
    
    result
  
end
