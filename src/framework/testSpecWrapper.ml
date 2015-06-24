open Prelude
open Cil
open Pretty
open Analyses
open GobConfig

let pp_vars = ["GOBLINT_PP_VAR__FLAG_A"; "GOBLINT_PP_VAR__FLAG_B"; "GOBLINT_PP_VAR__FLAG_C"]
let num_pp_vars = List.length pp_vars

let flag_values = 
  let rec make n =
    if n = 0 then [[]] else 
      let f xs = [ true :: xs; false :: xs ] in
      List.flatten @@ List.map f @@ make (n - 1)
  in
  make num_pp_vars

let flag_values_to_string fstate =
  "[" ^ (String.concat ", " @@ List.map string_of_bool fstate) ^ "]"

let exp_to_string e = sprint 80 (Cil.d_exp () e)
let lval_to_string e = sprint 80 (Cil.d_lval () e)
  
let makeUniformList n x = 
  let rec recfun i acc = if i = 0 then acc else recfun (i - 1) (x :: acc) in
  recfun n []

(* A flat lattice made out of booleans, contains just four elements: top, true, false, bottom. *)
module FlatBoolDomain =
struct
  
  include Lattice.Flat (IntDomain.Booleans) (struct let bot_name = "Inconsistent (Bottom)" let top_name = "Unknown (Top)" end)
  
  let lift b = `Lifted b
  
  let is_possible_value b d = leq (lift b) d
  
end

(* A lattice made out of boolean lists of length num_pp_vars, relations are defined element-wise. *)
module FlatBoolListDomain 
: 
sig
  include Lattice.S with type t = Lattice.Liszt (FlatBoolDomain).t
  val add_constraint : int -> bool -> t -> t
  val is_possible_value : bool list -> FlatBoolDomain.t list -> bool
end
=
struct
  
  include Lattice.Liszt (FlatBoolDomain)
  
  let bot () = makeUniformList num_pp_vars (FlatBoolDomain.bot ())
  
  let is_top = List.for_all FlatBoolDomain.is_top
  
  let top () = makeUniformList num_pp_vars (FlatBoolDomain.top ())
  
  let is_bot = List.for_all FlatBoolDomain.is_bot
  
  let add_constraint idx value d = 
    let f i v = if i = idx then FlatBoolDomain.meet (FlatBoolDomain.lift value) v else v in
    List.mapi f d
    
  let is_possible_value fstate d =
    List.for_all2 FlatBoolDomain.is_possible_value fstate d
  
end

(* This lattice contains the state of its child lattice for each flag_value. *)
(* It represents the domain state as if the according flag value were true. *)

module ListDomain (L:Lattice.S)
=
struct
  
  include Lattice.Liszt (L)
  
  let bot () = makeUniformList num_pp_vars (L.bot ())
  
  let is_top = List.for_all L.is_top
  
  let top () = makeUniformList num_pp_vars (L.top ())
  
  let is_bot = List.for_all L.is_bot
  
end

module PpFlagDependent (S:Spec)
  : Spec with module D = Lattice.Prod (ListDomain (S.D)) (FlatBoolListDomain)
          and module G = ListDomain (S.G)
          and module C = Printable.Prod (Printable.Liszt (S.C)) (FlatBoolListDomain)
=
struct
  
  module D = Lattice.Prod (ListDomain (S.D)) (FlatBoolListDomain)
  module G = ListDomain (S.G)
  module C = Printable.Prod (Printable.Liszt (S.C)) (FlatBoolListDomain)

  (* TODO! *)
  let conv i ctx =
    let (child_doms, flag_dom) = ctx.local in
    let dom = List.nth child_doms i in
    { ctx with local = dom
             ; spawn = (fun v d -> ctx.spawn v ([d], flag_dom))
             ; split = (fun d e tv -> ctx.split ([d], flag_dom) e tv )
    }
    
  let flags_from_ctx ctx = 
    let (_, flag_dom) = ctx.local in
    flag_dom

  let name = S.name^" pp_flag_dependent"

  let init () = 
    print_endline "-> PpFlagDependent.init";
    S.init ()
    
  let finalize () = 
    print_endline "-> PpFlagDependent.finalize";
    S.finalize ()
  
  let startstate v =
    let s = S.startstate v in
    (makeUniformList num_pp_vars s, FlatBoolListDomain.top ())
  
  let exitstate v =
    let s = S.exitstate v in
    (makeUniformList num_pp_vars s, FlatBoolListDomain.top ())
  
  let otherstate v =
    let s = S.otherstate v in
    (makeUniformList num_pp_vars s, FlatBoolListDomain.top ())
  
  let morphstate v (ds,f) =
    (List.map (fun d -> S.morphstate v d) ds, f) (*  use top here instead of f ??? *)

  
  let should_join (xs,_) (ys,_) = List.exists2 S.should_join xs ys (* ??? *)
  let val_of (c,f) = (List.map S.val_of c, f)
  let context (d,f) = (List.map S.context d, f)
  let call_descr func (c,f) = S.call_descr func (List.hd c) (* ??? *)
  
  let sync ctx =
    let d, diff = S.sync (conv ctx) in
    (d, flags_from_ctx ctx), diff
  
  let query ctx q =
    let flags = flags_from_ctx ctx in
    let child_query i flag_value = 
      if FlatBoolListDomain.is_possible_value flag_value flags 
        then S.query (conv i ctx) q
        else Queries.Result.bot ()
    in
    let child_results = List.mapi child_query flag_values in
    List.fold_left Queries.Result.join (Queries.Result.top ()) child_results
    
  let assign ctx lv e =
    
    let flags = flags_from_ctx ctx in
    print_endline ("assign: " ^ lval_to_string lv ^ " = " ^ exp_to_string e ^ " (flags = " ^ FlatBoolListDomain.short 80 flags ^ ")");
    let possible_flag_values = List.filter (fun s -> FlatBoolListDomain.is_possible_value s flags) flag_values in
    print_endline ("  #possible_flag_states = " ^ string_of_int (List.length possible_flag_values));
    List.iter (fun s -> print_endline ("  " ^ flag_values_to_string s)) possible_flag_values;
    
    let child_assign i flag_value = 
      if FlatBoolListDomain.is_possible_value flag_value flags 
        then S.assign (conv i ctx) lv e
        else S.D.bot ()
    in
    let child_results = List.mapi child_assign flag_values in
    
    child_results, flags
  
  (*let is_pp_var var = 
    let prefix = "GOBLINT_PP_VAR__" in
    String.length var.vname > String.length prefix && String.sub var.vname 0 (String.length prefix) = prefix*)
  
  let get_simple_var_expr e tv =
    match e with
    | Lval (Var var, NoOffset) -> Some (var, tv)
    | UnOp (LNot, (Lval (Var var, NoOffset)), _) -> Some (var, not tv)
    | _ -> None

  let get_list_index x xs =
    let (n, _) = List.find (fun (i,y) -> y = x) @@ List.mapi (fun i y -> (i,y)) xs in
    n

  let branch ctx e tv =
    print_endline ("branch: flags = " ^ FlatBoolListDomain.short 80 (flags_from_ctx ctx));
    
    let flags = flags_from_ctx ctx in
    
    let flags = 
      match get_simple_var_expr e tv with
      (* If a branch on a flag variable is discovered, change flag state accordingly. *)
      | Some (var, value) when List.exists (fun x -> x = var.vname) pp_vars -> 
        let idx = get_list_index var.vname pp_vars in
        print_endline ("simple variable branch: [" ^ var.vname ^ "@" ^ string_of_int idx ^ " == " ^ string_of_bool value ^ "]");
        FlatBoolListDomain.add_constraint idx value flags
      (* Otherwise leave flag state unchanged. *)
      | _ -> 
        flags
    in
    
    let child_branch i flag_value = 
      if FlatBoolListDomain.is_possible_value flag_value flags 
        then S.branch (conv i ctx) e tv
        else S.D.bot ()
    in
    let child_results = List.mapi child_branch flag_values in
    
    child_results, flags

  let body ctx f =
    let flags = flags_from_ctx ctx in
    let child_body i flag_value = 
      if FlatBoolListDomain.is_possible_value flag_value flags 
        then S.body (conv i ctx) f
        else S.D.bot ()
    in
    let child_results = List.mapi child_body flag_values in
    child_results, flags

  let return ctx r f =
    let flags = flags_from_ctx ctx in
    let child_return i flag_value = 
      if FlatBoolListDomain.is_possible_value flag_value flags 
        then S.return (conv i ctx) r f
        else S.D.bot ()
    in
    let child_results = List.mapi child_return flag_values in
    child_results, flags

  let intrpt ctx =
    let flags = flags_from_ctx ctx in
    let child_intrpt i flag_value = 
      if FlatBoolListDomain.is_possible_value flag_value flags 
        then S.intrpt (conv i ctx)
        else S.D.bot ()
    in
    let child_results = List.mapi child_intrpt flag_values in
    child_results, flags

  let special ctx r f args =
    let flags = flags_from_ctx ctx in
    let child_special i flag_value = 
      if FlatBoolListDomain.is_possible_value flag_value flags 
        then S.special (conv i ctx) r f args
        else S.D.bot ()
    in
    let child_results = List.mapi child_special flag_values in
    child_results, flags

  let enter ctx r f args =
    
    let str_r = Option.map_default lval_to_string "<None>" r in
    let str_f = f.vname in
    let str_args = String.concat " , " @@ List.map exp_to_string args in
    print_endline ("enter: [" ^ str_r ^ " = " ^ str_f ^ "(" ^ str_args  ^ ")] (flags = " ^ FlatBoolListDomain.short 80 (flags_from_ctx ctx) ^ ")");
    
    
    List.map (fun (x,y) -> (x, flags_from_ctx ctx), (y, flags_from_ctx ctx)) @@ S.enter (conv ctx) r f args

  (* todo: use flags of domain argument ??? *)
  let combine ctx r fe f args (es, _) =
    let flags = flags_from_ctx ctx in
    let child_combine i flag_value = 
      if FlatBoolListDomain.is_possible_value flag_value flags 
        then S.combine (conv i ctx) r fe f args (List.nth es i)
        else S.D.bot ()
    in
    let child_results = List.mapi child_combine flag_values in
    child_results, flags
  
end
