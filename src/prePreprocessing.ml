open Batteries
open GobConfig

type location = { loc_line: int; loc_col: int; loc_index: int }
type xchar = char * location

let loc_to_string loc =
    string_of_int loc.loc_line ^ ":" ^ string_of_int loc.loc_col ^ "(" ^ string_of_int loc.loc_index ^ ")"

let xchar_to_string (c, loc) =
    "'" ^ String.make 1 c ^ "'@[" ^ loc_to_string loc ^ "]'"

let xchars_to_string cs =
    String.concat ", " @@ List.map xchar_to_string cs
    
let xchars_to_underlying_string cs =
    String.of_list @@ List.map (fun (c,l) -> c) cs

let read_file filename =
    List.of_enum @@ Enum.map (fun line -> line ^ "\n") @@ File.lines_of filename    
    
let annotate_chars lines = 
    let process_line line row =
        let indices = List.of_enum (1 -- String.length line) in
        List.map2 (fun c col -> (c, row, col)) (String.to_list line) indices
    in
    let xyz = List.concat @@ List.map2 process_line lines (List.of_enum (1 -- List.length lines)) in
    List.map2 (fun (c, row, col) index -> (c, {loc_line = row; loc_col = col; loc_index = index})) xyz (List.of_enum (0 --^ List.length xyz))
    
let merge_continued_lines input =
    let rec impl input result = 
        match input with
        | [] -> result
        | ('\\', _) :: ('\n', _) :: rest -> impl rest result
        | c :: rest -> impl rest (c :: result)
    in
    List.rev @@ impl input []

let remove_comments input =

    let rec process_mode_normal rest acc =
        match rest with
        | [] -> acc
        | ('/',_) :: ('/',_) :: rest -> process_mode_comment_single rest acc
        | ('/',_) :: ('*',_) :: rest -> process_mode_comment_multi rest acc
        | ('\'',l) :: rest -> process_mode_char rest (('\'',l) :: acc)
        | ('\"',l) :: rest -> process_mode_string rest (('\"',l) :: acc)
        | (c,l) :: rest -> process_mode_normal rest ((c,l) :: acc)
        
    and process_mode_comment_single rest acc =
        match rest with
        | [] -> acc
        | ('\n',l) :: rest -> process_mode_normal rest (('\n',l) :: acc)
        | (_,_) :: rest -> process_mode_comment_single rest acc
        
    and process_mode_comment_multi rest acc =
        match rest with
        | [] -> acc
        | ('*',_) :: ('/',_) :: rest -> process_mode_normal rest acc
        | (_,_) :: rest -> process_mode_comment_multi rest acc
        
    and process_mode_char rest acc =
        match rest with
        | [] -> acc
        | ('\n',l) :: rest -> process_mode_normal rest (('\n',l) :: acc)
        | ('\\',l1) :: ('\'',l2) :: rest -> process_mode_char rest (('\'',l2) :: ('\\',l1) :: acc)
        | ('\'',l) :: rest -> process_mode_normal rest (('\'',l) :: acc)
        | (c,l) :: rest -> process_mode_char rest ((c,l) :: acc)
        
    and process_mode_string rest acc =
        match rest with
        | [] -> acc
        | ('\n',l) :: rest -> process_mode_normal rest (('\n',l) :: acc)
        | ('\\',l1) :: ('\"',l2) :: rest -> process_mode_string rest (('\"',l2) :: ('\\',l1) :: acc)
        | ('\"',l) :: rest -> process_mode_normal rest (('\"',l) :: acc)
        | (c,l) :: rest -> process_mode_string rest ((c,l) :: acc)

     in
     List.rev @@ process_mode_normal input []
     
let split_lines input =
    let rec impl rest line result =
        match rest with
        | [] -> result
        | ('\n',l) :: rest -> impl rest [] (List.rev line :: result)
        | c :: rest -> impl rest (c :: line) result
    in
    List.rev @@ impl input [] []
    
type line_type = 
    | LT_INCLUDE of string * location * location
    | LT_FLAG_IFDEF of string * location * location
    | LT_FLAG_IFNDEF of string * location * location
    | LT_PP_IF
    | LT_PP_ELIF
    | LT_PP_ELSE of location * location
    | LT_PP_END of location * location
    | LT_OTHER
    
let line_type_to_string typ = match typ with
    | LT_INCLUDE (path, l1, l2) -> "LT_INCLUDE[{" ^  path ^ "}@" ^ loc_to_string l1 ^ "-" ^ loc_to_string l2 ^ "]"
    | LT_FLAG_IFDEF (v, l1, l2) -> "LT_FLAG_IFDEF[" ^  v ^ "@" ^ loc_to_string l1 ^ "-" ^ loc_to_string l2 ^ "]"
    | LT_FLAG_IFNDEF (v, l1, l2) -> "LT_FLAG_IFNDEF[" ^  v ^ "@" ^ loc_to_string l1 ^ "-" ^ loc_to_string l2 ^ "]"
    | LT_PP_IF -> "LT_PP_IF"
    | LT_PP_ELIF -> "LT_PP_ELIF"
    | LT_PP_ELSE (l1, l2) -> "LT_PP_ELSE[@" ^ loc_to_string l1 ^ "-" ^ loc_to_string l2 ^ "]"
    | LT_PP_END (l1, l2) -> "LT_PP_END[@" ^ loc_to_string l1 ^ "-" ^ loc_to_string l2 ^ "]"
    | LT_OTHER -> "LT_OTHER"

let get_line_types lines pp_vars =
    
    let trim_front input =
        let rec impl rest acc =
            match rest with
            | [] -> acc
            | (c,_) :: rest when (c = ' ' || c = '\t') -> impl rest acc
            | c :: rest -> impl rest (c :: acc)
        in
        List.rev @@ impl input []
    in
    
    let starts_with input str =
        let start = List.take (String.length str) input in
        String.length str = List.length start &&  List.for_all2 (fun c1 (c2,_) -> c1 = c2) (String.to_list str) start
    in
    
    let extract_quoted input =
        let rec impl rest acc =
            match rest with
            | [] -> None
            | ('\"',_) :: _ -> Some (List.rev acc)
            | c :: rest -> impl rest (c :: acc)
        in
        if starts_with input "\"" then
            impl (List.tl input) []
        else
            None
    in
    
    let extract_pp_var line pp_vars =
        let match_var v = 
            let vlen = String.length v in
            starts_with line v && (List.length line = vlen || starts_with (List.drop vlen line) " " || starts_with (List.drop vlen line) "\t")
        in
        if List.exists match_var pp_vars then
            Some (List.find match_var pp_vars)
        else
            None
    in
    
    let get_line_type line pp_vars =
        let trimmed = trim_front line in
        if not (starts_with trimmed "#") then 
            LT_OTHER
        else
            let (_, l1) = List.hd trimmed in
            let trimmed = trim_front (List.drop 1 trimmed) in
            if starts_with trimmed "include" then
                let trimmed = trim_front (List.drop 7 trimmed) in
                match extract_quoted trimmed with
                | Some path -> 
                    let pathstr = xchars_to_underlying_string path in
                    let (_, l2) = List.at trimmed (List.length path - 1 + 2) in
                    LT_INCLUDE (pathstr, l1, l2)
                | None -> LT_OTHER
            else if starts_with trimmed "ifdef" then
                let trimmed = trim_front (List.drop 5 trimmed) in
                match extract_pp_var trimmed pp_vars with
                | Some v -> 
                    let (_, l2) = List.at trimmed (String.length v - 1) in
                    LT_FLAG_IFDEF (v, l1, l2)
                | None -> LT_PP_IF
            else if starts_with trimmed "ifndef" then
                let trimmed = trim_front (List.drop 6 trimmed) in
                match extract_pp_var trimmed pp_vars with
                | Some v ->
                    let (_, l2) = List.at trimmed (String.length v - 1) in
                    LT_FLAG_IFNDEF (v, l1, l2)
                | None -> LT_PP_IF
            else if starts_with trimmed "if" then 
                LT_PP_IF
            else if starts_with trimmed "elif" then 
                LT_PP_ELIF
            else if starts_with trimmed "else" then
                let (_, l2) = List.at trimmed 3 in
                LT_PP_ELSE (l1, l2)
            else if starts_with trimmed "endif" then
                let (_, l2) = List.at trimmed 4 in
                LT_PP_END (l1, l2)
            else
                LT_OTHER
    in
    
    List.map (fun line -> (get_line_type line pp_vars, line)) lines
    
type pp_stack_entry = SE_IF | SE_VARIF

exception InconsistentIfException 

let get_replacements unique_counter include_mappings files_to_process filepath outdir lines =
  
    let simplify_file_path (path : string) =
        
        let rec impl input result =
            match input with
            | [] -> result 
            | (x :: []) -> x :: result
            | (x :: ".." :: rest) when x <> ".." && x <> "." && x <> "" -> impl rest result
            | (x :: "." :: rest) when x <> "" -> impl (x :: rest) result
            | (x :: y :: rest) -> impl (y :: rest) (x :: result)
        in
        
        let parts = String.nsplit path "/" in
        String.concat "/" @@ List.rev @@ impl parts []
    in
  
    let get_unique_int () =
        unique_counter := !unique_counter + 1;
        !unique_counter - 1
    in
    
    let handle_include_path path =
        if get_bool "dbg.verbose" then print_endline ("  handle_include_path {" ^ path ^ "}");
        let realpath = simplify_file_path @@ Filename.concat (Filename.dirname filepath) path in
        if List.mem_assoc realpath !include_mappings then
            let mapped_path = List.assoc realpath !include_mappings in
            mapped_path
        else begin
            let unique_path = Filename.concat outdir @@ Filename.basename path ^ "_" ^ String.of_int (get_unique_int ()) in
            include_mappings := ((realpath, unique_path) :: (!include_mappings));
            files_to_process := ((realpath, unique_path) :: (!files_to_process));
            unique_path
        end
    in
  
    let rec impl rest replacements stack = 
        match rest with
        | [] -> replacements
        
        | ((LT_INCLUDE (path, l1, l2), _) :: rest) ->
            let newpath = handle_include_path path in
            let added_newlines = String.make (l2.loc_line - l1.loc_line) '\n' in
            let r = ("#include \"" ^ newpath ^ "\"" ^ added_newlines, l1.loc_index, l2.loc_index - l1.loc_index + 1) in
            impl rest (r :: replacements) stack
        
        | ((LT_FLAG_IFDEF (v, l1, l2), _) :: rest) ->
            let added_newlines = String.make (l2.loc_line - l1.loc_line) '\n' in
            let r = (" GOBLINT_PP_VAR_IF(GOBLINT_PP_VAR__" ^ v ^ ")" ^ added_newlines, l1.loc_index, l2.loc_index - l1.loc_index + 1) in
            impl rest (r :: replacements) (SE_VARIF :: stack)
            
        | ((LT_FLAG_IFNDEF (v, l1, l2), _) :: rest) ->
            let added_newlines = String.make (l2.loc_line - l1.loc_line) '\n' in
            let r = ("GOBLINT_PP_VAR_IFNOT(GOBLINT_PP_VAR__" ^ v ^ ")" ^ added_newlines, l1.loc_index, l2.loc_index - l1.loc_index + 1) in
            impl rest (r :: replacements) (SE_VARIF :: stack)
            
        | ((LT_PP_IF, line) :: rest) -> 
            impl rest replacements (SE_IF :: stack)
            
        | ((LT_PP_ELIF, line) :: rest) -> 
            begin match stack with
            | [] -> impl rest replacements []
            | (SE_IF :: _) -> impl rest replacements stack
            | (SE_VARIF :: _) -> raise InconsistentIfException
            end
            
        | ((LT_PP_ELSE (l1, l2), line) :: rest) -> 
            begin match stack with
            | [] -> impl rest replacements []
            | (SE_IF :: _) -> impl rest replacements stack
            | (SE_VARIF :: _) -> 
            let added_newlines = String.make (l2.loc_line - l1.loc_line) '\n' in
                let r = ("GOBLINT_PP_VAR_ELSE" ^ added_newlines, l1.loc_index, l2.loc_index - l1.loc_index + 1) in
                impl rest (r :: replacements) stack
            end
            
        | ((LT_PP_END (l1, l2), line) :: rest) -> 
            begin match stack with
            | [] -> impl rest replacements []
            | (SE_IF :: s) -> impl rest replacements s
            | (SE_VARIF :: s) -> 
            let added_newlines = String.make (l2.loc_line - l1.loc_line) '\n' in
                let r = ("GOBLINT_PP_VAR_ENDIF" ^ added_newlines, l1.loc_index, l2.loc_index - l1.loc_index + 1) in
                impl rest (r :: replacements) s
            end
            
        | ((LT_OTHER, line) :: rest) -> 
            impl rest replacements stack
            
    in
    List.rev @@ impl lines [] []
    
let apply_replacements input replacements =
    
    let rec impl replacement rest acc =
        let (rstr, rpos, rlen) = replacement in
        match rest with
        | [] -> acc
        | (c,l) :: rest when l.loc_index = rpos -> 
            let rest = List.drop (rlen - 1) rest in
            let insterted = List.map (fun c -> (c, {loc_line = -1; loc_col = -1; loc_index = -1})) @@ String.to_list rstr in
            impl replacement rest (List.rev insterted @ acc)
        | (c,l) :: rest -> impl replacement rest ((c,l) :: acc)
    
    in
    List.fold_left (fun acc replacement -> List.rev @@ impl replacement acc []) input replacements
    
let to_strings input =
    let chars = List.map (fun (c,_) -> c) input in
    let str = String.of_list chars in
    String.nsplit str "\n"
        
let add_file_directive lines filename =
    let fullname = 
        if Filename.is_relative filename then 
            Filename.concat (Sys.getcwd ()) filename 
        else 
            filename 
    in
    if get_bool "dbg.verbose" then print_endline ("  fullname = " ^ fullname);
    ("#line 1 \"" ^ fullname ^ "\"") :: lines
    
let write_lines file lines = 
    File.write_lines file (List.enum lines)
    
let process_file infile outfile outdir ppvars unique_counter include_mappings files_to_process =
    
    if get_bool "dbg.verbose" then print_endline "  file:";
    if get_bool "dbg.verbose" then print_endline ("    infile = " ^ infile);
    if get_bool "dbg.verbose" then print_endline ("    outfile = " ^ outfile);
    if get_bool "dbg.verbose" then List.iter (fun v -> print_endline ("  " ^ v)) ppvars;
    
    let input = read_file infile in
    let annotated = annotate_chars input in
    let continued = merge_continued_lines annotated in
    let without_comments = remove_comments continued in
    let lines = split_lines without_comments in
    let with_types = get_line_types lines ppvars in
    let replacements = get_replacements unique_counter include_mappings files_to_process infile outdir with_types in
    let replaced = apply_replacements annotated replacements in   
    let out_lines = to_strings replaced in
    let with_file_directive = add_file_directive out_lines infile in
    write_lines outfile with_file_directive;
    
    if get_bool "dbg.verbose" then print_endline "  file done."
    
let pre_preprocess infile outfile ppvars =
  
    if get_bool "dbg.verbose" then print_endline "pre_preprocess:";
    if get_bool "dbg.verbose" then print_endline "  ppvars = ";
    
    let outdir = Filename.dirname outfile in
    
    let unique_counter = ref 0 in
    let include_mappings : (string * string) list ref = ref [] in
    let files_to_process : (string * string) list ref = ref [(infile, outfile)] in
    
    if get_bool "dbg.verbose" then List.iter (fun (a,b) -> print_endline ("NEEDED: " ^ a ^ " -> " ^ b)) !files_to_process;
    
    let rec impl () =
        if List.length (!files_to_process) = 0 then () else begin
            let (infile, outfile) = List.hd !files_to_process in
            files_to_process := List.tl !files_to_process;
            process_file infile outfile outdir ppvars unique_counter include_mappings files_to_process;
            if get_bool "dbg.verbose" then List.iter (fun (a,b) -> print_endline ("NEEDED: " ^ a ^ " -> " ^ b)) !files_to_process;
            impl ()
        end
    in
    
    impl ();
        
    if get_bool "dbg.verbose" then print_endline "pre_preprocess done."
    