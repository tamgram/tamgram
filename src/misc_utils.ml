let normalize_user_provided_string (s : string) =
  let rec aux (acc : char list) (l : char list) : char list =
    match l with
    | [] -> acc
    | c :: rest -> (
        match c with
        | '_' -> (
            match acc with
            | '_' :: '_' :: _acc_rest -> aux acc rest
            | _ -> aux (c :: acc) rest
          )
        | _ -> (
            aux (c :: acc) rest
          )
      )
  in
  CCString.to_list s
  |> List.map (fun c ->
      match c with
      | 'A' .. 'Z'
      | 'a' .. 'z'
      | '0' .. '9'
      | '_'
        -> c
      | _ -> '_'
    )
  |> aux []
  |> List.rev
  |> CCString.of_list

let replace_proc_end ~replace_with (proc : Tg_ast.proc) : Tg_ast.proc =
  let open Tg_ast in
  let rec aux proc =
    match proc with
    | P_null -> replace_with
    | P_break _ | P_continue _ -> proc
    | P_let { binding; next } ->
      P_let { binding; next = aux next }
    | P_let_macro { binding; next } ->
      P_let_macro { binding; next = aux next }
    | P_app { path; name; named_args; args; next } ->
      P_app { path; name; named_args; args; next = aux next }
    | P_line { tag; rule; next } -> P_line { tag; rule; next = aux next }
    | P_branch (loc, procs, next) -> P_branch (loc, procs, aux next)
    | P_scoped (proc, next) -> P_scoped (proc, aux next)
    | P_loop { label; mode; proc; next } ->
      P_loop { label; mode; proc; next = aux next }
    | P_if_then_else { loc; cond; true_branch; false_branch; next } ->
      P_if_then_else {
        loc;
        cond;
        true_branch = aux true_branch;
        false_branch = aux false_branch;
        next = aux next;
      }
  in
  aux proc

let arg_base_index_of_macro (macro : Name.t Binding.t) =
  match Binding.name macro with `Global _ -> 0 | `Local i -> i

  (*
let record_usage_of_node ~(node_id : int) (usage : Cell_lifetime.Usage.t)
    (usages : Cell_lifetime.Usage.t Int_map.t) : Cell_lifetime.Usage.t Int_map.t
  =
  match Int_map.find_opt node_id usages with
  | None -> Int_map.add node_id usage usages
  | Some usage' ->
    Int_map.add node_id (Cell_lifetime.Usage.union usage usage') usages
    *)

let reserved_prefix_check (s : string) : (unit, string) result =
  let rec aux l =
    match l with
    | [] -> Ok ()
    | pre :: xs -> if CCString.prefix ~pre s then Error pre else aux xs
  in
  aux Params.reserved_prefixes

let read_file ~path : (string, Error_msg.t) result =
  try
    Ok
      CCIO.(
        with_in path (fun ic -> read_all ic))
  with
  | Sys_error _ ->
    Error (Error_msg.make_msg_only (Printf.sprintf "Failed to open file %s" path))

let available_files_in_dir ~dir : (string String_map.t, Error_msg.t) result =
  let exception Ambiguous_modul_name of string in
  try
    Sys.readdir dir
    |> Array.to_list
    |> List.fold_left
      (fun m s ->
         let key = String.lowercase_ascii s in
         match String_map.find_opt key m with
         | None -> String_map.add key (Filename.concat dir s) m
         | Some _ -> (
             let modul_name =
               key
               |> (fun s ->
                   CCString.chop_suffix ~suf:Params.file_extension s
                   |> Option.value ~default:s
                 )
               |> String.capitalize_ascii
             in
             raise (Ambiguous_modul_name modul_name)
           ))
      String_map.empty
    |> Result.ok
  with
  | Sys_error _ ->
    Error (Error_msg.make_msg_only (Printf.sprintf "Failed to read directory %s" dir))
  | Ambiguous_modul_name name ->
    Error (Error_msg.make_msg_only (Printf.sprintf "Module name %s matches multiple files" name))
