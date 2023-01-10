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
    | P_app (path, name, args, next) ->
      P_app (path, name, args, aux next)
    | P_line { tag; rule; next } -> P_line { tag; rule; next = aux next }
    | P_branch (loc, procs, next) -> P_branch (loc, procs, next)
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
