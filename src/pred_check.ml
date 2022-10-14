open Result_infix

(* let check_pred (binding : Tg_ast.pred Binding.t) : (unit, Error_msg.t) result =
   let open Tg_ast in
   let name = Binding.name_str binding in
   let { arity; options } = Binding.get binding in
   let is_local = List.mem `Local options in
   let is_global = List.mem `Global options in
   if is_local && is_global then
    Error
      (Fmt.str "%a: Cannot specify predicate to be both local and global"
         Loc.pp_loc_of_tagged name)
   else if is_global then Ok ()
   else if arity < 1 then
    Error
      (Fmt.str "%a: Local predicates must have arity >= 1" Loc.pp_loc_of_tagged
         name)
   else Ok () *)

let aux_modul (decls : Tg_ast.decl list) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux decls =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process _ | D_process_macro _ | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_let _
        | D_macro _ | D_equation _ | D_lemma _ | D_restriction _ | D_rule _
        | D_open _ | D_insert _ ->
          Ok ()
        | D_modul (_, m) -> aux m
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux ds
  in
  aux decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let+ () = aux_modul spec.root in
  spec
