open Result_syntax

let check_term ?(error_msg = "Cannot use cells here") (x : Tg_ast.term) : (unit, Error_msg.t) result =
  let cells = Term.cells_in_term x in
  if String_tagged_map.is_empty cells then Ok ()
  else (
    let (x, _) = String_tagged_map.choose cells in
    Error
      (Error_msg.make
         (Loc.tag x)
         (Fmt.str "%s, e.g. '%s" error_msg
            (Loc.content x))
      )
  )

let check_terms ?error_msg (l : Tg_ast.term list) : (unit, Error_msg.t) result =
  let rec aux l =
    match l with
    | [] -> Ok ()
    | x :: xs ->
      let* () = check_term ?error_msg x in
      aux xs
  in
  aux l

let check_rule_bindings ~error_msg (l : Tg_ast.rule_binding list) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux l =
    match l with
    | [] -> Ok ()
    | x :: xs ->
      let* () =
        match x with
        | R_let binding -> check_term ~error_msg (Binding.get binding)
        | R_let_macro { binding; _ } -> check_term ~error_msg (Binding.get binding).body
      in
      aux xs
  in
  aux l

let check_rule
    ({ l; bindings_before_a; a; bindings_before_r; r; _ } : Tg_ast.rule) :
  (unit, Error_msg.t) result =
  let error_msg = "Cannot use cells in singleton processes" in
  let* () = check_terms ~error_msg l in
  let* () = check_rule_bindings ~error_msg bindings_before_a in
  let* () = check_terms ~error_msg a in
  let* () = check_rule_bindings ~error_msg bindings_before_r in
  let+ () = check_terms ~error_msg r in
  ()

let check_proc_macro (macro : Tg_ast.proc_macro) : (unit, Error_msg.t) result =
  let cells_in_args =
    (macro.named_arg_and_typs @ macro.arg_and_typs)
    |> List.filter_map (fun binding ->
        match Binding.get binding with
        | (l, `Cell) -> Some (Binding.name_str binding, l)
        | _ -> None
      )
    |> String_tagged_map.of_list
  in
  let cells_in_proc = Proc.cells_in_proc macro.body in
  let rec aux s =
    match s () with
    | Seq.Nil -> Ok ()
    | Seq.Cons ((x, rw), rest) -> (
        match String_tagged_map.find_opt x cells_in_args with
        | None ->
          Error
            (Error_msg.make (Loc.tag x)
               (Fmt.str "Cannot use cells not named in arguments, e.g. '%s"
                  (Loc.content x))
            )
        | Some l -> (
            if rw = `Rw && not (List.mem `Rw l) then
              Error
                (Error_msg.make (Loc.tag x)
                   (Fmt.str "Cell '%s was not marked as rw in arguments"
                      (Loc.content x))
                )
            else (
              aux rest
            )
          )
      )
  in
  aux (String_tagged_map.to_seq cells_in_proc)

let check_modul (decls : Tg_ast.modul) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux decls =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process _
        | D_fun _ | D_fun_exp_args _
        | D_pred _ | D_pred_exp_args _
        | D_ppred _ | D_ppred_exp_args _
        | D_apred _ | D_apred_exp_args _
        | D_papred _ | D_papred_exp_args _
        | D_open _ | D_include _ | D_import _ | D_modul_alias _ ->
          Ok ()
        | D_process_macro macro ->
          check_proc_macro (Binding.get macro)
        | D_let { binding; _ }
        | D_restriction { binding; _ }
        | D_equation { binding; _ } ->
          check_term (Binding.get binding)
        | D_lemma { binding; _ } -> check_term (Binding.get binding).formula
        | D_macro { binding; _ } -> check_term (Binding.get binding).body
        | D_rule { binding; _ } -> check_rule (Binding.get binding)
        | D_modul (_, m) -> aux m
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux ds
  in
  aux decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let+ () = check_modul spec.root in
  spec
