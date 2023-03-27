open Result_let

let check_term (x : Tg_ast.term) : (unit, Error_msg.t) result =
  let cells = Term.cells_in_term x in
  if String_tagged_set.is_empty cells then Ok ()
  else
    let x = String_tagged_set.min_elt cells in
    Error
      (Error_msg.make
         (Loc.tag x)
         (Fmt.str "Cannot use cells here, e.g. '%s"
            (Loc.content x))
      )

let check_terms (l : Tg_ast.term list) : (unit, Error_msg.t) result =
  let rec aux l =
    match l with
    | [] -> Ok ()
    | x :: xs ->
      let* () = check_term x in
      aux xs
  in
  aux l

let check_rule_bindings (l : Tg_ast.rule_binding list) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux l =
    match l with
    | [] -> Ok ()
    | x :: xs ->
      let* () =
        match x with
        | R_let binding -> check_term (Binding.get binding)
        | R_let_macro { binding; _ } -> check_term (Binding.get binding).body
      in
      aux xs
  in
  aux l

let check_rule
    ({ l; bindings_before_a; a; bindings_before_r; r; _ } : Tg_ast.rule) :
  (unit, Error_msg.t) result =
  let* () = check_terms l in
  let* () = check_rule_bindings bindings_before_a in
  let* () = check_terms a in
  let* () = check_rule_bindings bindings_before_r in
  let+ () = check_terms r in
  ()

let check_proc_macro (macro : Tg_ast.proc_macro) : (unit, Error_msg.t) result =
  let cells_in_args =
    macro.arg_and_typs
    |> List.filter_map (fun binding ->
        match Binding.get binding with
        | (_, `Cell) -> Some (Binding.name_str binding)
        | _ -> None
      )
    |> String_tagged_set.of_list
  in
  let cells = Proc.cells_in_proc macro.body in
  if String_tagged_set.is_empty (String_tagged_set.diff cells cells_in_args) then
    Ok ()
  else
    let x = String_tagged_set.min_elt cells in
    Error
      (Error_msg.make (Loc.tag x)
         (Fmt.str "Cannot use cells not named in arguments, e.g. '%s"
            (Loc.content x))
      )

let check_modul (decls : Tg_ast.modul) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux decls =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process _
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _
        | D_open _ | D_insert _ ->
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
