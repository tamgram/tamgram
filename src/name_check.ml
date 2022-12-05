open Result_infix

let check_prefix (name : string Loc.tagged) : (unit, Error_msg.t) result =
  match Misc_utils.reserved_prefix_check (Loc.content name) with
  | Ok () -> Ok ()
  | Error pre ->
    Error
      (Error_msg.make (Loc.tag name)
         (Fmt.str "Use of reserved prefix %s is not allowed"
            pre)
      )

let check_cell (name : string Loc.tagged) : (unit, Error_msg.t) result =
  if Loc.tag name = None then Ok () else check_prefix name

let check_name ~allow_wildcard (name : string Loc.tagged) :
  (unit, Error_msg.t) result =
  if Loc.tag name = None then Ok ()
  else if Loc.content name = "_" then
    if allow_wildcard then Ok ()
    else
      Error
        (Error_msg.make
           (Loc.tag name)
           "Wildcard \"_\" not allowed here"
        )
  else if List.mem (Loc.content name) Params.reserved_names then
    Error
      (Error_msg.make
         (Loc.tag name)
         (Fmt.str "Use of reserved name %s is not allowed"
            (Loc.content name)))
  else check_prefix name

let check_names ~allow_wildcard names =
  let rec aux names =
    match names with
    | [] -> Ok ()
    | x :: xs ->
      let* () = check_name ~allow_wildcard x in
      aux xs
  in
  aux names

let check_is_capitalized ~is_capitalized (name : string Loc.tagged) : (unit, Error_msg.t) result =
  match Loc.tag name with
  | None -> Ok ()
  | Some _ ->
    let s = Loc.content name in
    let is_capitalized_already =
      String.capitalize_ascii s = s
    in
    if (is_capitalized && is_capitalized_already)
    || (not is_capitalized && not is_capitalized_already)
    then
      Ok ()
    else
      Error
        (Error_msg.make
           (Loc.tag name)
           (Fmt.str "%s should be %s"
              (Loc.content name)
              (if is_capitalized then
                 "capitalized"
               else
                 "uncapitalized"
              ))
        )

let rec check_term ~allow_wildcard (term : Tg_ast.term) : (unit, Error_msg.t) result
  =
  let open Tg_ast in
  let rec aux ~allow_wildcard term =
    match term with
    | T_symbol (x, `Cell) -> check_name ~allow_wildcard:false x
    | T_value _ | T_symbol _ -> Ok ()
    | T_name_as (x, name) ->
      let* () = check_name ~allow_wildcard:false name in
      aux ~allow_wildcard x
    | T_var _ -> Ok ()
    | T_tuple (_, l) -> check_terms ~allow_wildcard l
    | T_app (path, _, l, _) -> (
        match path with
        | [ x ] when Loc.content x = "undef" -> (
            match l with
            | [ T_symbol (name, `Cell) ] ->
              if Loc.content name = Params.pid_cell_name then
                Error
                  (Error_msg.make
                     (Loc.tag x)
                     (Fmt.str "cannot undefine reserved cell '%s"
                        Params.pid_cell_name)
                  )
              else Ok ()
            | _ -> failwith "Unexpected case")
        | _ -> check_terms ~allow_wildcard l)
    | T_unary_op (_, x) -> aux ~allow_wildcard x
    | T_binary_op (_, x, y) ->
      let* () = aux ~allow_wildcard x in
      aux ~allow_wildcard y
    | T_cell_pat_match (x, y) ->
      let* () = check_name ~allow_wildcard x in
      aux ~allow_wildcard:true y
    | T_cell_assign (x, y) ->
      let* () = check_name ~allow_wildcard:false x in
      if Loc.content x = Params.pid_cell_name then
        Error
          (Error_msg.make
             (Loc.tag x)
             (Fmt.str "cannot assign to reserved cell '%s"
                Params.pid_cell_name)
          )
      else aux ~allow_wildcard:false y
    | T_let { binding; next; _ } ->
      let* () = check_name ~allow_wildcard:true (Binding.name_str binding) in
      let* () = check_term ~allow_wildcard:false (Binding.get binding) in
      aux ~allow_wildcard next
    | T_let_macro { binding; next; _ } ->
      let* () = check_name ~allow_wildcard:false (Binding.name_str binding) in
      let { arg_and_typs; ret_typ = _; body } = Binding.get binding in
      let* () =
        check_names ~allow_wildcard:false
          (List.map Binding.name_str arg_and_typs)
      in
      let* () = aux ~allow_wildcard:false body in
      aux ~allow_wildcard next
    | T_action { fact; temporal } ->
      let* () = aux ~allow_wildcard:false fact in
      check_name ~allow_wildcard:false (fst temporal)
    | T_temporal_a_lt_b { a = a, _; b = b, _ } ->
      let* () = check_name ~allow_wildcard:false a in
      check_name ~allow_wildcard:false b
    | T_temporal_eq { a = a, _; b = b, _ } ->
      let* () = check_name ~allow_wildcard:false a in
      check_name ~allow_wildcard:false b
    | T_quantified { quant; formula; _ } ->
      let* () =
        List.fold_left
          (fun res x ->
             let* () = res in
             check_name ~allow_wildcard:false (Binding.name_str x))
          (Ok ()) quant
      in
      aux ~allow_wildcard:false formula
  in
  aux ~allow_wildcard term

and check_terms ~allow_wildcard terms =
  List.fold_left
    (fun res x ->
       let* () = res in
       check_term ~allow_wildcard x)
    (Ok ()) terms

let check_rule_bindings (bindings : Tg_ast.rule_binding list) :
  (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux bindings =
    match bindings with
    | [] -> Ok ()
    | x :: xs -> (
        match x with
        | R_let x ->
          let* () = check_name ~allow_wildcard:true (Binding.name_str x) in
          let* () = check_term ~allow_wildcard:false (Binding.get x) in
          aux xs
        | R_let_macro { binding; _ } ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          let { arg_and_typs; ret_typ = _; body } = Binding.get binding in
          let* () =
            check_names ~allow_wildcard:false
              (List.map Binding.name_str arg_and_typs)
          in
          let* () = check_term ~allow_wildcard:false body in
          aux xs)
  in
  aux bindings

let check_rule (rule : Tg_ast.rule) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let { l; vars_in_l; bindings_before_a; a; bindings_before_r; r } = rule in
  let* () = check_terms ~allow_wildcard:true l in
  let* () =
    List.fold_left
      (fun res x ->
         let* () = res in
         check_name ~allow_wildcard:true (Binding.name_str x))
      (Ok ()) vars_in_l
  in
  let* () = check_rule_bindings bindings_before_a in
  let* () = check_terms ~allow_wildcard:false a in
  let* () = check_rule_bindings bindings_before_r in
  check_terms ~allow_wildcard:false r

let check_proc (proc : Tg_ast.proc) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux proc =
    match proc with
    | P_null (* | P_goto _ *) -> Ok ()
    (* | P_entry_point { next; _ } -> aux next *)
    | P_let { binding; next; _ } ->
      let* () = check_name ~allow_wildcard:true (Binding.name_str binding) in
      let* () = check_term ~allow_wildcard:false (Binding.get binding) in
      aux next
    | P_let_macro { binding; next; _ } ->
      let* () = check_name ~allow_wildcard:false (Binding.name_str binding) in
      let { arg_and_typs; ret_typ = _; body } = Binding.get binding in
      let* () =
        check_names ~allow_wildcard:false
          (List.map Binding.name_str arg_and_typs)
      in
      let* () = check_term ~allow_wildcard:false body in
      aux next
    | P_app (_path, _name, args, next) ->
      let* () = check_terms ~allow_wildcard:false args in
      aux next
    | P_line { tag = _; rule; next } ->
      let* () = check_rule rule in
      aux next
    | P_branch (_loc, procs, next) ->
      let* () =
        CCList.fold_left
          (fun res x ->
             let* () = res in
             aux x)
          (Ok ()) procs
      in
      aux next
    | P_scoped (x, next) ->
      let* () = aux x in
      aux next
    | P_while_cell_cas { proc; next; _ } ->
      let* () = aux proc in
      aux next
  in
  aux proc

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux decls =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process { binding; _ } ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          check_proc (Binding.get binding)
        | D_process_macro binding ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          let { arg_and_typs; body } : proc_macro = Binding.get binding in
          let* () =
            check_names ~allow_wildcard:false
              (List.map Binding.name_str arg_and_typs)
          in
          check_proc body
        | D_let { binding; _ } ->
          check_name ~allow_wildcard:false (Binding.name_str binding)
        | D_fun binding ->
          check_name ~allow_wildcard:false (Binding.name_str binding)
        | D_pred binding | D_ppred binding ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          check_is_capitalized ~is_capitalized:true (Binding.name_str binding)
        | D_apred binding | D_papred binding ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          check_is_capitalized ~is_capitalized:true (Binding.name_str binding)
        | D_macro { binding; _ } ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          let { arg_and_typs; ret_typ = _; body } = Binding.get binding in
          let* () =
            check_names ~allow_wildcard:false
              (List.map Binding.name_str arg_and_typs)
          in
          check_term ~allow_wildcard:false body
        | D_lemma { binding; _ } ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          check_term ~allow_wildcard:false (Binding.get binding).formula
        | D_restriction { binding; _ } ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          check_term ~allow_wildcard:false (Binding.get binding)
        | D_equation { binding; _ } ->
          let* () =
            check_name ~allow_wildcard:false (Binding.name_str binding)
          in
          check_term ~allow_wildcard:false (Binding.get binding)
        | D_rule { binding; _ } -> check_rule (Binding.get binding)
        | D_open _ | D_insert _ -> Ok ()
        | D_modul (_, l) ->
          let* () = aux l in
          aux ds
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux ds
  in
  let+ () = aux spec.root in
  spec
