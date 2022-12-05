open Result_infix

let check_for_overlaps_in_bindings (x1 : Tg_ast.term String_tagged_map.t)
    (x2 : Tg_ast.term String_tagged_map.t) : (unit, Error_msg.t) result =
  let overlap =
    String_tagged_map.merge
      (fun _ x1 x2 ->
         match (x1, x2) with Some _, Some x -> Some x | _, _ -> None)
      x1 x2
  in
  match String_tagged_map.min_binding_opt overlap with
  | None -> Ok ()
  | Some (name, term) ->
    Error
      (Error_msg.make (Term.loc term)
         (Fmt.str "Name %s is already used by another \"as\""
            (Loc.content name))
      )

let rec rewrite_term free_vars (term : Tg_ast.term) :
  (Tg_ast.term * Tg_ast.term String_tagged_map.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux term :
    (Tg_ast.term * Tg_ast.term String_tagged_map.t, Error_msg.t) result =
    match term with
    | T_value _ | T_symbol _ | T_var _ -> Ok (term, String_tagged_map.empty)
    | T_tuple (loc, l) ->
      let+ l, bindings = rewrite_terms free_vars l in
      (T_tuple (loc, l), bindings)
    | T_app (path, name, args, anno) ->
      let+ args, bindings = rewrite_terms free_vars args in
      (T_app (path, name, args, anno), bindings)
    | T_unary_op (op, x) ->
      let+ x, bindings = aux x in
      (T_unary_op (op, x), bindings)
    | T_binary_op (op, x, y) ->
      let* x, bindings_x = aux x in
      let* y, bindings_y = aux y in
      let+ () = check_for_overlaps_in_bindings bindings_x bindings_y in
      ( T_binary_op (op, x, y),
        String_tagged_map.union (fun _ _ x -> Some x) bindings_x bindings_y )
    | T_cell_pat_match (cell, x) ->
      let+ x, bindings = aux x in
      (T_cell_pat_match (cell, x), bindings)
    | T_cell_assign _ -> failwith "Unexpected case"
    | T_name_as (x, name_str) ->
      let* x, bindings = aux x in
      if String_tagged_set.mem name_str free_vars then
        Error
          (Error_msg.make
             (Loc.tag name_str)
             (Fmt.str "Name %s already appears as a free variable"
                (Loc.content name_str))
          )
      else Ok (x, String_tagged_map.add name_str x bindings)
    | T_let _ | T_let_macro _ | T_action _ | T_temporal_a_lt_b _
    | T_temporal_eq _ | T_quantified _ ->
      failwith "Unexpected case"
  in
  aux term

and rewrite_terms free_vars (terms : Tg_ast.term list) :
  (Tg_ast.term list * Tg_ast.term String_tagged_map.t, Error_msg.t) result =
  let rec aux acc bindings terms =
    match terms with
    | [] -> Ok (List.rev acc, bindings)
    | x :: xs ->
      let* x, bindings' = rewrite_term free_vars x in
      let* () = check_for_overlaps_in_bindings bindings bindings' in
      let bindings =
        String_tagged_map.union (fun _ _ x -> Some x) bindings bindings'
      in
      aux (x :: acc) bindings xs
  in
  aux [] String_tagged_map.empty terms

let rewrite_rule (rule : Tg_ast.rule) : (Tg_ast.rule, Error_msg.t) result =
  let open Tg_ast in
  let { l; vars_in_l; bindings_before_a; a; bindings_before_r; r } = rule in
  let+ l, bindings_from_l =
    rewrite_terms (Term.free_var_name_strs_in_terms ~ignore_name_as:true l) l
  in
  let bindings_before_a =
    String_tagged_map.fold
      (fun k v acc -> R_let (Binding.make k v) :: acc)
      bindings_from_l bindings_before_a
  in
  { l; vars_in_l; bindings_before_a; a; bindings_before_r; r }

let rewrite_proc (proc : Tg_ast.proc) : (Tg_ast.proc, Error_msg.t) result =
  let open Tg_ast in
  let rec aux proc =
    match proc with
    | P_null (* | P_goto _ *) -> Ok proc
    | P_let { binding; next } ->
      let+ next = aux next in
      P_let { binding; next }
    | P_let_macro { binding; next } ->
      let+ next = aux next in
      P_let_macro { binding; next }
    | P_app (path, name, args, next) ->
      let+ next = aux next in
      P_app (path, name, args, next)
    | P_line { tag; rule; next } ->
      let* next = aux next in
      let+ rule = rewrite_rule rule in
      P_line { tag; rule; next }
    | P_branch (loc, procs, next) ->
      let* next = aux next in
      let+ procs = aux_list [] procs in
      P_branch (loc, procs, next)
    | P_scoped (proc, next) ->
      let* proc = aux proc in
      let+ next = aux next in
      P_scoped (proc, next)
    (* | P_entry_point { name; next } ->
      let+ next = aux next in
      P_entry_point { name; next } *)
    | P_while_cell_cas { cell; term; proc; next } ->
      let* proc = aux proc in
      let+ next = aux next in
      P_while_cell_cas { cell; term; proc; next }
  and aux_list acc procs =
    match procs with
    | [] -> Ok (List.rev acc)
    | p :: ps ->
      let* p = aux p in
      aux_list (p :: acc) ps
  in
  aux proc

let aux_modul (modul : Tg_ast.modul) : (Tg_ast.modul, Error_msg.t) result =
  let open Tg_ast in
  let rec aux acc decls =
    match decls with
    | [] -> Ok (List.rev acc)
    | d :: ds ->
      let* d =
        match d with
        | D_process { binding } ->
          let+ proc = rewrite_proc (Binding.get binding) in
          D_process { binding = Binding.update proc binding }
        | D_process_macro binding ->
          let macro = Binding.get binding in
          let+ body = rewrite_proc macro.body in
          let macro = { macro with body } in
          D_process_macro (Binding.update macro binding)
        | D_rule { binding } ->
          let+ rule = rewrite_rule (Binding.get binding) in
          D_rule { binding = Binding.update rule binding }
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_let _ | D_macro _ | D_equation _
        | D_lemma _ | D_restriction _ | D_open _ | D_insert _ ->
          Ok d
        | D_modul (name, m) ->
          let+ m = aux [] m in
          D_modul (name, m)
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux (d :: acc) ds
  in
  aux [] modul

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let+ root = aux_modul spec.root in
  { spec with root }
