let rec rewrite_term (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux (name_to_use : string option) term : Tg_ast.term =
    match term with
    | T_value x -> (
        match name_to_use with
        | None -> term
        | Some name_to_use -> (
            match Loc.content x with
            | `Str "." -> T_value (Loc.update_content (`Str name_to_use) x)
            | _ -> term
          )
      )
    | T_symbol (sym, sort) -> (
        match name_to_use with
        | None -> term
        | Some name_to_use -> (
            match Loc.content sym with
            | "." -> T_symbol (Loc.update_content name_to_use sym, sort)
            | _ -> term
          )
      )
    | T_var (path, name, typ) -> (
        match name_to_use with
        | None -> term
        | Some name_to_use -> (
            match path with
            | [ x ] -> (
                match Loc.content x with
                | "." -> T_var ([ Loc.update_content name_to_use x ], name, typ)
                | _ -> term
              )
            | _ -> term
          )
      )
    | T_tuple (loc, l) -> T_tuple (loc, List.map (aux name_to_use) l)
    | T_app { path; name; named_args; args; anno } ->
      let named_args =
        List.map (fun (name, x) ->
            (name, aux (Some name) x))
          named_args
      in
      T_app { path; name; named_args; args; anno }
    | T_unary_op (op, x) ->
      T_unary_op (op, aux name_to_use x)
    | T_binary_op (op, x, y) ->
      T_binary_op (op, aux name_to_use x, aux name_to_use y)
    | T_cell_pat_match (cell, x) ->
      T_cell_pat_match (cell, aux name_to_use x)
    | T_name_as (x, name_str) ->
      T_name_as (aux name_to_use x, name_str)
    | T_cell_assign _
    | T_let _ | T_let_macro _ | T_action _ | T_temporal_a_lt_b _
    | T_temporal_eq _ | T_quantified _ ->
      term
  in
  aux None term

and rewrite_terms l =
  List.map rewrite_term l

let rewrite_rule_binding (x : Tg_ast.rule_binding) =
  let open Tg_ast in
  match x with
  | R_let b -> R_let (Binding.map rewrite_term b)
  | R_let_macro { binding } ->
    let macro = Binding.get binding in
    R_let_macro {
      binding = Binding.update
      { macro with body = rewrite_term macro.body }
      binding
      }

let rewrite_rule (rule : Tg_ast.rule) : Tg_ast.rule =
  let open Tg_ast in
  let { l; vars_in_l; bindings_before_a; a; bindings_before_r; r } = rule in
  let l = rewrite_terms l in
  let bindings_before_a =
    List.map rewrite_rule_binding bindings_before_a
  in
  let a = rewrite_terms a in
  let bindings_before_r =
    List.map rewrite_rule_binding bindings_before_r
  in
  let r = rewrite_terms r in
  { l; vars_in_l; bindings_before_a; a; bindings_before_r; r }

let rewrite_proc (proc : Tg_ast.proc) : Tg_ast.proc =
  let open Tg_ast in
  let rec aux proc =
    match proc with
    | P_null | P_break _ | P_continue _ -> proc
    | P_let { binding; next } ->
      let next = aux next in
      P_let { binding; next }
    | P_let_macro { binding; next } ->
      let next = aux next in
      P_let_macro { binding; next }
    | P_app { path; name; named_args; args; next } ->
      let named_args =
        List.map (fun (name, x) ->
            (name, rewrite_term x))
          named_args
      in
      let next = aux next in
      P_app { path; name; named_args; args; next }
    | P_line { tag; rule; next } ->
      let rule = rewrite_rule rule in
      let next = aux next in
      P_line { tag; rule; next }
    | P_branch (loc, procs, next) ->
      let next = aux next in
      let procs = List.map aux procs in
      P_branch (loc, procs, next)
    | P_scoped (proc, next) ->
      let proc = aux proc in
      let next = aux next in
      P_scoped (proc, next)
    | P_loop { label; mode; proc; next } ->
      let proc = aux proc in
      let next = aux next in
      P_loop { label; mode; proc; next }
    | P_if_then_else { loc; cond; true_branch; false_branch; next } ->
      let true_branch = aux true_branch in
      let false_branch = aux false_branch in
      let next = aux next in
      P_if_then_else { loc; cond; true_branch; false_branch; next }
  in
  aux proc

let aux_modul (modul : Tg_ast.modul) : Tg_ast.modul =
  let open Tg_ast in
  let rec aux acc decls =
    match decls with
    | [] -> List.rev acc
    | d :: ds ->
      let d =
        match d with
        | D_process { binding } ->
          let proc = rewrite_proc (Binding.get binding) in
          D_process { binding = Binding.update proc binding }
        | D_process_macro binding ->
          let macro = Binding.get binding in
          let body = rewrite_proc macro.body in
          let macro = { macro with body } in
          D_process_macro (Binding.update macro binding)
        | D_rule { binding } ->
          let rule = rewrite_rule (Binding.get binding) in
          D_rule { binding = Binding.update rule binding }
        | D_fun _ | D_fun_exp_args _
        | D_pred _ | D_pred_exp_args _
        | D_ppred _ | D_ppred_exp_args _
        | D_apred _ | D_apred_exp_args _
        | D_papred _ | D_papred_exp_args _
        | D_let _ | D_macro _ | D_equation _
        | D_lemma _ | D_restriction _
        | D_open _ | D_include _ | D_import _ | D_modul_alias _ | D_builtins _ ->
          d
        | D_modul (name, m) ->
          let m = aux [] m in
          D_modul (name, m)
      in
      aux (d :: acc) ds
  in
  aux [] modul

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let root = aux_modul spec.root in
  Ok { spec with root }
