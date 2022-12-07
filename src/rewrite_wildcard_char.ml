let counter = ref 0

let get_num () : int =
  let ret = !counter in
  counter := succ ret;
  ret

let rewrite_term (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ | T_symbol _ -> term
    | T_var (path, name, typ) -> (
        match path with
        | [ x ] when Loc.content x = "_" ->
          T_var
            ( [
              Loc.update_content
                (Printf.sprintf "%s%d" Params.wildcard_var_prefix
                   (get_num ()))
                x;
            ],
              name,
              typ )
        | _ -> term)
    | T_tuple (loc, l) -> T_tuple (loc, aux_list l)
    | T_app (path, name, args, anno) -> T_app (path, name, aux_list args, anno)
    | T_unary_op (op, x) -> T_unary_op (op, aux x)
    | T_binary_op (op, x, y) -> T_binary_op (op, aux x, aux y)
    | T_cell_pat_match (cell, x) -> T_cell_pat_match (cell, aux x)
    | T_cell_assign _ -> failwith "Unexpected case"
    | T_name_as (x, name_str) -> T_name_as (aux x, name_str)
    | T_let _ | T_let_macro _ | T_action _ | T_temporal_a_lt_b _
    | T_temporal_eq _ | T_quantified _ ->
      failwith "Unexpected case"
  and aux_list terms = List.map aux terms in
  aux term

let rewrite_rule (rule : Tg_ast.rule) : Tg_ast.rule =
  let open Tg_ast in
  let l = List.map rewrite_term rule.l in
  { rule with l }

let rewrite_proc (proc : Tg_ast.proc) : Tg_ast.proc =
  let open Tg_ast in
  let rec aux proc =
    match proc with
    | P_null | P_break _ | P_continue _ -> proc
    | P_let { binding; next } ->
      P_let { binding; next = aux next }
    | P_let_macro { binding; next } ->
      P_let_macro { binding; next = aux next }
    | P_app (path, name, args, next) ->
      P_app (path, name, args, aux next)
    | P_line { tag; rule; next } ->
      P_line { tag; rule = rewrite_rule rule; next = aux next }
    | P_branch (loc, procs, next) ->
      P_branch (loc, List.map aux procs, aux next)
    | P_scoped (proc, next) -> P_scoped (aux proc, aux next)
    | P_while_cell_cas { label; mode; cell; term; proc; next } ->
      P_while_cell_cas {
        label;
        mode;
        cell;
        term = rewrite_term term;
        proc = aux proc;
        next = aux next;
      }
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
          D_process { binding = Binding.map rewrite_proc binding }
        | D_process_macro binding ->
          D_process_macro (Binding.map
                             (fun ({ arg_and_typs; body } : proc_macro) ->
                                { arg_and_typs; body = rewrite_proc body } ) binding)
        | D_rule { binding } ->
          D_rule { binding = Binding.map rewrite_rule binding }
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_let _ | D_macro _ | D_equation _
        | D_lemma _ | D_restriction _ | D_open _ | D_insert _ ->
          d
        | D_modul (name, m) -> D_modul (name, aux [] m)
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux (d :: acc) ds
  in
  aux [] modul

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  Ok { spec with root = aux_modul spec.root }
