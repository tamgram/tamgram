open Result_syntax

let check_if_missing
    (builtins : Builtin_set.t)
    (req : Builtin.t)
    (pp_item : Format.formatter -> 'a -> unit)
    (item : 'a)
    (loc : Loc.t option)
  : (unit, Error_msg.t) result =
  if Builtin_set.mem req builtins then
    Ok ()
  else
    Error (
      Error_msg.make loc
        (Fmt.str "%a requires builtin %a" pp_item item Builtin.pp req)
    )

let check_results (f : 'a -> (unit, 'b) result) (l : 'a list) : (unit, 'b) result =
  let rec aux l =
    match l with
    | [] -> Ok ()
    | x :: xs ->
      let* () = f x in
      aux xs
  in
  aux l

let rec aux_term (builtins : Builtin_set.t) (x : Tg_ast.term) : (unit, Error_msg.t) result =
  let open Tg_ast in
  match x with
  | T_value _ | T_symbol _ | T_var _ ->
    Ok ()
  | T_tuple (_, l) ->
    aux_terms builtins l
  | T_app { named_args; args; _ } ->
    let* () = aux_terms builtins (List.map snd named_args) in
    aux_terms builtins args
  | T_unary_op (_op, x) ->
    aux_term builtins x
  | T_binary_op (op, x0, x1) -> (
      let loc = Term.loc x in
      let* () =
        match op with
        | `Exp ->
          check_if_missing builtins `Diffie_hellman
            Printers.pp_binary_op op
            loc
        | `Plus ->
          check_if_missing builtins `Multiset
            Printers.pp_binary_op op
            loc
        | `Xor ->
          check_if_missing builtins `Xor
            Printers.pp_binary_op op
            loc
        | _ -> Ok ()
      in
      let* () = aux_term builtins x0 in
      aux_term builtins x1
    )
  | T_cell_pat_match (_, x)
  | T_cell_assign (_, x)
  | T_name_as (x, _) -> aux_term builtins x
  | T_let { binding; next } ->
    let* () = aux_term builtins (Binding.get binding) in
    aux_term builtins next
  | T_let_macro { binding; next } ->
    let* () = aux_macro builtins (Binding.get binding) in
    aux_term builtins next
  | T_action { fact; _ } ->
    aux_term builtins fact
  | T_temporal_a_lt_b _ | T_temporal_eq _ -> Ok ()
  | T_quantified { formula; _ } ->
    aux_term builtins formula
and aux_terms builtins l =
  check_results (aux_term builtins) l

and aux_macro builtins (x : Tg_ast.macro) =
  let open Tg_ast in
  aux_term builtins x.body

let aux_rule_binding builtins (x : Tg_ast.rule_binding) =
  match x with
  | R_let binding ->
    aux_term builtins (Binding.get binding)
  | R_let_macro { binding } ->
    aux_macro builtins (Binding.get binding)

let aux_rule_bindings builtins l =
  check_results (aux_rule_binding builtins) l

let aux_rule builtins (x : Tg_ast.rule) =
  let open Tg_ast in
  let* () = aux_terms builtins x.l in
  let* () = aux_rule_bindings builtins x.bindings_before_a in
  let* () = aux_terms builtins x.a in
  let* () = aux_rule_bindings builtins x.bindings_before_r in
  let+ () = aux_terms builtins x.r in
  ()

let aux_proc (builtins : Builtin_set.t) (x : Tg_ast.proc) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux (x : Tg_ast.proc) =
    match x with
    | P_null | P_break _ | P_continue _ -> Ok ()
    | P_let { binding; next } ->
      let* () = aux_term builtins (Binding.get binding) in
      aux next
    | P_let_macro { binding; next } ->
      let* () = aux_macro builtins (Binding.get binding) in
      aux next
    | P_app { named_args; args; next } ->
      let* () = aux_terms builtins (List.map snd named_args) in
      let* () = aux_terms builtins args in
      aux next
    | P_line { tag = _; rule; next } ->
      let* () = aux_rule builtins rule in
      aux next
    | P_branch (_loc, procs, next) ->
      let* () = aux_list procs in
      aux next
    | P_scoped (proc, next) ->
      let* () = aux proc in
      aux next
    (* | P_entry_point { next; _ } ->
       aux next *)
    | P_loop { mode; proc; next; _ } ->
      let* () =
        match mode with
        | `While { term; _ } ->
          aux_term builtins term
        | `Unconditional ->
          Ok ()
      in
      let* () = aux proc in
      aux next
    | P_if_then_else { cond = { term; _ }; true_branch; false_branch; next } -> (
        let* () = aux_term builtins term in
        let* () = aux true_branch in
        let* () = aux false_branch in
        aux next
      )
  and aux_list l =
    check_results aux l
  in
  aux x

let aux_proc_macro builtins (x : Tg_ast.proc_macro) =
  aux_proc builtins x.body

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  let builtins =
    spec.builtins
    |> List.map Loc.content
    |> Builtin_set.of_list
  in
  let rec aux (decls : Tg_ast.decl list) =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_builtins _ -> Ok ()
        | D_process { binding } ->
          aux_proc builtins (Binding.get binding)
        | D_process_macro binding ->
          aux_proc_macro builtins (Binding.get binding)
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ -> Ok ()
        | D_let { binding } ->
          aux_term builtins (Binding.get binding)
        | D_macro { binding } ->
          aux_macro builtins (Binding.get binding)
        | D_equation { binding } ->
          aux_term builtins (Binding.get binding)
        | D_lemma { binding } ->
          aux_term builtins (Binding.get binding).formula
        | D_restriction { binding } ->
          aux_term builtins (Binding.get binding)
        | D_rule { binding } ->
          aux_rule builtins (Binding.get binding)
        | D_modul (_name, m) ->
          aux m
        | D_import _ | D_modul_alias _ -> Ok ()
      in
      aux ds
  in
  let+ () = aux spec.root in
  spec
