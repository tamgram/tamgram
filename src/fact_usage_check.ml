open Result_infix

type field =
  [ `L
  | `A
  | `R
  ]

let check_term ~disallowed_names (field : field) (term : Tg_ast.term) :
  (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ | T_symbol _ -> Ok ()
    | T_name_as (x, _) -> aux x
    | T_var _ -> Ok ()
    | T_tuple _ -> Ok ()
    | T_app (path, _, _, _) -> (
        match path with
        | [] -> failwith "Unexpected case"
        | [ s ] ->
          if List.mem (Loc.content s) disallowed_names then
            Error
              (Error_msg.make
                 (Loc.tag s)
                 (Fmt.str
                    "Use of predicate %s is not allowed in %s field of rule"
                    (Loc.content s)
                    (match field with
                     | `L -> "premise"
                     | `A -> "action"
                     | `R -> "consequence"))
              )
          else Ok ()
        | _ -> Ok ())
    | T_unary_op (_, term) -> aux term
    | T_binary_op (_, x, y) ->
      let* () = aux x in
      aux y
    | T_cell_pat_match (_, term) -> aux term
    | T_cell_assign (_, term) -> aux term
    | T_temporal_eq _ | T_temporal_a_lt_b _ -> Ok ()
    | T_let _ | T_let_macro _ | T_action _ | T_quantified _ ->
      failwith "Unexpected case"
  in
  aux term

let check_rule (rule : Tg_ast.rule) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let { l; a; r; _ } = rule in
  let* () =
    List.fold_left
      (fun res x ->
         let* () = res in
         let+ () = check_term ~disallowed_names:[ "Out" ] `L x in
         ())
      (Ok ()) l
  in
  let* () =
    List.fold_left
      (fun res x ->
         let* () = res in
         let+ () = check_term ~disallowed_names:[ "Out"; "In"; "Fr" ] `A x in
         ())
      (Ok ()) a
  in
  let* () =
    List.fold_left
      (fun res x ->
         let* () = res in
         let+ () = check_term ~disallowed_names:[ "In"; "Fr" ] `R x in
         ())
      (Ok ()) r
  in
  Ok ()

let check_proc (proc : Tg_ast.proc) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux proc =
    match proc with
    | P_null | P_break _ | P_continue _ -> Ok ()
    | P_let _ | P_let_macro _ -> failwith "Unexpected case"
    | P_app (_, _, _, next) -> aux next
    | P_line { tag = _; rule; next } ->
      let* () = check_rule rule in
      aux next
    | P_branch (_loc, procs, next) ->
      let* () =
        List.fold_left
          (fun res p ->
             let* () = res in
             let+ () = aux p in
             ())
          (Ok ()) procs
      in
      aux next
    | P_scoped (proc, next) ->
      let* () = aux proc in
      aux next
    | P_loop { proc; next; _ } ->
      let* () = aux proc in
      aux next
    | P_if_then_else { true_branch; false_branch; next; _ } ->
      let* () = aux true_branch in
      let* () = aux false_branch in
      aux next
  in
  aux proc

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux decls =
    match decls with
    | [] -> Ok spec
    | d :: ds -> (
        match d with
        | D_process { binding; _ } ->
          let* () = check_proc (Binding.get binding) in
          aux ds
        | _ -> aux ds)
  in
  aux spec.root
