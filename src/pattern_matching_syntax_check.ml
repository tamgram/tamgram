open Result_infix

let rec check_term_either_constant_or_wildcard (term : Tg_ast.term)
  : (unit, Error_msg.t) result =
  let open Tg_ast in
  let aux term =
    match term with
    | T_value _ | T_symbol _ -> Ok ()
    | T_var (path, _, _) -> (
        let msg = "Only wildcard (_) can be used as variable here" in
        match path with
        | [] -> failwith "Unexpected case"
        | [ x ] -> (
            match Loc.content x with
            | "_" -> Ok ()
            | _ -> Error (Error_msg.make (Loc.tag x) msg)
          )
        | _ -> Error (Error_msg.make (Path.loc path) msg)
      )
    | T_tuple (_, l) -> check_terms_either_constant_or_wildcard l
    | T_app (_, _, l, _) -> check_terms_either_constant_or_wildcard l
    | _ -> Error (Error_msg.make (Term.loc term) "Only constants, wildcards, cells, tuples, and function applications can be used here")
  in
  aux term

and check_terms_either_constant_or_wildcard terms : (unit, Error_msg.t) result =
  let rec aux terms =
    match terms with
    | [] -> Ok ()
    | x :: xs ->
      let* () = check_term_either_constant_or_wildcard x in
      aux xs
  in
  aux terms

let rec check_term ~allow_path_to_var ~(allow_let_binding : bool)
    ~(allow_cell_pat_match : bool) ~(allow_name_as : bool) (term : Tg_ast.term)
  : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux ~allow_let_binding ~allow_cell_pat_match ~allow_name_as term =
    match term with
    | T_value _ | T_symbol _ -> Ok ()
    | T_var (path, _, _) -> (
        match path with
        | [] -> failwith "Unexpected case"
        | [ _ ] -> Ok ()
        | _ ->
          if allow_path_to_var then Ok ()
          else
            Error
              (Error_msg.make
                 (Loc.tag (List.hd path))
                 "Path not expected here"
              )
      )
    | T_cell_assign (_, x) ->
      aux ~allow_let_binding ~allow_cell_pat_match:false ~allow_name_as:false
        x
    | T_cell_pat_match (cell, x) ->
      if allow_cell_pat_match then
        aux ~allow_let_binding ~allow_cell_pat_match:false ~allow_name_as:true
          x
      else
        Error
          (Error_msg.make
             (Loc.tag cell)
             "Cell pattern matching via \"cas\" not allowed here"
          )
    | T_name_as (x, _) ->
      if allow_name_as then
        aux ~allow_let_binding ~allow_cell_pat_match:false ~allow_name_as:true
          x
      else
        Error
          (Error_msg.make
             (Term.loc x)
             "Naming term via \"as\" not allowed here")
    | T_unary_op (_, x) ->
      aux ~allow_let_binding ~allow_cell_pat_match ~allow_name_as x
    | T_binary_op (_, x, y) ->
      let* () =
        aux ~allow_let_binding ~allow_cell_pat_match ~allow_name_as x
      in
      aux ~allow_let_binding ~allow_cell_pat_match ~allow_name_as y
    | T_tuple (_, l) ->
      check_terms ~allow_path_to_var ~allow_let_binding ~allow_cell_pat_match
        ~allow_name_as l
    | T_app (_, _, args, _) ->
      check_terms ~allow_path_to_var ~allow_let_binding ~allow_cell_pat_match
        ~allow_name_as args
    | T_let { binding; next; _ } ->
      if allow_let_binding then
        let* () =
          aux ~allow_let_binding ~allow_cell_pat_match:false
            ~allow_name_as:false (Binding.get binding)
        in
        aux ~allow_let_binding ~allow_cell_pat_match ~allow_name_as next
      else
        Error
          (Error_msg.make (Loc.tag (Binding.name_str binding))
             "Let binding not allowed here")
    | T_let_macro { binding; next; _ } ->
      if allow_let_binding then
        let* () =
          aux ~allow_let_binding ~allow_cell_pat_match:false
            ~allow_name_as:false (Binding.get binding).body
        in
        aux ~allow_let_binding ~allow_cell_pat_match ~allow_name_as next
      else
        Error
          (Error_msg.make
             (Loc.tag (Binding.name_str binding))
             "Let binding not allowed here")
    | T_action { fact; _ } ->
      aux ~allow_let_binding ~allow_cell_pat_match:false ~allow_name_as:false
        fact
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> Ok ()
    | T_quantified { formula; _ } ->
      aux ~allow_let_binding ~allow_cell_pat_match:false ~allow_name_as:false
        formula
  in
  aux ~allow_let_binding ~allow_cell_pat_match ~allow_name_as term

and check_terms ~allow_path_to_var ~allow_let_binding ~allow_cell_pat_match
    ~allow_name_as terms =
  let rec aux terms =
    match terms with
    | [] -> Ok ()
    | x :: xs ->
      let* () =
        check_term ~allow_path_to_var ~allow_let_binding ~allow_cell_pat_match
          ~allow_name_as x
      in
      aux xs
  in
  aux terms

let check_for_inconsistent_typ_annotations
    (m1 : Typ.term option String_tagged_map.t)
    (m2 : Typ.term option String_tagged_map.t) :
  (Typ.term option String_tagged_map.t, Error_msg.t) result =
  let inconsistency =
    String_tagged_map.merge
      (fun _k x1 x2 ->
         match (x1, x2) with
         | Some x1, Some x2 -> if x1 = x2 then None else Some (x1, x2)
         | _, _ -> None)
      m1 m2
  in
  let default () =
    Ok (String_tagged_map.union (fun _ _ x -> Some x) m1 m2)
  in
  match String_tagged_map.min_binding_opt inconsistency with
  | None -> default ()
  | Some (name_str, (x1, x2)) ->
    if Loc.content name_str = "_" then
      default ()
    else (
      let x1_str =
        match x1 with
        | None -> "unannotated"
        | Some x -> Fmt.str "%a" Printers.pp_typ x
      in
      let x2_str =
        match x2 with
        | None -> "unannotated"
        | Some x -> Fmt.str "%a" Printers.pp_typ x
      in
      Error
        (Error_msg.make
           (Loc.tag name_str)
           (Fmt.str "inconsistent type annotations (%s and %s) for name %s"
              x1_str x2_str (Loc.content name_str)))
    )

let rec check_typ_annotations_of_term (term : Tg_ast.term) :
  (Typ.term option String_tagged_map.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ | T_symbol _ -> Ok String_tagged_map.empty
    | T_var (path, _, typ) -> (
        match path with
        | [ x ] -> Ok String_tagged_map.(add x typ empty)
        | _ -> failwith "Unexpected case")
    | T_tuple (_, l) -> check_typ_annotations_of_terms l
    | T_app (_, _, args, _) -> check_typ_annotations_of_terms args
    | T_unary_op (_, x) -> aux x
    | T_binary_op (_, x, y) ->
      let* x = aux x in
      let* y = aux y in
      check_for_inconsistent_typ_annotations x y
    | T_cell_pat_match (_, x) -> aux x
    | T_cell_assign (_, x) -> aux x
    | T_name_as (x, _) -> aux x
    | T_let _ | T_let_macro _ -> failwith "Unexpected case"
    | T_action { fact; _ } -> aux fact
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> Ok String_tagged_map.empty
    | T_quantified { formula; _ } -> aux formula
  in
  aux term

and check_typ_annotations_of_terms (terms : Tg_ast.term list) :
  (Typ.term option String_tagged_map.t, Error_msg.t) result =
  let rec aux acc terms =
    match terms with
    | [] -> Ok acc
    | x :: xs ->
      let* m = check_typ_annotations_of_term x in
      let* acc = check_for_inconsistent_typ_annotations acc m in
      aux acc xs
  in
  aux String_tagged_map.empty terms

let check_rule_binding (binding : Tg_ast.rule_binding) =
  let open Tg_ast in
  match binding with
  | R_let binding ->
    check_term ~allow_path_to_var:true ~allow_let_binding:true
      ~allow_cell_pat_match:false ~allow_name_as:false (Binding.get binding)
  | R_let_macro { binding; _ } ->
    check_term ~allow_path_to_var:true ~allow_let_binding:true
      ~allow_cell_pat_match:false ~allow_name_as:false
      (Binding.get binding).body

let check_rule_bindings bindings =
  let rec aux bindings =
    match bindings with
    | [] -> Ok ()
    | x :: xs ->
      let* () = check_rule_binding x in
      aux xs
  in
  aux bindings

let check_rule (rule : Tg_ast.rule) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let { l; vars_in_l = _; bindings_before_a; a; bindings_before_r; r } = rule in
  let* () =
    check_terms ~allow_path_to_var:false ~allow_let_binding:false
      ~allow_cell_pat_match:true ~allow_name_as:true l
  in
  let* _ = check_typ_annotations_of_terms l in
  let* () = check_rule_bindings bindings_before_a in
  let* () =
    check_terms ~allow_path_to_var:true ~allow_let_binding:true
      ~allow_cell_pat_match:false ~allow_name_as:false a
  in
  let* () = check_rule_bindings bindings_before_r in
  check_terms ~allow_path_to_var:true ~allow_let_binding:true
    ~allow_cell_pat_match:false ~allow_name_as:false r

let check_proc (proc : Tg_ast.proc) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux proc =
    match proc with
    | P_null | P_break _ | P_continue _ -> Ok ()
    | P_let { binding; next; _ } ->
      let* () =
        check_term ~allow_path_to_var:true ~allow_let_binding:true
          ~allow_cell_pat_match:false ~allow_name_as:false
          (Binding.get binding)
      in
      aux next
    | P_let_macro { binding; next; _ } ->
      let* () =
        check_term ~allow_path_to_var:true ~allow_let_binding:true
          ~allow_cell_pat_match:false ~allow_name_as:false
          (Binding.get binding).body
      in
      aux next
    | P_app (_path, _name, _args, next) ->
      aux next
    | P_line { tag = _; rule; next } ->
      let* () = check_rule rule in
      aux next
    | P_branch (_loc, procs, next) ->
      let* () = aux_list procs in
      aux next
    | P_scoped (p, next) ->
      let* () = aux p in
      aux next
    | P_loop { mode; proc; next; _ } -> (
        let* () =
          match mode with
          | `While { term; _ } -> check_term_either_constant_or_wildcard term
          | `Unconditional -> Ok ()
        in
        let* () = aux proc in
        aux next
      )
  and aux_list procs =
    match procs with
    | [] -> Ok ()
    | p :: ps ->
      let* () = aux p in
      aux_list ps
  in
  aux proc

let aux_modul (decls : Tg_ast.modul) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux decls =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process { binding; _ } -> check_proc (Binding.get binding)
        | D_process_macro binding -> check_proc (Binding.get binding).body
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_open _ | D_insert _ -> Ok ()
        | D_equation { binding; _ }
        | D_restriction { binding; _ } ->
          check_term ~allow_path_to_var:false ~allow_let_binding:true
            ~allow_cell_pat_match:false ~allow_name_as:false
            (Binding.get binding)
        | D_let { binding; _ } ->
          check_term ~allow_path_to_var:true ~allow_let_binding:true
            ~allow_cell_pat_match:false ~allow_name_as:false
            (Binding.get binding)
        | D_macro { binding; _ } ->
          check_term ~allow_path_to_var:true ~allow_let_binding:true
            ~allow_cell_pat_match:false ~allow_name_as:false
            (Binding.get binding).body
        | D_lemma { binding; _ } ->
          check_term ~allow_path_to_var:false ~allow_let_binding:true
            ~allow_cell_pat_match:false ~allow_name_as:false
            (Binding.get binding).formula
        | D_rule { binding; _ } -> check_rule (Binding.get binding)
        | D_modul (_, m) -> aux m
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux ds
  in
  aux decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let+ () = aux_modul spec.root in
  spec
