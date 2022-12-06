let warnings : Error_msg.t list ref = ref []

let check_name (name_str : string Loc.tagged) (name : Name.t)
    (usage : Name_set.t) : unit =
  if CCString.prefix ~pre:"_" (Loc.content name_str) then ()
  else if Name_set.mem name usage then ()
  else
    match Loc.tag name_str with
    | None -> ()
    | Some loc ->
      warnings :=
        Error_msg.make ~typ:`Warning (Some loc)
          (Printf.sprintf "Name %s is not used" (Loc.content name_str))
        :: !warnings

let check_names (l : (string Loc.tagged * Name.t) list) usage :
  unit =
  let rec aux l =
    match l with
    | [] -> ()
    | (name_str, name) :: xs -> (
        check_name name_str name usage;
        aux xs
      )
  in
  aux l

let check_args (l : Typ.term Binding.t list) usage : unit =
  let non_cell_args =
    (List.filter (fun binding ->
         Binding.get binding <> `Cell
       ) l)
  in
  check_names
    (List.map (fun binding ->
         (Binding.name_str binding, Binding.name binding)
       ) non_cell_args)
    usage

let remove_index_ge ~(ge : int) (usage : Name_set.t) : Name_set.t =
  Name_set.filter
    (fun x -> match x with `Global _ -> true | `Local i -> i < ge)
    usage

let rec names_used_in_term (term : Tg_ast.term) : Name_set.t =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ | T_symbol _ -> Name_set.empty
    | T_name_as (x, _) -> aux x
    | T_var (_path, name, _typ) -> Name_set.(add name empty)
    | T_tuple (_, l) -> names_used_in_terms l
    | T_app (_path, name, l, _) ->
      let usage = names_used_in_terms l in
      Name_set.add name usage
    | T_unary_op (_, x) -> aux x
    | T_binary_op (_, x, y) ->
      let x = aux x in
      let y = aux y in
      Name_set.union x y
    | T_cell_pat_match (_, y) -> aux y
    | T_cell_assign (_, y) -> aux y
    | T_let { binding; next; _ } ->
      let usage_next = aux next in
      check_let_binding binding usage_next
    | T_let_macro { binding; next; _ } ->
      let usage_next = aux next in
      check_let_macro_binding binding usage_next
    | T_action { fact; temporal } ->
      let usage_fact = aux fact in
      Name_set.add (snd temporal) usage_fact
    | T_temporal_a_lt_b { a; b } | T_temporal_eq { a; b } ->
      (Name_set.empty |> Name_set.add (snd a) |> Name_set.add (snd b))
    | T_quantified { quant; formula; _ } ->
      let ge =
        match Binding.name (List.hd quant) with
        | `Global _ -> failwith "Unexpected"
        | `Local i -> i
      in
      let usage = aux formula in
      remove_index_ge ~ge usage
  in
  aux term

and names_used_in_terms (terms : Tg_ast.term list) : Name_set.t =
  let rec aux acc terms =
    match terms with
    | [] -> acc
    | x :: xs ->
      let usage = names_used_in_term x in
      aux (Name_set.union usage acc) xs
  in
  aux Name_set.empty terms

and check_let_binding (binding : Tg_ast.term Binding.t)
    (usage_next : Name_set.t) : Name_set.t =
  check_name (Binding.name_str binding) (Binding.name binding) usage_next;
  let usage_inner = names_used_in_term (Binding.get binding) in
  let ge =
    match Binding.name binding with
    | `Global _ -> failwith "Unexpected case"
    | `Local i -> i
  in
  Name_set.union (remove_index_ge ~ge usage_inner) usage_next

and check_let_macro_binding (binding : Tg_ast.macro Binding.t)
    (usage_next : Name_set.t) : Name_set.t =
  let macro = Binding.get binding in
  let usage_inner = names_used_in_term macro.body in
  check_args macro.arg_and_typs usage_inner;
  check_name (Binding.name_str binding) (Binding.name binding) usage_next;
  let ge =
    match Binding.name binding with
    | `Global _ -> failwith "Unexpected case"
    | `Local i -> i
  in
  Name_set.union (remove_index_ge ~ge usage_inner) usage_next

let check_rule_binding (binding : Tg_ast.rule_binding) (usage_next : Name_set.t)
  : Name_set.t =
  let open Tg_ast in
  match binding with
  | R_let binding -> check_let_binding binding usage_next
  | R_let_macro { binding; _ } -> check_let_macro_binding binding usage_next

let check_rule_bindings (bindings : Tg_ast.rule_binding list)
    (usage_next : Name_set.t) : Name_set.t =
  let rec aux usage_next bindings =
    match bindings with
    | [] -> usage_next
    | x :: xs ->
      let usage_next = check_rule_binding x usage_next in
      aux usage_next xs
  in
  aux usage_next (List.rev bindings)

let names_used_in_rule (rule : Tg_ast.rule) : Name_set.t =
  let open Tg_ast in
  let { l = _; vars_in_l; bindings_before_a; a; bindings_before_r; r } = rule in
  let usage_r = names_used_in_terms r in
  let usage_up_to_a = check_rule_bindings bindings_before_r usage_r in
  let usage_a = names_used_in_terms a in
  let usage_up_to_l =
    check_rule_bindings bindings_before_a (Name_set.union usage_up_to_a usage_a)
  in
  check_names
    (List.map (fun x -> (Binding.name_str x, Binding.name x)) vars_in_l)
    usage_up_to_l;
  usage_up_to_l

let names_used_in_proc (proc : Tg_ast.proc) : Name_set.t =
  let open Tg_ast in
  let rec aux usage_next proc =
    match proc with
    | P_null (* | P_goto _ *) -> usage_next
    | P_let { binding; next; _ } ->
      let usage_next = aux usage_next next in
      check_let_binding binding usage_next
    | P_let_macro { binding; next; _ } ->
      let usage_next = aux usage_next next in
      check_let_macro_binding binding usage_next
    | P_app (_path, name, l, next) ->
      let usage_next = aux usage_next next in
      let usage = names_used_in_terms l in
      Name_set.add name
        (Name_set.union usage usage_next)
    | P_line { tag = _; rule; next } ->
      let usage_next = aux usage_next next in
      let usage_rule = names_used_in_rule rule in
      Name_set.union usage_next usage_rule
    | P_branch (_loc, procs, next) ->
      let usage_next = aux usage_next next in
      aux_list usage_next Name_set.empty procs
    | P_scoped (proc, next) ->
      let usage_next = aux usage_next next in
      aux usage_next proc
    (* | P_entry_point { next; _ } -> aux usage_next next *)
    | P_while_cell_cas { term; proc; next; _ } ->
      let usage_next = aux usage_next next in
      let usage = names_used_in_term term in
      aux (Name_set.union usage usage_next) proc
  and aux_list usage_next acc procs =
    match procs with
    | [] -> acc
    | x :: xs ->
      let usage = aux usage_next x in
      aux_list usage_next (Name_set.union usage acc) xs
  in
  aux Name_set.empty proc

let names_used_in_modul (modul : Tg_ast.modul) : Name_set.t =
  let open Tg_ast in
  let rec aux acc decls =
    match decls with
    | [] -> acc
    | d :: ds ->
      let usage =
        match d with
        | D_process { binding; _ } -> names_used_in_proc (Binding.get binding)
        | D_process_macro binding ->
          let macro = Binding.get binding in
          let usage = names_used_in_proc macro.body in
          check_args macro.arg_and_typs usage;
          usage
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_open _ | D_insert _ ->
          Name_set.empty
        | D_let { binding; _ }
        | D_equation { binding; _ }
        | D_restriction { binding; _ } ->
          names_used_in_term (Binding.get binding)
        | D_macro { binding; _ } ->
          let macro = Binding.get binding in
          let usage = names_used_in_term macro.body in
          check_args macro.arg_and_typs usage;
          usage
        | D_lemma { binding; _ } ->
          names_used_in_term (Binding.get binding).formula
        | D_rule { binding; _ } -> names_used_in_rule (Binding.get binding)
        | D_modul (_, m) -> aux Name_set.empty m
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux (Name_set.union usage acc) ds
  in
  aux Name_set.empty modul

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  warnings := [];
  let _ = names_used_in_modul spec.root in
  Ok { spec with warnings = !warnings }
