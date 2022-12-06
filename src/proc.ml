let sub
    ~loc
    ?(cell_subs : (string * string Loc.tagged) list = [])
    (subs : (Name.t * Tg_ast.term) list) (proc : Tg_ast.proc)
  : Tg_ast.proc =
  let open Tg_ast in
  let term_sub (x : Tg_ast.term) : Tg_ast.term =
    x
    |> Term.sub ~loc subs
    |> Term.change_cell_names_in_term cell_subs
  in
  let aux_rule_binding (binding : rule_binding) : rule_binding =
    match binding with
    | R_let binding ->
      R_let (
        Binding.map term_sub
          binding
      )
    | R_let_macro { binding } ->
      R_let_macro {
        binding =
          Binding.map (fun { arg_and_typs; ret_typ; body } ->
              { arg_and_typs;
                ret_typ;
                body = term_sub body;
              })
            binding;
      }
  in
  let rec aux proc =
    match proc with
    | P_null (* | P_goto _ *) -> proc
    | P_let { binding; next } ->
      let binding = Binding.map term_sub binding in
      P_let { binding; next = aux next }
    | P_let_macro { binding; next } ->
      let binding = Binding.map
          (fun { arg_and_typs; ret_typ; body } ->
             { arg_and_typs;
               ret_typ;
               body = term_sub body;
             })
          binding
      in
      P_let_macro {
        binding;
        next = aux next;
      }
    | P_app (path, name, l, next) ->
      P_app (path, name, List.map term_sub l, aux next)
    | P_line { tag; rule = { l; vars_in_l; bindings_before_a; a; bindings_before_r; r }; next } ->
      P_line
        { tag;
          rule = {
            l = List.map term_sub l;
            vars_in_l;
            bindings_before_a = List.map aux_rule_binding bindings_before_a;
            a = List.map term_sub a;
            bindings_before_r = List.map aux_rule_binding bindings_before_r;
            r = List.map term_sub r;
          };
          next = aux next;
        }
    | P_branch (loc, procs, next) ->
      P_branch (loc, List.map aux procs, aux next)
    | P_scoped (proc, next) ->
      P_scoped (aux proc, aux next)
    | P_while_cell_cas { cell; term; proc; next } ->
      P_while_cell_cas { cell;
                         term = term_sub term;
                         proc = aux proc;
                         next = aux next;
                       }
      (* | P_entry_point { name; next } ->
         P_entry_point { name; next = aux next } *)
  in
  aux proc

let cells_in_proc (proc : Tg_ast.proc) : String_tagged_set.t =
  let open Tg_ast in
  let aux_rule_binding (binding : rule_binding) : String_tagged_set.t =
    match binding with
    | R_let binding ->
      Term.cells_in_term (Binding.get binding)
    | R_let_macro { binding } ->
      Term.cells_in_term (Binding.get binding).body
  in
  let rec aux proc =
    match proc with
    | P_null (* | P_goto _ *) -> String_tagged_set.empty
    | P_let { binding; next } ->
      let x = Binding.get binding in
      String_tagged_set.union (Term.cells_in_term x) (aux next)
    | P_let_macro { binding; next } ->
      let ({ body; _ } : Tg_ast.macro) = Binding.get binding in
      String_tagged_set.union (Term.cells_in_term body) (aux next)
    | P_app (_path, _name, l, next) ->
      String_tagged_set.union (Term.cells_in_terms l) (aux next)
    | P_line { tag = _; rule = { l; vars_in_l = _; bindings_before_a; a; bindings_before_r; r }; next } ->
      List.fold_left String_tagged_set.union String_tagged_set.empty
        [
          Term.cells_in_terms l;
          List.map aux_rule_binding bindings_before_a
          |> List.fold_left String_tagged_set.union String_tagged_set.empty;
          Term.cells_in_terms a;
          List.map aux_rule_binding bindings_before_r
          |> List.fold_left String_tagged_set.union String_tagged_set.empty;
          Term.cells_in_terms r;
          aux next;
        ]
    | P_branch (_loc, procs, next) ->
      List.fold_left
        String_tagged_set.union String_tagged_set.empty
        (aux next :: List.map aux procs)
    | P_scoped (proc, next) ->
      String_tagged_set.union (aux proc) (aux next)
    (* | P_entry_point { name = _; next } ->
       aux next *)
    | P_while_cell_cas { cell; term; proc; next } ->
      List.map aux [ proc; next ]
      |> List.fold_left
        String_tagged_set.union
        String_tagged_set.(add cell (Term.cells_in_term term))
  in
  aux proc

let while_used_in_proc (proc : Tg_ast.proc) : bool =
  let open Tg_ast in
  let rec aux proc =
    match proc with
    | P_null -> false
    | P_let { next; _ } ->
      aux next
    | P_let_macro { next; _ } ->
      aux next
    | P_app _ ->
      failwith "Unexpected case"
    | P_line { next; _ } ->
      aux next
    | P_branch (_loc, procs, next) ->
      List.fold_left
        (||) false
        (List.map aux (next :: procs))
    | P_scoped (proc, next) ->
      aux proc || aux next
    | P_while_cell_cas _ ->
      true
  in
  aux proc
