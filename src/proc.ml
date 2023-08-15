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
  let cond_cell_match_sub (x : Tg_ast.cond_cell_match) =
    { x with
      cell = (match List.assoc_opt (Loc.content x.cell) cell_subs with
          | None -> x.cell
          | Some c -> c);
      term = term_sub x.term
    }
  in
  let loop_mode_sub (x : Tg_ast.loop_mode) =
    match x with
    | `While x -> `While (cond_cell_match_sub x)
    | `Unconditional -> `Unconditional
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
          Binding.map (fun { named_arg_and_typs; arg_and_typs; ret_typ; body } ->
              { named_arg_and_typs;
                arg_and_typs;
                ret_typ;
                body = term_sub body;
              })
            binding;
      }
  in
  let rec aux proc =
    match proc with
    | P_null | P_break _ | P_continue _ -> proc
    | P_let { binding; next } ->
      let binding = Binding.map term_sub binding in
      P_let { binding; next = aux next }
    | P_let_macro { binding; next } ->
      let binding = Binding.map
          (fun { named_arg_and_typs; arg_and_typs; ret_typ; body } ->
             { named_arg_and_typs;
               arg_and_typs;
               ret_typ;
               body = term_sub body;
             })
          binding
      in
      P_let_macro {
        binding;
        next = aux next;
      }
    | P_app {path; name; named_args; args; next } ->
      let named_args = List.map (fun (s, x) -> (s, term_sub x)) named_args in
      let args = List.map term_sub args in
      P_app {path; name; named_args; args; next = aux next }
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
    | P_loop { label; mode; proc; next } ->
      P_loop { label;
               mode = loop_mode_sub mode;
               proc = aux proc;
               next = aux next;
             }
    | P_if_then_else { loc; cond; true_branch; false_branch; next } ->
      P_if_then_else { loc;
                       cond = cond_cell_match_sub cond;
                       true_branch = aux true_branch;
                       false_branch = aux false_branch;
                       next = aux next;
                     }
  in
  aux proc

let cells_in_proc (proc : Tg_ast.proc) : Tg_ast.rw String_tagged_map.t =
  let open Tg_ast in
  let aux_rule_binding (binding : rule_binding) : Tg_ast.rw String_tagged_map.t =
    Term.cells_in_term
      (match binding with
       | R_let binding ->
         (Binding.get binding)
       | R_let_macro { binding } ->
         (Binding.get binding).body)
  in
  let rec aux proc =
    match proc with
    | P_null | P_break _ | P_continue _ -> String_tagged_map.empty
    | P_let { binding; next } ->
      let x = Binding.get binding in
      Term.union_cell_rw (Term.cells_in_term x) (aux next)
    | P_let_macro { binding; next } ->
      let ({ body; _ } : Tg_ast.macro) = Binding.get binding in
      Term.union_cell_rw (Term.cells_in_term body) (aux next)
    | P_app { named_args; args; next; _ } ->
      Term.union_cell_rw
        (Term.union_cell_rw
           (Term.cells_in_terms (List.map snd named_args))
           (Term.cells_in_terms args)
        )
        (aux next)
    | P_line { tag = _; rule = { l; vars_in_l = _; bindings_before_a; a; bindings_before_r; r }; next } ->
      List.fold_left Term.union_cell_rw String_tagged_map.empty
        [
          Term.cells_in_terms l;
          List.map aux_rule_binding bindings_before_a
          |> List.fold_left Term.union_cell_rw
            String_tagged_map.empty;
          Term.cells_in_terms a;
          List.map aux_rule_binding bindings_before_r
          |> List.fold_left Term.union_cell_rw
            String_tagged_map.empty;
          Term.cells_in_terms r;
          aux next;
        ]
    | P_branch (_loc, procs, next) ->
      List.fold_left
        Term.union_cell_rw String_tagged_map.empty
        (aux next :: List.map aux procs)
    | P_scoped (proc, next) ->
      Term.union_cell_rw (aux proc) (aux next)
    | P_loop { label = _; mode; proc; next } -> (
        List.fold_left Term.union_cell_rw
          String_tagged_map.empty
          [ aux proc
          ; aux next
          ; (match mode with
             | `While { cell; term; _ } ->
               String_tagged_map.(add cell `R (Term.cells_in_term term))
             | `Unconditional -> String_tagged_map.empty
            )
          ]
      )
    | P_if_then_else { cond = { cell; term; _ }; true_branch; false_branch } -> (
        List.fold_left Term.union_cell_rw
          String_tagged_map.empty
          [ aux true_branch
          ; aux false_branch
          ; String_tagged_map.(add cell `R (Term.cells_in_term term))
          ]
      )
  in
  aux proc
