let rec reduce_term subs (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux subs term =
    match term with
    | T_value _ | T_temporal_a_lt_b _ | T_temporal_eq _ | T_symbol _ -> term
    | T_name_as (x, name) -> T_name_as (aux subs x, name)
    | T_var (path, _, _) -> Term.sub ~loc:(Path.loc path) subs term
    | T_tuple (loc, l) -> T_tuple (loc, List.map (aux subs) l)
    | T_app (path, name, args, anno) -> (
        let args = reduce_terms subs args in
        match List.assoc_opt name subs with
        | None -> T_app (path, name, args, anno)
        | Some x ->
          match x with
          | T_var (path, name, _) -> T_app (path, name, args, anno)
          | _ -> failwith "Unexpected case"
      )
    | T_unary_op (op, x) -> T_unary_op (op, aux subs x)
    | T_binary_op (op, x, y) -> T_binary_op (op, aux subs x, aux subs y)
    | T_cell_pat_match (x, y) -> T_cell_pat_match (x, aux subs y)
    | T_cell_assign (x, y) -> T_cell_assign (x, aux subs y)
    | T_let { binding; next; _ } ->
      let subs =
        (Binding.name binding, aux subs (Binding.get binding)) :: subs
      in
      aux subs next
    | T_let_macro { binding; next } ->
      T_let_macro
        {
          binding = Binding.map (reduce_macro subs) binding;
          next = aux subs next;
        }
    | T_action { fact; temporal } -> T_action { fact = aux subs fact; temporal }
    | T_quantified { loc; quantifier; quant; formula } ->
      T_quantified { loc; quantifier; quant; formula = aux subs formula }
  in
  aux subs term

and reduce_terms subs terms = List.map (reduce_term subs) terms

and reduce_macro subs ({ arg_and_typs; ret_typ; body } : Tg_ast.macro) :
  Tg_ast.macro =
  { arg_and_typs; ret_typ; body = reduce_term subs body }

let reduce_rule_bindings subs (bindings : Tg_ast.rule_binding list) :
  (Name.t * Tg_ast.term) list * Tg_ast.rule_binding list =
  let open Tg_ast in
  let rec aux subs acc bindings =
    match bindings with
    | [] -> (subs, List.rev acc)
    | x :: xs -> (
        match x with
        | R_let x ->
          let subs = (Binding.name x, reduce_term subs (Binding.get x)) :: subs in
          aux subs acc xs
        | R_let_macro { binding } ->
          let acc =
            R_let_macro
              { binding = Binding.map (reduce_macro subs) binding }
            :: acc
          in
          aux subs acc xs)
  in
  aux subs [] bindings

let reduce_rule subs (rule : Tg_ast.rule) : Tg_ast.rule =
  let open Tg_ast in
  let { l; vars_in_l; bindings_before_a; a; bindings_before_r; r } = rule in
  let subs_a, bindings_before_a = reduce_rule_bindings subs bindings_before_a in
  let subs_r, bindings_before_r =
    reduce_rule_bindings subs_a bindings_before_r
  in
  {
    l = reduce_terms subs l;
    vars_in_l;
    bindings_before_a;
    a = reduce_terms subs_a a;
    bindings_before_r;
    r = reduce_terms subs_r r;
  }

let reduce_proc subs (proc : Tg_ast.proc) : Tg_ast.proc =
  let open Tg_ast in
  let rec aux subs proc =
    match proc with
    | P_null (* | P_goto _ *) -> proc
    (* | P_entry_point { name; next } ->
      P_entry_point { name; next = aux subs next } *)
    | P_let { binding; next; _ } ->
      let subs =
        (Binding.name binding, reduce_term subs (Binding.get binding)) :: subs
      in
      aux subs next
    | P_let_macro { binding; next } ->
      P_let_macro
        {
          binding = Binding.map (reduce_macro subs) binding;
          next = aux subs next;
        }
    | P_app (path, name, l, next) ->
      P_app (path, name, reduce_terms subs l, aux subs next)
    | P_line { tag; rule; next } ->
      P_line { tag; rule = reduce_rule subs rule; next = aux subs next }
    | P_branch (loc, procs, next) ->
      P_branch (loc, List.map (aux subs) procs, aux subs next)
    | P_scoped (proc, next) ->
      Misc_utils.replace_proc_end ~replace_with:(aux subs next)
        (aux subs proc)
    | P_while_cell_cas { cell; term; proc; next } ->
      P_while_cell_cas { cell; term; proc = aux subs proc; next = aux subs next }
  in
  aux subs proc

let reduce_modul (decls : Tg_ast.modul) : Tg_ast.modul =
  let open Tg_ast in
  let rec aux subs acc decls =
    match decls with
    | [] -> (List.rev acc, subs)
    | d :: ds -> (
        match d with
        | D_process { binding } ->
          aux subs
            (D_process
               { binding = Binding.map (reduce_proc subs) binding }
             :: acc)
            ds
        | D_process_macro binding ->
          aux subs
            (D_process_macro
               ( Binding.map (fun ({ arg_and_typs; body } : proc_macro) ->
                     { arg_and_typs; body = reduce_proc subs body }) binding )
             :: acc)
            ds
        | D_let { binding; _ } ->
          let subs =
            (Binding.name binding, reduce_term subs (Binding.get binding))
            :: subs
          in
          aux subs acc ds
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_open _ | D_insert _ ->
          aux subs (d :: acc) ds
        | D_macro { binding } ->
          aux subs
            (D_macro
               { binding = Binding.map (reduce_macro subs) binding }
             :: acc)
            ds
        | D_lemma { binding } ->
          aux subs
            (D_lemma
               {
                 binding =
                   Binding.map
                     (fun lemma ->
                        { lemma with formula = reduce_term subs lemma.formula })
                     binding;
               }
             :: acc)
            ds
        | D_restriction { binding } ->
          aux subs
            (D_restriction
               { binding = Binding.map (reduce_term subs) binding }
             :: acc)
            ds
        | D_equation { binding } ->
          aux subs
            (D_equation
               { binding = Binding.map (reduce_term subs) binding }
             :: acc)
            ds
        | D_rule { binding } ->
          aux subs
            (D_rule
               { binding = Binding.map (reduce_rule subs) binding }
             :: acc)
            ds
        | D_modul (name, m) ->
          let m, subs = aux subs [] m in
          aux subs (D_modul (name, m) :: acc) ds
        | D_builtins _ -> failwith "Unexpected case"
      )
  in
  let m, _ = aux [] [] decls in
  m

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  Ok { spec with root = reduce_modul spec.root }
