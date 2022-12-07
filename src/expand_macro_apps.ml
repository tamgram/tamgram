let rec aux_term (defs : (Name.t * Tg_ast.macro) list)
    (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux (defs : (Name.t * Tg_ast.macro) list) term =
    match term with
    | T_value _ | T_symbol _ | T_temporal_a_lt_b _ | T_temporal_eq _ | T_var _
      ->
      term
    | T_name_as (x, name) -> T_name_as (aux defs x, name)
    | T_tuple (loc, l) -> T_tuple (loc, List.map (aux defs) l)
    | T_app (path, name, l, anno) -> (
        let l = List.map (aux defs) l in
        match List.assoc_opt name defs with
        | None -> T_app (path, name, l, anno)
        | Some macro -> (
            match l with
            | [] -> aux defs macro.body
            | _ ->
              (* TODO: add anno to term after expansion maybe *)
              let subs =
                List.map2
                  (fun binding x ->
                     (Binding.name binding, x))
                  macro.arg_and_typs
                  l
              in
              let x =
                Term.sub ~loc:(Path.loc path) subs
                  macro.body
              in
              aux defs x))
    | T_unary_op (op, x) -> T_unary_op (op, aux defs x)
    | T_binary_op (op, x, y) ->
      T_binary_op
        (op, aux defs x, aux defs y)
    | T_cell_pat_match (x, y) ->
      T_cell_pat_match (x, aux defs y)
    | T_cell_assign (x, y) -> T_cell_assign (x, aux defs y)
    | T_let { binding; next } ->
      T_let
        {
          binding = Binding.map (aux defs) binding;
          next = aux defs next;
        }
    | T_let_macro { binding; next; _ } ->
      let macro = aux_macro defs (Binding.get binding) in
      aux
        ((Binding.name binding, macro) :: defs)
        next
    | T_action { fact; temporal } ->
      T_action { fact = aux defs fact; temporal }
    | T_quantified { loc; quantifier; quant; formula } ->
      T_quantified
        {
          loc;
          quantifier;
          quant;
          formula = aux defs formula;
        }
  in
  aux defs term

and aux_terms defs terms =
  List.map (aux_term defs) terms

and aux_macro defs macro =
  { macro with body = aux_term defs macro.body }

let aux_rule defs (rule : Tg_ast.rule) : Tg_ast.rule =
  let open Tg_ast in
  let { l; vars_in_l; bindings_before_a; a; bindings_before_r; r } = rule in
  let defs_a =
    List.fold_left
      (fun acc x ->
         match x with
         | R_let _ -> failwith "Unexpected case"
         | R_let_macro { binding; _ } ->
           (Binding.name binding, Binding.get binding) :: acc)
      defs bindings_before_a
  in
  let defs_r =
    List.fold_left
      (fun acc x ->
         match x with
         | R_let _ -> failwith "Unexpected case"
         | R_let_macro { binding; _ } ->
           (Binding.name binding, Binding.get binding) :: acc)
      defs_a bindings_before_r
  in
  {
    l = aux_terms defs l;
    vars_in_l;
    bindings_before_a = [];
    a = aux_terms defs_a a;
    bindings_before_r = [];
    r = aux_terms defs_r r;
  }

let aux_proc
    (term_macro_defs : (Name.t * Tg_ast.macro) list)
    (proc_macro_defs : (Name.t * Tg_ast.proc_macro) list)
    (proc : Tg_ast.proc)
  : Tg_ast.proc =
  let open Tg_ast in
  let rec aux term_macro_defs proc =
    match proc with
    | P_null (* | P_goto _ *) -> proc
    (* | P_entry_point { name; next } ->
       P_entry_point { name; next = aux term_macro_defs next } *)
    | P_let { binding; next } ->
      P_let
        {
          binding = Binding.map (aux_term term_macro_defs) binding;
          next = aux term_macro_defs next;
        }
    | P_let_macro { binding; next; _ } ->
      let macro =
        aux_macro term_macro_defs
          (Binding.get binding)
      in
      aux
        ((Binding.name binding, macro) :: term_macro_defs)
        next
    | P_app (path, name, args, next) -> (
        let args = List.map (aux_term term_macro_defs) args in
        match List.assoc_opt name proc_macro_defs with
        | None -> failwith "Unexpected case"
        | Some macro -> (
            let body =
              match args with
              | [] -> macro.body
              | _ ->
                let cell_subs, subs =
                  List.fold_left2
                    (fun (cell_subs, subs) binding arg ->
                       match Binding.get binding with
                       | `Cell -> (
                           match arg with
                           | T_symbol (arg_cell, `Cell) ->
                             ((Binding.name_str_untagged binding, arg_cell) :: cell_subs,
                              subs)
                           | _ -> failwith "Unexpected case"
                         )
                       | _ -> (
                           (cell_subs,
                            (Binding.name binding, arg) :: subs
                           )
                         )
                    )
                    ([], [])
                    macro.arg_and_typs args
                in
                Proc.sub ~loc:(Path.loc path) ~cell_subs subs
                  macro.body
            in
            let next =
              aux
                term_macro_defs
                next
            in
            Misc_utils.replace_proc_end
              ~replace_with:next body
          )
      )
    | P_line { tag; rule; next } ->
      P_line {
        tag;
        rule = aux_rule term_macro_defs rule;
        next = aux term_macro_defs next;
      }
    | P_branch (loc, procs, next) ->
      P_branch
        ( loc,
          List.map (aux term_macro_defs) procs,
          aux term_macro_defs next )
    | P_scoped (proc, next) ->
      P_scoped
        ( aux term_macro_defs proc,
          aux term_macro_defs next )
    | P_while_cell_cas { label; mode; cell; term; proc; next } ->
      P_while_cell_cas {
        label;
        mode;
        cell;
        term;
        proc = aux term_macro_defs proc;
        next = aux term_macro_defs next;
      }
  in
  aux term_macro_defs proc

let aux_modul (decls : Tg_ast.modul) : Tg_ast.modul =
  let open Tg_ast in
  let rec aux term_macro_defs proc_macro_defs acc decls 
    : decl list
      * (Name.t * macro) list
      * (Name.t * proc_macro) list =
    match decls with
    | [] -> (List.rev acc, term_macro_defs, proc_macro_defs)
    | d :: ds -> (
        match d with
        | D_process { binding } ->
          let d =
            D_process
              { binding = Binding.map (aux_proc term_macro_defs proc_macro_defs) binding }
          in
          aux term_macro_defs proc_macro_defs (d :: acc) ds
        | D_process_macro binding ->
          let { arg_and_typs; body } : proc_macro = Binding.get binding in
          aux term_macro_defs
            (( Binding.name binding,
               { arg_and_typs;
                 body = aux_proc term_macro_defs proc_macro_defs body
               }
             )
             :: proc_macro_defs)
            acc ds
        | D_let { binding } ->
          let d =
            D_let
              {
                binding =
                  Binding.map (aux_term term_macro_defs) binding;
              }
          in
          aux term_macro_defs proc_macro_defs (d :: acc) ds
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_open _ | D_insert _ ->
          aux term_macro_defs proc_macro_defs (d :: acc) ds
        | D_macro { binding; _ } ->
          let { arg_and_typs; ret_typ; body } = Binding.get binding in
          aux
            (( Binding.name binding,
               {
                 arg_and_typs;
                 ret_typ;
                 body = aux_term term_macro_defs body;
               } )
             :: term_macro_defs)
            proc_macro_defs
            acc ds
        | D_lemma { binding } ->
          let d =
            D_lemma
              {
                binding =
                  Binding.map
                    (fun lemma ->
                       { lemma with
                         formula = aux_term term_macro_defs lemma.formula })
                    binding;
              }
          in
          aux term_macro_defs proc_macro_defs (d :: acc) ds
        | D_restriction { binding } ->
          let d =
            D_restriction
              {
                binding =
                  Binding.map (aux_term term_macro_defs) binding;
              }
          in
          aux term_macro_defs proc_macro_defs (d :: acc) ds
        | D_equation { binding } ->
          let d =
            D_equation
              {
                binding =
                  Binding.map (aux_term term_macro_defs) binding;
              }
          in
          aux term_macro_defs proc_macro_defs (d :: acc) ds
        | D_rule { binding } ->
          let d =
            D_rule
              {
                binding =
                  Binding.map (aux_rule term_macro_defs) binding;
              }
          in
          aux term_macro_defs proc_macro_defs (d :: acc) ds
        | D_modul (name, modul) ->
          let modul, term_macro_defs, proc_macro_defs =
            aux term_macro_defs proc_macro_defs [] modul
          in
          let d = D_modul (name, modul) in
          aux term_macro_defs proc_macro_defs (d :: acc) ds
        | D_builtins _ -> failwith "Unexpected case"
      )
  in
  let decls, _, _ = aux [] [] [] decls in
  decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  Ok { spec with root = aux_modul spec.root }
