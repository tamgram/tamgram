open Result_syntax

let ( let** ) (r : ('a, Error_msg.t * [< Lexical_ctx.name_resolution_error ]) result)
    f =
  match r with
  | Ok v -> f v
  | Error (x, y) -> Error (x, Some (y :> Lexical_ctx.name_resolution_error))

let ( let++ ) (r : ('a, Error_msg.t * [< Lexical_ctx.name_resolution_error ]) result)
    f =
  match r with
  | Ok v -> Ok (f v)
  | Error (x, y) -> Error (x, Some (y :> Lexical_ctx.name_resolution_error))

let check_for_dup_args (args : string Loc.tagged list) : (unit, Error_msg.t) result =
  let rec aux (seen : (string * Loc.t option) list) args =
    match args with
    | [] -> Ok ()
    | x :: xs -> (
        match List.assoc_opt (Loc.content x) seen with
        | Some loc ->
          Error
            (Error_msg.make
               (Loc.tag x)
               (Fmt.str "Name %s already used in the arguments at %a"
                  (Loc.content x) Loc.pp_opt loc))
        | None -> aux ((Loc.content x, Loc.tag x) :: seen) xs)
  in
  aux [] args

let rec aux_term
    ~(lexical_ctx_for_var : Lexical_ctx.t)
    ~(lexical_ctx_for_func : Lexical_ctx.t)
    (term : Tg_ast.term)
  : (Tg_ast.term, Error_msg.t * Lexical_ctx.name_resolution_error option) result =
  let open Tg_ast in
  let rec aux ~lexical_ctx_for_var ~lexical_ctx_for_func term =
    match term with
    | T_value _ | T_symbol _ | T_name_as _ -> Ok term
    | T_var (path, _, typ) ->
      let** name =
        Lexical_ctx.resolve_name path lexical_ctx_for_var
      in
      Ok (T_var (path, name, typ))
    | T_tuple (loc, l) ->
      let+ l =
        aux_terms ~lexical_ctx_for_var ~lexical_ctx_for_func l
      in
      T_tuple (loc, l)
    | T_app { path; named_args; args; anno; _ } ->
      let** name =
        Lexical_ctx.resolve_name path lexical_ctx_for_func
      in
      let* named_args =
        aux_named_args ~lexical_ctx_for_var ~lexical_ctx_for_func named_args
      in
      let+ args =
        aux_terms ~lexical_ctx_for_var ~lexical_ctx_for_func args
      in
      T_app { path; name; named_args; args; anno }
    | T_unary_op (op, x) ->
      let+ x =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func x
      in
      T_unary_op (op, x)
    | T_binary_op (op, x, y) ->
      let* x =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func x
      in
      let+ y =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func y
      in
      T_binary_op (op, x, y)
    | T_cell_pat_match (x, y) ->
      let+ y =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func y
      in
      T_cell_pat_match (x, y)
    | T_cell_assign (x, y) ->
      let+ y =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func y
      in
      T_cell_assign (x, y)
    | T_let { binding; next } ->
      let* bound_to =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func (Binding.get binding)
      in
      let lexical_ctx_for_var, name =
        Lexical_ctx.add_local_name_str
          (Binding.name_str_untagged binding)
          lexical_ctx_for_var
      in
      let+ next =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func next
      in
      T_let
        {
          binding =
            binding |> Binding.update_name name |> Binding.update bound_to;
          next;
        }
    | T_let_macro { binding; next } ->
      let* binding =
        aux_macro ~lexical_ctx_for_var ~lexical_ctx_for_func binding
      in
      let lexical_ctx_for_func, name =
        Lexical_ctx.add_local_name_str
          (Binding.name_str_untagged binding)
          lexical_ctx_for_func
      in
      let+ next =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func next
      in
      T_let_macro
        { binding = Binding.update_name name binding; next }
    | T_action { fact; temporal = t, _ } ->
      let* fact =
        aux_term ~lexical_ctx_for_var ~lexical_ctx_for_func fact
      in
      let++ name = Lexical_ctx.resolve_name [ t ] lexical_ctx_for_var in
      T_action { fact; temporal = (t, name) }
    | T_temporal_eq { a = a, _; b = b, _ } ->
      let** a_name = Lexical_ctx.resolve_name [ a ] lexical_ctx_for_var in
      let++ b_name = Lexical_ctx.resolve_name [ b ] lexical_ctx_for_var in
      T_temporal_eq { a = (a, a_name); b = (b, b_name) }
    | T_temporal_a_lt_b { a = a, _; b = b, _ } ->
      let** a_name = Lexical_ctx.resolve_name [ a ] lexical_ctx_for_var in
      let++ b_name = Lexical_ctx.resolve_name [ b ] lexical_ctx_for_var in
      T_temporal_a_lt_b { a = (a, a_name); b = (b, b_name) }
    | T_quantified { loc; quantifier; quant; formula } ->
      let lexical_ctx_for_var, quant =
        CCList.fold_map
          (fun lexical_ctx x ->
             let lexical_ctx, name =
               Lexical_ctx.add_local_name_str
                 (Binding.name_str_untagged x)
                 lexical_ctx
             in
             (lexical_ctx, Binding.update_name name x))
          lexical_ctx_for_var quant
      in
      let+ formula =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func formula
      in
      T_quantified { loc; quantifier; quant; formula }
  in
  aux ~lexical_ctx_for_var ~lexical_ctx_for_func term

and aux_terms ~lexical_ctx_for_var ~lexical_ctx_for_func terms =
  let rec aux acc ~lexical_ctx_for_var ~lexical_ctx_for_func terms =
    match terms with
    | [] -> Ok (List.rev acc)
    | x :: xs ->
      let* x =
        aux_term ~lexical_ctx_for_var ~lexical_ctx_for_func x
      in
      aux (x :: acc) ~lexical_ctx_for_var ~lexical_ctx_for_func xs
  in
  aux [] ~lexical_ctx_for_var ~lexical_ctx_for_func terms

and aux_named_args ~lexical_ctx_for_var ~lexical_ctx_for_func named_args =
  let names, args = List.split named_args in
  let+ args = aux_terms ~lexical_ctx_for_var ~lexical_ctx_for_func args in
  List.combine names args

and aux_macro
    ~lexical_ctx_for_var
    ~lexical_ctx_for_func
    (binding : Tg_ast.macro Binding.t)
  : ( Tg_ast.macro Binding.t,
      Error_msg.t * Lexical_ctx.name_resolution_error option )
      result
  =
  let open Tg_ast in
  let { named_arg_and_typs; arg_and_typs; ret_typ; body } = Binding.get binding in
  match check_for_dup_args (List.map Binding.name_str arg_and_typs) with
  | Error msg -> Error (msg, None)
  | Ok () ->
    let lexical_ctx_for_var, named_arg_and_typs =
      CCList.fold_map
        (fun lexical_ctx x ->
           let lexical_ctx, name =
             Lexical_ctx.add_local_name_str
               (Binding.name_str_untagged x)
               lexical_ctx
           in
           (lexical_ctx, Binding.update_name name x))
        lexical_ctx_for_var named_arg_and_typs
    in
    let lexical_ctx_for_var, arg_and_typs =
      CCList.fold_map
        (fun lexical_ctx x ->
           let lexical_ctx, name =
             Lexical_ctx.add_local_name_str
               (Binding.name_str_untagged x)
               lexical_ctx
           in
           (lexical_ctx, Binding.update_name name x))
        lexical_ctx_for_var arg_and_typs
    in
    let+ body =
      aux_term ~lexical_ctx_for_var ~lexical_ctx_for_func body
    in
    Binding.update { named_arg_and_typs; arg_and_typs; ret_typ; body } binding

let aux_rule_bindings
    ~(lexical_ctx_for_var : Lexical_ctx.t)
    ~(lexical_ctx_for_func : Lexical_ctx.t)
    (bindings : Tg_ast.rule_binding list)
  : ( Lexical_ctx.t * Lexical_ctx.t * Tg_ast.rule_binding list,
      Error_msg.t * Lexical_ctx.name_resolution_error option )
      result =
  let open Tg_ast in
  let rec aux ~lexical_ctx_for_var ~lexical_ctx_for_func acc bindings =
    match bindings with
    | [] -> Ok (lexical_ctx_for_var, lexical_ctx_for_func, List.rev acc)
    | x :: xs -> (
        match x with
        | R_let x ->
          let* bound_to =
            aux_term ~lexical_ctx_for_var ~lexical_ctx_for_func (Binding.get x)
          in
          let lexical_ctx_for_var, name =
            Lexical_ctx.add_local_name_str
              (Binding.name_str_untagged x)
              lexical_ctx_for_var
          in
          let x = x |> Binding.update_name name |> Binding.update bound_to in
          aux ~lexical_ctx_for_var ~lexical_ctx_for_func (R_let x :: acc) xs
        | R_let_macro { binding } ->
          let* binding = aux_macro ~lexical_ctx_for_var ~lexical_ctx_for_func binding in
          let lexical_ctx_for_func, name =
            Lexical_ctx.add_local_name_str
              (Binding.name_str_untagged binding)
              lexical_ctx_for_func
          in
          let x =
            R_let_macro
              { binding = Binding.update_name name binding }
          in
          aux ~lexical_ctx_for_var ~lexical_ctx_for_func (x :: acc) xs)
  in
  aux ~lexical_ctx_for_var ~lexical_ctx_for_func [] bindings

let aux_rule
    ~(lexical_ctx_for_var : Lexical_ctx.t)
    ~(lexical_ctx_for_func : Lexical_ctx.t)
    (rule : Tg_ast.rule)
  : (Tg_ast.rule, Error_msg.t * Lexical_ctx.name_resolution_error option) result =
  let open Tg_ast in
  let { l; vars_in_l = _; bindings_before_a; a; bindings_before_r; r } = rule in
  let free_name_str_and_typs_in_l =
    Term.free_var_name_str_and_typs_in_terms l |> String_map.to_list
  in
  let free_name_strs_in_l_untagged = List.map fst free_name_str_and_typs_in_l in
  let lexical_ctx_for_var, l_names =
    Lexical_ctx.add_local_name_strs
      free_name_strs_in_l_untagged
      lexical_ctx_for_var
  in
  let* l =
    aux_terms ~lexical_ctx_for_var ~lexical_ctx_for_func l
  in
  let vars_in_l =
    List.map2
      (fun (name_str, typ) name ->
         Binding.make ~name (Loc.update_content name_str typ) (Loc.content typ))
      free_name_str_and_typs_in_l l_names
  in
  let* lexical_ctx_for_var, lexical_ctx_for_func, bindings_before_a =
    aux_rule_bindings
      ~lexical_ctx_for_var
      ~lexical_ctx_for_func
      bindings_before_a
  in
  let* a = aux_terms ~lexical_ctx_for_var ~lexical_ctx_for_func a in
  let* lexical_ctx_for_var, lexical_ctx_for_func, bindings_before_r =
    aux_rule_bindings
      ~lexical_ctx_for_var
      ~lexical_ctx_for_func
      bindings_before_r
  in
  let+ r = aux_terms ~lexical_ctx_for_var ~lexical_ctx_for_func r in
  { l; vars_in_l; bindings_before_a; a; bindings_before_r; r }

let aux_proc
    ~(lexical_ctx_for_var : Lexical_ctx.t)
    ~(lexical_ctx_for_func : Lexical_ctx.t)
    (proc : Tg_ast.proc)
  : (Tg_ast.proc, Error_msg.t * Lexical_ctx.name_resolution_error option) result =
  let open Tg_ast in
  let rec aux ~lexical_ctx_for_var ~lexical_ctx_for_func proc =
    match proc with
    | P_null | P_break _ | P_continue _ -> Ok proc
    | P_let { binding; next } ->
      let* bound_to =
        aux_term
          ~lexical_ctx_for_var
          ~lexical_ctx_for_func
          (Binding.get binding)
      in
      let lexical_ctx_for_var, name =
        Lexical_ctx.add_local_name_str
          (Binding.name_str_untagged binding)
          lexical_ctx_for_var
      in
      let+ next = aux ~lexical_ctx_for_var ~lexical_ctx_for_func next in
      P_let
        {
          binding =
            binding |> Binding.update_name name |> Binding.update bound_to;
          next;
        }
    | P_let_macro { binding; next } ->
      let* binding =
        aux_macro ~lexical_ctx_for_var ~lexical_ctx_for_func binding
      in
      let lexical_ctx_for_func, name =
        Lexical_ctx.add_local_name_str
          (Binding.name_str_untagged binding)
          lexical_ctx_for_func
      in
      let+ next = aux ~lexical_ctx_for_var ~lexical_ctx_for_func next in
      P_let_macro
        { binding = Binding.update_name name binding; next }
    | P_app { path; named_args; args; next; _ } ->
      let** name = Lexical_ctx.resolve_name path lexical_ctx_for_func in
      let* named_args =
        aux_named_args ~lexical_ctx_for_var ~lexical_ctx_for_func named_args
      in
      let* args =
        aux_terms ~lexical_ctx_for_var ~lexical_ctx_for_func args
      in
      let+ next =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func next
      in
      P_app { path; name; named_args; args; next }
    | P_line { tag; rule; next } ->
      let* rule =
        aux_rule ~lexical_ctx_for_var ~lexical_ctx_for_func rule
      in
      let+ next =
        aux ~lexical_ctx_for_var ~lexical_ctx_for_func next
      in
      P_line { tag; rule; next }
    | P_branch (loc, procs, next) ->
      let* procs =
        aux_list [] ~lexical_ctx_for_var ~lexical_ctx_for_func procs
      in
      let+ next = aux ~lexical_ctx_for_var ~lexical_ctx_for_func next in
      P_branch (loc, procs, next)
    | P_scoped (proc, next) ->
      let* proc = aux ~lexical_ctx_for_var ~lexical_ctx_for_func proc in
      let+ next = aux ~lexical_ctx_for_var ~lexical_ctx_for_func next in
      P_scoped (proc, next)
    | P_loop { label; mode; proc; next } -> (
        let* mode =
          match mode with
          | `While { mode; cell; term; _ } ->
            let free_vars =
              Term.free_var_name_strs_in_term term
              |> String_tagged_set.to_seq
              |> Seq.map Loc.content
              |> List.of_seq
            in
            let lexical_ctx_for_pat_term, names =
              Lexical_ctx.add_local_name_strs free_vars Lexical_ctx.empty
            in
            let vars_in_term =
              List.map2 (fun name name_str ->
                  Binding.make_untagged ~name name_str ()
                )
                names
                free_vars
            in
            let* term =
              aux_term ~lexical_ctx_for_var:lexical_ctx_for_pat_term ~lexical_ctx_for_func term
            in
            Ok (`While { mode; cell; term; vars_in_term })
          | `Unconditional -> Ok mode
        in
        let* proc = aux ~lexical_ctx_for_var ~lexical_ctx_for_func proc in
        let+ next = aux ~lexical_ctx_for_var ~lexical_ctx_for_func next in
        P_loop { label; mode; proc; next }
      )
    | P_if_then_else { loc; cond = { mode; cell; term; _ }; true_branch; false_branch; next } -> (
        let* cond =
          let free_vars =
            Term.free_var_name_strs_in_term term
            |> String_tagged_set.to_seq
            |> Seq.map Loc.content
            |> List.of_seq
          in
          let lexical_ctx_for_pat_term, names =
            Lexical_ctx.add_local_name_strs free_vars Lexical_ctx.empty
          in
          let vars_in_term =
            List.map2 (fun name name_str ->
                Binding.make_untagged ~name name_str ()
              )
              names
              free_vars
          in
          let* term =
            aux_term ~lexical_ctx_for_var:lexical_ctx_for_pat_term ~lexical_ctx_for_func term
          in
          Ok { mode; cell; term; vars_in_term }
        in
        let* true_branch = aux ~lexical_ctx_for_var ~lexical_ctx_for_func true_branch in
        let* false_branch = aux ~lexical_ctx_for_var ~lexical_ctx_for_func false_branch in
        let+ next = aux ~lexical_ctx_for_var ~lexical_ctx_for_func next in
        P_if_then_else { loc; cond; true_branch; false_branch; next }
      )
  and aux_list acc ~lexical_ctx_for_var ~lexical_ctx_for_func procs =
    match procs with
    | [] -> Ok (List.rev acc)
    | x :: xs ->
      let* x = aux ~lexical_ctx_for_var ~lexical_ctx_for_func x in
      aux_list (x :: acc) ~lexical_ctx_for_var ~lexical_ctx_for_func xs
  in
  aux ~lexical_ctx_for_var ~lexical_ctx_for_func proc

let aux_proc_macro
    ~lexical_ctx_for_var
    ~lexical_ctx_for_func
    (binding : Tg_ast.proc_macro Binding.t)
  : ( Tg_ast.proc_macro Binding.t,
      Error_msg.t * Lexical_ctx.name_resolution_error option )
      result =
  let open Tg_ast in
  let { named_arg_and_typs; arg_and_typs; body } : proc_macro = Binding.get binding in
  match check_for_dup_args (List.map Binding.name_str arg_and_typs) with
  | Error msg -> Error (msg, None)
  | Ok () ->
    let lexical_ctx_for_var, named_arg_and_typs =
      CCList.fold_map
        (fun lexical_ctx x ->
           match Binding.get x with
           | (_, `Cell) -> lexical_ctx, x
           | _ ->
             let lexical_ctx, name =
               Lexical_ctx.add_local_name_str
                 (Binding.name_str_untagged x)
                 lexical_ctx
             in
             (lexical_ctx, Binding.update_name name x))
        lexical_ctx_for_var named_arg_and_typs
    in
    let lexical_ctx_for_var, arg_and_typs =
      CCList.fold_map
        (fun lexical_ctx x ->
           match Binding.get x with
           | (_, `Cell) -> lexical_ctx, x
           | _ ->
             let lexical_ctx, name =
               Lexical_ctx.add_local_name_str
                 (Binding.name_str_untagged x)
                 lexical_ctx
             in
             (lexical_ctx, Binding.update_name name x))
        lexical_ctx_for_var arg_and_typs
    in
    let+ body =
      aux_proc ~lexical_ctx_for_var ~lexical_ctx_for_func body
    in
    Binding.update { named_arg_and_typs; arg_and_typs; body } binding

let aux_modul
    ~(lexical_ctx_for_var : Lexical_ctx.t)
    ~(lexical_ctx_for_func : Lexical_ctx.t)
    ~(lexical_ctx_for_form : Lexical_ctx.t)
    (modul : Tg_ast.modul)
  :
    ( Lexical_ctx.t * Lexical_ctx.t * Lexical_ctx.t * Tg_ast.modul,
      Error_msg.t * Lexical_ctx.name_resolution_error option )
      result =
  let open Tg_ast in
  let rec aux
      acc
      ~lexical_ctx_for_var
      ~lexical_ctx_for_func
      ~lexical_ctx_for_form
      decls
    =
    match decls with
    | [] -> Ok (
        lexical_ctx_for_var,
        lexical_ctx_for_func,
        lexical_ctx_for_form,
        List.rev acc
      )
    | d :: ds -> (
        match d with
        | D_fun _ | D_pred _ | D_ppred _ | D_apred _ | D_papred _ ->
          let lexical_ctx_for_func, d =
            Lexical_ctx.add_decl d lexical_ctx_for_func
          in
          let lexical_ctx_for_form, d =
            Lexical_ctx.add_decl ~reuse_name_global:true d
              lexical_ctx_for_form
          in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        | D_process { binding } ->
          let* x =
            aux_proc ~lexical_ctx_for_var ~lexical_ctx_for_func (Binding.get binding)
          in
          let d = D_process { binding = Binding.update x binding } in
          let lexical_ctx_for_var, d =
            Lexical_ctx.add_decl d lexical_ctx_for_var
          in
          let lexical_ctx_for_form, d =
            Lexical_ctx.add_decl ~reuse_name_global:true d
              lexical_ctx_for_form
          in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        | D_process_macro binding ->
          let* binding =
            aux_proc_macro ~lexical_ctx_for_var ~lexical_ctx_for_func
              binding
          in
          let d = D_process_macro binding in
          let lexical_ctx_for_func, d =
            Lexical_ctx.add_decl d lexical_ctx_for_func
          in
          let lexical_ctx_for_form, d =
            Lexical_ctx.add_decl ~reuse_name_global:true d
              lexical_ctx_for_form
          in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        | D_let { binding } ->
          let* bound_to =
            aux_term ~lexical_ctx_for_var ~lexical_ctx_for_func
              (Binding.get binding)
          in
          let d =
            D_let { binding = Binding.update bound_to binding }
          in
          let lexical_ctx_for_var, d =
            Lexical_ctx.add_decl d lexical_ctx_for_var
          in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        | D_macro { binding } ->
          let* binding =
            aux_macro ~lexical_ctx_for_var ~lexical_ctx_for_func binding
          in
          let d = D_macro { binding } in
          let lexical_ctx_for_func, d =
            Lexical_ctx.add_decl d lexical_ctx_for_func
          in
          let lexical_ctx_for_form, d =
            Lexical_ctx.add_decl ~reuse_name_global:true d
              lexical_ctx_for_form
          in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        | D_lemma { binding } ->
          let lemma = Binding.get binding in
          let* formula =
            aux_term
              ~lexical_ctx_for_var:lexical_ctx_for_form
              ~lexical_ctx_for_func:lexical_ctx_for_form
              lemma.formula
          in
          let binding =
            Binding.map (fun lemma -> { lemma with formula }) binding
          in
          let d = D_lemma { binding } in
          let lexical_ctx_for_var, d =
            Lexical_ctx.add_decl d lexical_ctx_for_var
          in
          let lexical_ctx_for_form, d =
            Lexical_ctx.add_decl ~reuse_name_global:true d
              lexical_ctx_for_form
          in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        | D_restriction { binding } ->
          let* formula =
            aux_term
              ~lexical_ctx_for_var:lexical_ctx_for_form
              ~lexical_ctx_for_func:lexical_ctx_for_form
              (Binding.get binding)
          in
          let binding = Binding.update formula binding in
          let d = D_restriction { binding } in
          let lexical_ctx_for_var, d =
            Lexical_ctx.add_decl d lexical_ctx_for_var
          in
          let lexical_ctx_for_form, d =
            Lexical_ctx.add_decl ~reuse_name_global:true d
              lexical_ctx_for_form
          in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        | D_equation { binding } ->
          let* formula =
            aux_term
              ~lexical_ctx_for_var:lexical_ctx_for_form
              ~lexical_ctx_for_func:lexical_ctx_for_form
              (Binding.get binding)
          in
          let binding = Binding.update formula binding in
          let d = D_equation { binding } in
          let lexical_ctx_for_var, d =
            Lexical_ctx.add_decl d lexical_ctx_for_var
          in
          let lexical_ctx_for_form, d =
            Lexical_ctx.add_decl ~reuse_name_global:true d
              lexical_ctx_for_form
          in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        | D_rule { binding } ->
          let* rule =
            aux_rule ~lexical_ctx_for_var ~lexical_ctx_for_func
              (Binding.get binding)
          in
          let binding = Binding.update rule binding in
          let d = D_rule { binding } in
          let lexical_ctx_for_var, d =
            Lexical_ctx.add_decl d lexical_ctx_for_var
          in
          let lexical_ctx_for_form, d =
            Lexical_ctx.add_decl ~reuse_name_global:true d
              lexical_ctx_for_form
          in
          aux (d :: acc) ~lexical_ctx_for_var ~lexical_ctx_for_func ~lexical_ctx_for_form ds
        | D_modul (name, body) ->
          let*
            lexical_ctx_for_var',
            lexical_ctx_for_func',
            lexical_ctx_for_form',
            body
            =
            aux []
              ~lexical_ctx_for_var:(Lexical_ctx.enter_sublevel
                                      lexical_ctx_for_var)
              ~lexical_ctx_for_func:(Lexical_ctx.enter_sublevel
                                       lexical_ctx_for_func)
              ~lexical_ctx_for_form:(Lexical_ctx.enter_sublevel
                                       lexical_ctx_for_form)
              body
          in
          let lexical_ctx_for_var =
            Lexical_ctx.add_submodul
              (Loc.content name) ~submodul:lexical_ctx_for_var'
              lexical_ctx_for_var
          in
          let lexical_ctx_for_func =
            Lexical_ctx.add_submodul
              (Loc.content name) ~submodul:lexical_ctx_for_func'
              lexical_ctx_for_func
          in
          let lexical_ctx_for_form =
            Lexical_ctx.add_submodul (Loc.content name)
              ~submodul:lexical_ctx_for_form' lexical_ctx_for_form
          in
          let d = D_modul (name, body) in
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
        (* | D_import path ->
           let** modul_for_var =
            Lexical_ctx.resolve_modul path lexical_ctx_for_var
           in
           let** modul_for_func =
            Lexical_ctx.resolve_modul path lexical_ctx_for_func
           in
           let** modul_for_form =
            Lexical_ctx.resolve_modul path lexical_ctx_for_form
           in
           let lexical_ctx_for_var =
            Lexical_ctx.open_modul ~into:lexical_ctx_for_var
              modul_for_var
           in
           let lexical_ctx_for_func =
            Lexical_ctx.open_modul ~into:lexical_ctx_for_func
              modul_for_func
           in
           let lexical_ctx_for_form =
            Lexical_ctx.open_modul ~into:lexical_ctx_for_form
              modul_for_form
           in
           aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
           | D_open path ->
           let** modul_for_var =
            Lexical_ctx.resolve_modul path lexical_ctx_for_var
           in
           let** modul_for_func =
            Lexical_ctx.resolve_modul path lexical_ctx_for_func
           in
           let** modul_for_form =
            Lexical_ctx.resolve_modul path lexical_ctx_for_form
           in
           let lexical_ctx_for_var =
            Lexical_ctx.open_modul ~into:lexical_ctx_for_var
              modul_for_var
           in
           let lexical_ctx_for_func =
            Lexical_ctx.open_modul ~into:lexical_ctx_for_func
              modul_for_func
           in
           let lexical_ctx_for_form =
            Lexical_ctx.open_modul ~into:lexical_ctx_for_form
              modul_for_form
           in
           aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
           | D_insert path ->
           let** modul_for_var =
            Lexical_ctx.resolve_modul path lexical_ctx_for_var
           in
           let** modul_for_func =
            Lexical_ctx.resolve_modul path lexical_ctx_for_func
           in
           let** modul_for_form =
            Lexical_ctx.resolve_modul path lexical_ctx_for_form
           in
           let lexical_ctx_for_var =
            Lexical_ctx.insert_modul ~into:lexical_ctx_for_var
              modul_for_var
           in
           let lexical_ctx_for_func =
            Lexical_ctx.insert_modul ~into:lexical_ctx_for_func
              modul_for_func
           in
           let lexical_ctx_for_form =
            Lexical_ctx.insert_modul ~into:lexical_ctx_for_form
              modul_for_form
           in
           aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds *)
        | D_import _
        | D_builtins _ ->
          aux
            (d :: acc)
            ~lexical_ctx_for_var
            ~lexical_ctx_for_func
            ~lexical_ctx_for_form
            ds
      )
  in
  aux
    []
    ~lexical_ctx_for_var
    ~lexical_ctx_for_func
    ~lexical_ctx_for_form
    modul

let unsatisfied_modul_imports (modul : Tg_ast.modul) : string Loc.tagged list =
  let open Tg_ast in
  let rec aux (seen : String_set.t) decls =
    match decls with
    | [] -> Seq.empty
    | d :: ds -> (
        match d with
        | D_modul (name, decls) -> (
            let seen' = String_set.add (Loc.content name) seen in
            Seq.append (aux seen decls) (aux seen' ds)
          )
        | D_import name -> (
            if String_set.mem (Loc.content name) seen then
              aux seen ds
            else
              Seq.cons name (aux seen ds)
          )
        | _ -> aux seen ds
      )
  in
  aux String_set.empty modul
  |> List.of_seq

(* let missing_top_level_modul (modul : Tg_ast.modul) : string option =
   Lexical_ctx.reset_name_indices_given_count ();
   match
    aux_modul
      ~lexical_ctx_for_var:Lexical_ctx.empty
      ~lexical_ctx_for_func:Lexical_ctx.empty
      ~lexical_ctx_for_form:Lexical_ctx.empty
      modul
   with
   | Error (_, e) -> (
      match e with
      | None -> None
      | Some e -> (
          match e with `Missing_top_level_modul s -> Some s | _ -> None))
   | Ok _ -> None *)

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  Lexical_ctx.reset_name_indices_given_count ();
  match
    aux_modul
      ~lexical_ctx_for_var:Lexical_ctx.empty
      ~lexical_ctx_for_func:Lexical_ctx.empty
      ~lexical_ctx_for_form:Lexical_ctx.empty
      spec.root
  with
  | Error (msg, _) -> Error msg
  | Ok (root_lexical_ctx_for_var,
        root_lexical_ctx_for_func,
        root_lexical_ctx_for_form,
        root) ->
    Ok Spec.{ spec with root;
                        root_lexical_ctx_for_var;
                        root_lexical_ctx_for_func;
                        root_lexical_ctx_for_form;
            }
