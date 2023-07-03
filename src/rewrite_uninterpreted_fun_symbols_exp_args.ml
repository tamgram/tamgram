open Result_syntax

let aux_macro ~binding ~named_arg_and_typs ~arg_and_typs ~ret_typ : Tg_ast.macro =
  let open Tg_ast in
  {
    named_arg_and_typs;
    arg_and_typs;
    ret_typ;
    body = T_app { path = [ Binding.name_str binding ];
                   name = `Local 0;
                   named_args = [];
                   args =
                     (List.map (fun b ->
                          T_var ([ Binding.name_str b], `Local 0, None))
                         named_arg_and_typs)
                     @ (List.map (fun b ->
                         T_var ([ Binding.name_str b], `Local 0, None))
                         arg_and_typs);
                   anno = None;
                 };
  }

let aux_modul (modul : Tg_ast.modul) : (Tg_ast.modul, Error_msg.t) result =
  let open Tg_ast in
  let rec aux acc decls =
    match decls with
    | [] -> Ok (List.rev acc)
    | d :: ds ->
      let* ds' =
        match d with
        | D_fun_exp_args binding ->
          let { named_arg_and_typs; arg_and_typs } : fun_symbol_explicit_args = Binding.get binding in
          let arity = List.length named_arg_and_typs + List.length arg_and_typs in
          let macro = aux_macro ~binding ~named_arg_and_typs ~arg_and_typs ~ret_typ:`Bitstring in
          Ok
            [ D_fun (Binding.make (Binding.name_str binding) arity)
            ; D_macro { binding = Binding.make (Binding.name_str binding) macro }
            ]
        | D_pred_exp_args binding ->
          let { named_arg_and_typs; arg_and_typs } : fun_symbol_explicit_args = Binding.get binding in
          let arity = List.length named_arg_and_typs + List.length arg_and_typs in
          let macro = aux_macro ~binding ~named_arg_and_typs ~arg_and_typs ~ret_typ:`Fact in
          Ok
            [ D_fun (Binding.make (Binding.name_str binding) arity)
            ; D_macro { binding = Binding.make (Binding.name_str binding) macro }
            ]
        | D_ppred_exp_args binding ->
          let { named_arg_and_typs; arg_and_typs } : fun_symbol_explicit_args = Binding.get binding in
          let arity = List.length named_arg_and_typs + List.length arg_and_typs in
          let macro = aux_macro ~binding ~named_arg_and_typs ~arg_and_typs ~ret_typ:`Pfact in
          Ok
            [ D_fun (Binding.make (Binding.name_str binding) arity)
            ; D_macro { binding = Binding.make (Binding.name_str binding) macro }
            ]
        | D_apred_exp_args binding ->
          let { named_arg_and_typs; arg_and_typs } : fun_symbol_explicit_args = Binding.get binding in
          let arity = List.length named_arg_and_typs + List.length arg_and_typs in
          let macro = aux_macro ~binding ~named_arg_and_typs ~arg_and_typs ~ret_typ:`Afact in
          Ok
            [ D_fun (Binding.make (Binding.name_str binding) arity)
            ; D_macro { binding = Binding.make (Binding.name_str binding) macro }
            ]
        | D_papred_exp_args binding ->
          let { named_arg_and_typs; arg_and_typs } : fun_symbol_explicit_args = Binding.get binding in
          let arity = List.length named_arg_and_typs + List.length arg_and_typs in
          let macro = aux_macro ~binding ~named_arg_and_typs ~arg_and_typs ~ret_typ:`Pafact in
          Ok
            [ D_fun (Binding.make (Binding.name_str binding) arity)
            ; D_macro { binding = Binding.make (Binding.name_str binding) macro }
            ]
        | D_process _
        | D_process_macro _
        | D_rule _
        | D_builtins _
        | D_fun _
        | D_pred _
        | D_ppred _
        | D_apred _
        | D_papred _
        | D_let _ | D_macro _ | D_equation _
        | D_lemma _ | D_restriction _ | D_import _ | D_modul_alias _ ->
          Ok [ d ]
        | D_modul (name, m) ->
          let+ m = aux [] m in
          [ D_modul (name, m) ]
      in
      aux ((List.rev ds') @ acc) ds
  in
  aux [] modul

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let+ root = aux_modul spec.root in
  { spec with root }
