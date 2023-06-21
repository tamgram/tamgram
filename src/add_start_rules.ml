let aux_proc (proc : Tg_ast.proc) : Tg_ast.proc =
  let open Tg_ast in
  let start_rule : Tg_ast.rule =
    {
      l =
        [
          T_app
            { path = Path.of_string "Fr";
              name = `Global 0;
              named_args = [];
              args = [
                T_var
                  ( Path.of_string Params.pid_cell_name,
                    `Local 0,
                    Some `Fresh );
              ];
              anno = None;
            };
        ];
      vars_in_l =
        [
          Binding.make ~name:(`Local 0)
            (Loc.untagged Params.pid_cell_name)
            `Fresh;
        ];
      bindings_before_a = [];
      a = [];
      bindings_before_r = [];
      r =
        [
          T_cell_assign
            ( Loc.untagged Params.pid_cell_name,
              T_var
                ([ Loc.untagged Params.pid_cell_name ], `Local 0, Some `Fresh)
            );
        ];
    }
  in
  P_line { tag = None; rule = start_rule; next = proc }

let aux_modul (decls : Tg_ast.modul) : Tg_ast.modul =
  let open Tg_ast in
  let rec aux acc decls =
    match decls with
    | [] -> List.rev acc
    | d :: ds ->
      let d =
        match d with
        | D_process { binding } ->
          D_process
            { binding = Binding.map aux_proc binding }
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_equation _ | D_lemma _
        | D_restriction _ | D_rule _ | D_import _ ->
          d
        | D_process_macro _
        | D_let _ | D_macro _ -> failwith "Unexpected case"
        | D_modul (name, m) -> D_modul (name, aux [] m)
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux (d :: acc) ds
  in
  aux [] decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  Ok { spec with root = aux_modul spec.root }
