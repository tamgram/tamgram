let while_used (decls : Tg_ast.modul) : bool =
  let open Tg_ast in
  let rec aux decls =
    match decls with
    | [] -> false
    | d :: ds ->
      let used =
        match d with
        | D_process { binding } ->
          Proc.while_used_in_proc (Binding.get binding)
        | D_modul (_name, m) -> aux m
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_equation _ | D_lemma _
        | D_restriction _ | D_rule _ | D_open _ | D_insert _ ->
          false
        | D_process_macro _
        | D_let _ | D_macro _ -> failwith "Unexpected case"
        | D_builtins _ -> failwith "Unexpected case"
      in
      used || aux ds
  in
  aux decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let restrictions =
    if while_used spec.root then
      Tg_ast.[
        (*D_restriction
          { binding =
              Binding.make_untagged Params.while_cell_eq_restriction_name
                Tg_ast.(
                  T_quantified {
                    loc = None;
                    quantifier = `All;
                    quant = [ Binding.make_untagged "x" `Bitstring
                            ; Binding.make_untagged "y" `Bitstring
                            ; Binding.make_untagged "i" `Temporal
                            ];
                    formula =
                      let x = T_var (Path.of_string "x", `Local 0, None) in
                      let y = T_var (Path.of_string "y", `Local 0, None) in
                      T_binary_op (`Imp,
                                   T_action {
                                     fact = T_app ( Path.of_string Params.while_cell_eq_apred_name, `Local 0, [x; y], None);
                                     temporal = (Loc.untagged "i", `Local 0);
                                   },
                                   T_binary_op (`Eq, x, y)
                                  );
                  }
                )
          }; *)
        D_restriction
          { binding =
              Binding.make_untagged Params.while_cell_neq_restriction_name
                Tg_ast.(
                  T_unary_op (`Not,
                              T_quantified {
                                loc = None;
                                quantifier = `Ex;
                                quant = [ Binding.make_untagged "x" `Bitstring
                                        ; Binding.make_untagged "i" `Temporal
                                        ];
                                formula =
                                  let x = T_var (Path.of_string "x", `Local 0, None) in
                                  T_action {
                                    fact = T_app ( Path.of_string Params.while_cell_neq_apred_name, `Local 0, [x; x], None);
                                    temporal = (Loc.untagged "i", `Local 0);
                                  };
                              }
                             )
                )
          };
      ]
    else
      []
  in
  Ok { spec with root = spec.root @ restrictions }
