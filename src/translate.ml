open Tr_utils

let pp_name_untagged formatter ((name_str, name) : string * Name.t) : unit =
  if List.mem name_str Params.builtin_functions
  || List.mem name_str Params.builtin_constants
  || List.mem name_str Params.reserved_names
  || name_str = Params.pid_cell_name
  || List.exists (fun prefix ->
      String.starts_with ~prefix name_str)
      Params.[
        state_pred_prefix;
        auto_gen_name_prefix;
        pcell_ptr_prefix;
        cell_pat_match_apred_prefix;
      ]
  then
    Fmt.pf formatter "%s" name_str
  else
    let name_str =
      (match CCString.chop_prefix ~pre:"_" name_str with
       | None -> name_str
       | Some s -> Params.tamarin_output_underscore_prefix_replacement ^ s
      )
      |> CCString.replace ~which:`All ~sub:"'" ~by:""
    in
    (match name with
     | `Global n ->
       Fmt.pf formatter "%s_%d" name_str n
     | `Local n ->
       Fmt.pf formatter "%s_%d" name_str n
    )

let name_str_untagged_of_path (path : Path.t) =
  Loc.content (List.hd (List.rev path))

let pp_path formatter ((path, name) : Path.t * Name.t) : unit =
  Fmt.pf formatter "%a"
    pp_name_untagged
    (name_str_untagged_of_path path, name)

let rewrite_name name_str name =
  Loc.untagged @@ Fmt.str "%a" pp_name_untagged (name_str, name)

let rewrite_path path name =
  Path.of_string
    (Fmt.str "%a" pp_path (path, name))

let rewrite_symbol_names_in_term (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ | T_symbol _ -> term
    | T_var (path, name, typ) -> T_var (rewrite_path path name, name, typ)
    | T_tuple (loc, l) -> T_tuple (loc, List.map aux l)
    | T_app { path; name; named_args; args; anno } ->
      let named_args = List.map (fun (s, x) -> (s, aux x)) named_args in
      let args = List.map aux args in
      T_app { path = rewrite_path path name; name; named_args; args; anno }
    | T_unary_op (op, term) ->
      T_unary_op (op, aux term)
    | T_binary_op (op, x1, x2) ->
      T_binary_op (op, aux x1, aux x2)
    | T_cell_pat_match (cell, x) ->
      T_cell_pat_match (cell, aux x)
    | T_cell_assign (cell, x) ->
      T_cell_assign (cell, aux x)
    | T_name_as _ | T_let _ | T_let_macro _ -> failwith "Unexpected case"
    | T_action { fact; temporal = (name_str, name) } ->
      T_action {
        fact = aux fact;
        temporal = (rewrite_name (Loc.content name_str) name, name);
      }
    | T_temporal_a_lt_b { a = (a0, a1); b = (b0, b1) } ->
      T_temporal_a_lt_b {
        a = (rewrite_name (Loc.content a0) a1, a1);
        b = (rewrite_name (Loc.content b0) b1, b1);
      }
    | T_temporal_eq { a = (a0, a1); b = (b0, b1) } ->
      T_temporal_eq {
        a = (rewrite_name (Loc.content a0) a1, a1);
        b = (rewrite_name (Loc.content b0) b1, b1);
      }
    | T_quantified { loc; quantifier; quant; formula } ->
      T_quantified
        { loc;
          quantifier;
          quant = List.map (fun binding ->
              let name = Binding.name binding in
              let name_str_untagged = Binding.name_str_untagged binding in
              Binding.update_name_str
                (rewrite_name name_str_untagged name)
                binding
            ) quant;
          formula = aux formula;
        }
  in
  aux term

let rewrite_symbol_names_in_rule (d : Tg_ast.decl) : Tg_ast.decl =
  let open Tg_ast in
  match d with
  | D_rule { binding } ->
    D_rule { binding = Binding.map (fun { l; a; r; _ } ->
        { l = List.map rewrite_symbol_names_in_term l;
          vars_in_l = [];
          bindings_before_a = [];
          a = List.map rewrite_symbol_names_in_term a;
          bindings_before_r = [];
          r = List.map rewrite_symbol_names_in_term r;
        }
      ) binding }
  | _ -> d

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux (lift_to_global : Tg_ast.decl list list) (acc : Tg_ast.decl list list) (decls : Tg_ast.decl list) : (Tg_ast.decl list * Tg_ast.decl list) =
    match decls with
    | [] -> (List.flatten @@ List.rev lift_to_global, List.flatten @@ List.rev acc)
    | d :: ds ->
      let lift_to_global', d' =
        match d with
        | D_modul (name, decls) ->
          let lift_to_global', decls = aux [] [] decls in
          (lift_to_global', [ D_modul (name, decls) ])
        | D_rule { binding } -> (
            let g = Name_map.find (Binding.name binding) spec.proc_graphs in
            let vertices = List.of_seq (Graph.vertex_seq g) in
            match vertices with
            | [ (_k, ru) ] ->
              let d = D_rule {
                  binding =
                    Binding.make
                      (Loc.untagged @@ Fmt.str "%a" pp_name_of_proc binding)
                      ru
                }
              in
              ([],
               [ rewrite_symbol_names_in_rule d ]
              )
            | _ -> failwith "Unexpected case"
          )
        | D_process { binding } ->
          ([],
           (match !Params.translate_style with
            | `Cell_by_cell ->
              Tr_cell_by_cell.[
                rule_tr binding spec;
                end_tr binding spec;
              ]
            | `Frame ->
              Tr_frame.[
                rule_tr binding spec;
                end_tr binding spec;
              ]
            | `Frame_minimal0 ->
              Tr_frame_minimal0.[
                rule_tr binding spec;
                end_tr binding spec;
              ]
            | `Frame_minimal1 ->
              Tr_frame_minimal1.[
                rule_tr binding spec;
                end_tr binding spec;
              ]
            | `Persistent0 ->
              Tr_persistent0.[
                rule_tr binding spec;
                end_tr binding spec;
              ]
            | `Frame_minimal_backward0 ->
              Tr_frame_minimal_backward0.[
                start_tr binding spec;
                rule_tr binding spec;
              ]
            | `Frame_minimal_hybrid0 ->
              Tr_frame_minimal_hybrid0.[
                start_tr binding spec;
                rule_tr binding spec;
                end_tr binding spec;
              ]
           )
           |> List.to_seq
           |> Seq.concat
           |> Seq.map rewrite_symbol_names_in_rule
           |> List.of_seq
          )
        | D_fun binding ->
          (
            [ D_fun (Binding.update_name_str_untagged (
                  let name_str_untagged = Binding.name_str_untagged binding in
                  let name = Binding.name binding in
                  Fmt.str "%a" pp_name_untagged (name_str_untagged, name))
                  binding
                )
            ],
            []
          )
        | D_pred binding ->
          (
            [ D_pred (Binding.update_name_str_untagged (
                  let name_str_untagged = Binding.name_str_untagged binding in
                  let name = Binding.name binding in
                  Fmt.str "%a" pp_name_untagged (name_str_untagged, name))
                  binding
                )
            ],
            []
          )
        | D_ppred binding ->
          (
            [ D_ppred (Binding.update_name_str_untagged (
                  let name_str_untagged = Binding.name_str_untagged binding in
                  let name = Binding.name binding in
                  Fmt.str "%a" pp_name_untagged (name_str_untagged, name))
                  binding
                )
            ],
            []
          )
        | D_apred binding ->
          (
            [ D_apred (Binding.update_name_str_untagged (
                  let name_str_untagged = Binding.name_str_untagged binding in
                  let name = Binding.name binding in
                  Fmt.str "%a" pp_name_untagged (name_str_untagged, name))
                  binding
                )
            ],
            []
          )
        | D_papred binding ->
          (
            [ D_papred (Binding.update_name_str_untagged (
                  let name_str_untagged = Binding.name_str_untagged binding in
                  let name = Binding.name binding in
                  Fmt.str "%a" pp_name_untagged (name_str_untagged, name))
                  binding
                )
            ],
            []
          )
        | D_equation { binding } ->
          ([],
           [ D_equation {
                 binding =
                   Binding.map
                     rewrite_symbol_names_in_term
                     binding 
               }
           ]
          )
        | D_lemma { binding } ->
          ([],
           [ D_lemma {
                 binding =
                   Binding.map
                     (fun lemma ->
                        { lemma with formula = rewrite_symbol_names_in_term lemma.formula } )
                     binding 
               }
           ]
          )
        | D_restriction { binding } ->
          ([],
           [ D_restriction {
                 binding =
                   Binding.map
                     rewrite_symbol_names_in_term
                     binding
               }
           ]
          )
        | _ ->
          ([], [ d ])
      in
      aux (lift_to_global' :: lift_to_global) (d' :: acc) ds
  in
  let lift_to_global, decls = aux [] [] spec.root in
  let decls =
    match !Params.translate_style with
    | `Persistent0 ->
      Tr_persistent0.restriction :: decls
    | _ -> decls
  in
  Ok { spec with root = lift_to_global @ decls }
