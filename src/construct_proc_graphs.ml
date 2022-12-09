open Result_infix

let add_apred_decls (restrictions_required : Tg_graph.restrictions_required) (spec : Spec.t)
  : Spec.t =
  let decls =
    Int_map.to_seq restrictions_required.cell_pat_match_restrictions
    |> Seq.map (fun (id, _term) ->
        let open Tg_ast in
        D_apred
          (Binding.make_untagged
             (Fmt.str "%s%d" Params.cell_pat_match_apred_prefix id)
             1
          )
      )
    |> List.of_seq
  in
  { spec with
    root = decls @ spec.root
  }

let add_restrictions (restrictions_required : Tg_graph.restrictions_required) (spec : Spec.t)
  : Spec.t =
  let cell_pat_restrictions =
    Int_map.to_seq restrictions_required.cell_pat_match_restrictions
    |> Seq.map (fun (id, term) ->
        let open Tg_ast in
        let free_vars = Name_map.to_seq @@ Term.free_var_names_in_term term in
        let temporal_var = "i" in
        let cell_var = "cell" in
        D_restriction
          { binding =
              Binding.make_untagged (Fmt.str "%s%d" Params.cell_pat_match_restriction_prefix id)
                (T_quantified {
                    loc = None;
                    quantifier = `All;
                    quant = (Binding.make_untagged temporal_var `Temporal)
                            ::
                            (Binding.make_untagged cell_var `Bitstring)
                            ::
                            (free_vars
                             |> Seq.map (fun (name, x) -> Binding.make ~name x `Bitstring)
                             |> List.of_seq
                            );
                    formula =
                      T_binary_op (`Imp,
                                   T_action {
                                     fact = T_app (Path.of_string (Fmt.str "%s%d" Params.cell_pat_match_apred_prefix id),
                                                   `Local 0,
                                                   [T_var (Path.of_string cell_var, `Local 0, None)],
                                                   None);
                                     temporal = (Loc.untagged temporal_var, `Local 0);
                                   },
                                   T_unary_op (`Not,
                                               T_binary_op (`Eq, T_var (Path.of_string "cell", `Local 0, None), term)
                                              )
                                  )
                  }
                )
          }
      )
  in
  let restrictions =
    if restrictions_required.cell_neq then
      Seq.cons
        Tg_ast.(D_restriction
                  { binding =
                      Binding.make_untagged Params.cell_neq_restriction_name
                        (
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
                                            fact = T_app ( Path.of_string Params.cell_neq_apred_name,
                                                           `Local 0, [x; x], None);
                                            temporal = (Loc.untagged "i", `Local 0);
                                          };
                                      }
                                     )
                        )
                  })
        cell_pat_restrictions
    else
      cell_pat_restrictions
  in
  let rec aux decls =
    let open Tg_ast in
    match decls with
    | [] -> List.of_seq restrictions
    | x :: xs ->
      match x with
      | D_lemma _ ->
        Seq.fold_left (fun acc restriction ->
            restriction :: acc)
          decls
          restrictions
      | _ ->
        x :: aux xs
  in
  { spec with
    root = aux spec.root;
  }

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  let proc_graphs = ref Name_map.empty in
  let rule_tags = ref Int_map.empty in
  let restrictions_required = ref Tg_graph.restrictions_empty in
  let rec aux (decls : decl list) =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process { binding } ->
          let+ g, tags, restrictions = Tg_graph.of_proc (Binding.get binding) in
          proc_graphs :=
            Name_map.add (Binding.name binding) g !proc_graphs;
          rule_tags :=
            Int_map.union (fun _ _ _ -> failwith "Unexpected case") !rule_tags tags;
          restrictions_required :=
            Tg_graph.restrictions_required_union !restrictions_required restrictions
        | D_rule { binding } ->
          let proc =
            P_line { tag = None; rule = Binding.get binding; next = P_null }
          in
          let+ g, tags, _restrictions = Tg_graph.of_proc proc in
          proc_graphs :=
            Name_map.add (Binding.name binding) g !proc_graphs;
          rule_tags :=
            Int_map.union (fun _ _ _ -> failwith "Unexpected case") !rule_tags tags
        | D_modul (_, decls) ->
          aux decls
        | _ -> Ok ()
      in
      aux ds
  in
  let+ () = aux spec.root in
  {
    spec with
    proc_graphs = !proc_graphs;
    rule_tags = !rule_tags;
  }
  |> add_apred_decls !restrictions_required
  |> add_restrictions !restrictions_required
