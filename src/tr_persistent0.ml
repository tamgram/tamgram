open Tr_utils

let pcell_ptr_of_cell (c : string) =
  Fmt.str "%s_%s" Params.pcell_ptr_prefix c

let rule_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  let roots = Int_set.of_seq @@ Graph.roots g in
  let total_cells_required =
    Seq.fold_left (fun acc (k, _ru) ->
        let cell_usage = Int_map.find k spec.cell_usages in
        let cells_required =
          Cell_lifetime.Usage.requires_cells cell_usage
        in
        String_tagged_set.union acc cells_required
      )
      String_tagged_set.empty
      (Graph.vertex_seq g)
  in
  Graph.edge_seq g
  |> Seq.map (fun (k, k') ->
      let ru = Graph.find k g in
      let cell_usage = Int_map.find k spec.cell_usages in
      let cells_required =
        Cell_lifetime.Usage.requires_cells cell_usage
        |> String_tagged_set.to_seq
        |> Seq.map Loc.content
      in
      let cells_defined_set =
        Cell_lifetime.Usage.defines_cells cell_usage
      in
      let cells_defined =
        cells_defined_set
        |> String_tagged_set.to_seq
        |> Seq.map Loc.content
      in
      let cell_subs = cell_subs_of_rule spec g k in
      let l = clean_up_l cell_subs ru.l in
      let a = clean_up_a cell_subs ru.a in
      let r, assigns =
        clean_up_r cell_subs ru.r
      in
      let is_root = Int_set.mem k roots in
      let l_facts_for_reads_and_assigns =
        if is_root then
          Seq.empty
        else
          Seq.map (fun c ->
              let ptr = pcell_ptr_of_cell c in
              T_unary_op (
                `Persist,
                T_app { path = Path.of_string "Pcell";
                        name = `Global 0;
                        named_args = [];
                        args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                                 T_var (Path.of_string ptr, `Global 0, Some `Fresh);
                                 T_value (Loc.untagged (`Str c));
                                 (match List.assoc_opt c cell_subs with
                                  | None -> 
                                    T_value (Loc.untagged (`Str "NULL"))
                                  | Some x -> x
                                 );
                               ];
                        anno = None;
                      }
              )
            )
            (Seq.append cells_required cells_defined)
      in
      let pcell_ptr_new =
        Fmt.str "%s_new" Params.pcell_ptr_prefix
      in
      let l_fresh_for_assigns =
        if String_tagged_set.is_empty cells_defined_set then
          Seq.empty
        else
          Seq.return (T_app { path = Path.of_string "Fr";
                              name = `Global 0;
                              named_args = [];
                              args = [
                                T_var 
                                  ( Path.of_string pcell_ptr_new,
                                    `Global 0,
                                    Some `Fresh
                                  )
                              ];
                              anno = None;
                            }
                     )
      in
      let a_facts_for_reads =
        if is_root then
          Seq.empty
        else
          Seq.map (fun c ->
              let ptr = pcell_ptr_of_cell c in
              T_app { path = Path.of_string Params.pcell_read_apred_name;
                      name = `Global 0;
                      named_args = [];
                      args = [T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                              T_var (Path.of_string ptr, `Global 0, Some `Fresh);
                              T_value (Loc.untagged (`Str c));
                             ];
                      anno = None;
                    }
            )
            cells_required
      in
      let a_facts_for_assigns =
        if is_root then
          Seq.empty
        else
          Seq.map (fun c ->
              let ptr = pcell_ptr_of_cell c in
              T_app { path = Path.of_string Params.pcell_freed_apred_name;
                      name = `Global 0;
                      named_args = [];
                      args = [T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                              T_var (Path.of_string ptr, `Global 0, Some `Fresh);
                              T_value (Loc.untagged (`Str c));
                             ];
                      anno = None;
                    }
            )
            cells_defined
      in
      let r_facts_for_assigns =
        if is_root then
          String_tagged_set.to_seq total_cells_required
          |> Seq.map Loc.content
          |> Seq.map (fun c ->
              T_unary_op (
                `Persist,
                T_app { path = Path.of_string "Pcell";
                        name = `Global 0;
                        named_args = [];
                        args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                                 T_var (Path.of_string pcell_ptr_new, `Global 0, Some `Fresh);
                                 T_value (Loc.untagged (`Str c));
                                 T_value (Loc.untagged (`Str "NULL"));
                               ];
                        anno = None;
                      }
              )
            )
        else
          Seq.map (fun (c, x) ->
              T_unary_op (
                `Persist,
                T_app { path = Path.of_string "Pcell";
                        name = `Global 0;
                        named_args = [];
                        args = [T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                                T_var (Path.of_string pcell_ptr_new, `Global 0, Some `Fresh);
                                T_value (Loc.untagged (`Str c));
                                x;
                               ];
                        anno = None;
                      }
              )
            )
            (List.to_seq assigns)
      in
      let l_st =
        if is_root then
          Seq.empty
        else
          Seq.return
            (T_app { path = Path.of_string "St";
                     name = `Global 0;
                     named_args = [];
                     args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                            ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k)))
                            ];
                     anno = None;
                   })
      in
      let l = Seq.concat (List.to_seq [
          l_st;
          l_fresh_for_assigns;
          l_facts_for_reads_and_assigns;
          List.to_seq l;
        ])
      in
      let a = Seq.concat (List.to_seq [
          a_facts_for_reads;
          a_facts_for_assigns;
          List.to_seq a;
        ])
      in
      let r_st =
        Seq.return
          (T_app { path = Path.of_string "St";
                   name = `Global 0;
                   named_args = [];
                   args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                          ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k')))
                          ];
                   anno = None;
                 })
      in
      let r = Seq.concat (List.to_seq [
          r_st;
          r_facts_for_assigns;
          List.to_seq r;
        ])
      in
      D_rule {
        binding =
          Binding.make
            (Loc.untagged @@ Fmt.str "TgRule%a_%dto%d"
               pp_name_of_proc binding k k')
            {
              l = List.of_seq l;
              vars_in_l = [];
              bindings_before_a = [];
              a = List.of_seq a;
              bindings_before_r = [];
              r = List.of_seq r;
            }
      }
    )

let end_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  Graph.leaves g
  |> Seq.map (fun k ->
      let ru = Graph.find k g in
      let cell_usage = Int_map.find k spec.cell_usages in
      let cells_required =
        Cell_lifetime.Usage.requires_cells cell_usage
        |> String_tagged_set.to_seq
        |> Seq.map Loc.content
      in
      let cell_subs = cell_subs_of_rule spec g k in
      let l = clean_up_l cell_subs ru.l in
      let a = clean_up_a cell_subs ru.a in
      let r, _assigns =
        clean_up_r cell_subs ru.r
      in
      let l_st =
        Seq.return
          (T_app { path = Path.of_string "St";
                   name = `Global 0;
                   named_args = [];
                   args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                          ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k)))
                          ];
                   anno = None;
                 })
      in
      let l_facts_for_reads =
        Seq.map (fun c ->
            let ptr = pcell_ptr_of_cell c in
            T_unary_op (
              `Persist,
              T_app { path = Path.of_string "Pcell";
                      name =`Global 0;
                      named_args = [];
                      args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                               T_var (Path.of_string ptr, `Global 0, Some `Fresh);
                               T_value (Loc.untagged (`Str c));
                               List.assoc c cell_subs
                             ];
                      anno = None;
                    }
            )
          )
          cells_required
      in
      let a_facts_for_reads =
        Seq.map (fun c ->
            let ptr = pcell_ptr_of_cell c in
            T_app { path = Path.of_string Params.pcell_read_apred_name;
                    name = `Global 0;
                    named_args = [];
                    args = [T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                            T_var (Path.of_string ptr, `Global 0, Some `Fresh);
                            T_value (Loc.untagged (`Str c));
                           ];
                    anno = None;
                  }
          )
          cells_required
      in
      let l = Seq.concat (List.to_seq [
          l_st;
          l_facts_for_reads;
          List.to_seq l;
        ])
      in
      let a = Seq.append a_facts_for_reads (List.to_seq a) in
      D_rule {
        binding =
          Binding.make
            (Loc.untagged @@ Fmt.str "TgEnd%a_%d" pp_name_of_proc binding k)
            {
              l = List.of_seq l;
              vars_in_l = [];
              bindings_before_a = [];
              a = List.of_seq a;
              bindings_before_r = [];
              r;
            }
      }
    )

let restriction =
  let open Tg_ast in
  D_restriction {
    binding =
      Binding.make (Loc.untagged Params.pcell_restriction_name)
        (
          T_quantified {
            loc = None;
            quantifier = `All;
            quant = [
              Binding.make (Loc.untagged "pid") `Bitstring;
              Binding.make (Loc.untagged Params.pcell_ptr_prefix) `Bitstring;
              Binding.make (Loc.untagged "cell") `Bitstring;
              Binding.make (Loc.untagged "i") `Temporal;
              Binding.make (Loc.untagged "j") `Temporal;
            ];
            formula =
              T_binary_op (
                `Imp,
                T_binary_op (
                  `And,
                  T_action {
                    fact = T_app { path = Path.of_string Params.pcell_read_apred_name;
                                   name = `Global 0;
                                   named_args = [];
                                   args = [ T_var (Path.of_string "pid", `Global 0, None);
                                            T_var (Path.of_string Params.pcell_ptr_prefix, `Global 0, None);
                                            T_var (Path.of_string "cell", `Global 0, None);
                                          ];
                                   anno = None;
                                 };
                    temporal = (Loc.untagged "i", `Global 0);
                  },
                  T_action {
                    fact = T_app { path = Path.of_string Params.pcell_freed_apred_name;
                                   name = `Global 0;
                                   named_args = [];
                                   args = [ T_var (Path.of_string "pid", `Global 0, None);
                                            T_var (Path.of_string Params.pcell_ptr_prefix, `Global 0, None);
                                            T_var (Path.of_string "cell", `Global 0, None);
                                          ];
                                   anno = None;
                                 };
                    temporal = (Loc.untagged "j", `Global 0);
                  }
                ),
                T_temporal_a_lt_b {
                  a = (Loc.untagged "i", `Global 0);
                  b = (Loc.untagged "j", `Global 0)
                }
              );
          }
        )
  }

