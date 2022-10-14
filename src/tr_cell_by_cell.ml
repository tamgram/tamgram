open Tr_utils

let l_and_cell_subs_of_rule (roots : Int_set.t) (k : int) (binding : Tg_ast.proc Binding.t) (spec : Spec.t)
  : Tg_ast.term list * (string * Tg_ast.term) list =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  let ru = Graph.find k g in
  let cell_usage = Int_map.find k spec.cell_usages in
  let required_cells =
    Cell_lifetime.Usage.requires_cells cell_usage
    |> String_tagged_set.to_seq
    |> Seq.map Loc.content
    |> List.of_seq
  in
  let cell_subs = cell_subs_of_rule spec g k in
  let l = clean_up_l cell_subs ru.l in
  if Int_set.mem k roots then
    (l, cell_subs)
  else
    (T_app (Path.of_string "St", `Global 0,
            [T_var (Path.of_string "pid", `Global 0, Some `Fresh);
             T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k)));
            ],
            None)
     ::
     List.map (fun c ->
         T_app (Path.of_string "Cell", `Global 0,
                [T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                 T_value (Loc.untagged (`Str c));
                 List.assoc c cell_subs;
                ],
                None)
       )
       required_cells
     @
     l,
     cell_subs)

let rule_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  let roots = Int_set.of_seq @@ Graph.roots g in
  Graph.edge_seq g
  |> Seq.map (fun (k, k') ->
      let ru = Graph.find k g in
      let l, cell_subs = l_and_cell_subs_of_rule roots k binding spec in
      let cell_usage = Int_map.find k spec.cell_usages in
      let cells_required =
        Cell_lifetime.Usage.requires_cells cell_usage
      in
      let cells_undefined =
        Cell_lifetime.Usage.undefines_cells cell_usage
      in
      let cells_defined =
        Cell_lifetime.Usage.defines_cells cell_usage
      in
      let leftover_cells =
        String_tagged_set.(
          diff
            (diff cells_required cells_undefined)
            cells_defined
        )
        |> String_tagged_set.to_seq
        |> Seq.map Loc.content
        |> List.of_seq
      in
      let a = clean_up_a cell_subs ru.a in
      let r, assigns =
        clean_up_r cell_subs ru.r
      in
      let facts_for_leftover_cells =
        List.map (fun c ->
            T_app (Path.of_string "Cell", `Global 0,
                   [ T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                     T_value (Loc.untagged (`Str c));
                     List.assoc c cell_subs;
                   ],
                   None
                  )
          ) leftover_cells
      in
      let facts_for_assigns =
        List.map (fun (c, x) ->
            T_app (Path.of_string "Cell", `Global 0,
                   [T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                    T_value (Loc.untagged (`Str c));
                    x;
                   ],
                   None)
          )
          assigns
      in
      D_rule {
        binding =
          Binding.make
            (Loc.untagged @@ Fmt.str "TgRule%a_%dto%d"
               pp_name_of_proc binding k k')
            {
              l;
              vars_in_l = [];
              bindings_before_a = [];
              a;
              bindings_before_r = [];
              r =
                T_app (Path.of_string "St", `Global 0,
                       [T_var (Path.of_string "pid", `Global 0, Some `Fresh);
                        T_value (Loc.untagged
                                   (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k')));
                       ],
                       None)
                ::
                List.flatten [
                  facts_for_leftover_cells;
                  facts_for_assigns;
                  r;
                ]
              ;
            }
      }
    )

let end_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  let roots = Int_set.of_seq @@ Graph.roots g in
  Graph.leaves g
  |> Seq.map (fun k ->
      let ru =
        Graph.find k g
      in
      let l, cell_subs = l_and_cell_subs_of_rule roots k binding spec in
      let a = clean_up_a cell_subs ru.a in
      let r, _assigns =
        clean_up_r cell_subs ru.r
      in
      D_rule {
        binding =
          Binding.make
            (Loc.untagged @@ Fmt.str "TgEnd%a_%d" pp_name_of_proc binding k)
            {
              l;
              vars_in_l = [];
              bindings_before_a = [];
              a;
              bindings_before_r = [];
              r;
            }
      }
    )

