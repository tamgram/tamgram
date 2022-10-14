open Tr_utils

let start_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  Graph.roots g
  |> Seq.map (fun k ->
      let ru = Graph.find k g in
      let cells_to_carry_over_after =
        Int_map.find k spec.cells_to_carry_over_after
      in
      let cell_subs = cell_subs_of_rule spec g k in
      let l = clean_up_l cell_subs ru.l in
      let a = clean_up_a cell_subs ru.a in
      let r, assigns =
        clean_up_r cell_subs ru.r
      in
      let frame_r =
        String_tagged_set.to_seq cells_to_carry_over_after
        |> Seq.map (fun c ->
            List.assoc (Loc.content c) (assigns @ cell_subs)
          )
        |> List.of_seq
      in
      let r =
        T_app (Path.of_string "St", `Global 0,
               [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
               ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k)))
               ; T_tuple (None, frame_r)
               ],
               None)
        ::
        r
      in
      D_rule {
        binding =
          Binding.make
            (Loc.untagged @@ Fmt.str "TgStart%a_%d" pp_name_of_proc binding k)
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

let rule_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  let leaves = Int_set.of_seq @@ Graph.leaves g in
  Graph.edge_seq g
  |> Seq.map (fun (pred', k) ->
      let ru = Graph.find k g in
      let cells_to_carry_over_after_pred =
        Int_map.find pred' spec.cells_to_carry_over_after
      in
      let cells_to_carry_over_after =
        Int_map.find k spec.cells_to_carry_over_after
      in
      let cell_subs = cell_subs_of_rule spec g k in
      let l = clean_up_l cell_subs ru.l in
      let a = clean_up_a cell_subs ru.a in
      let r, assigns =
        clean_up_r cell_subs ru.r
      in
      let frame_l =
        String_tagged_set.to_seq cells_to_carry_over_after_pred
        |> Seq.map (fun c ->
            List.assoc (Loc.content c) cell_subs
          )
        |> List.of_seq
      in
      let frame_r =
        String_tagged_set.to_seq cells_to_carry_over_after
        |> Seq.map (fun c ->
            List.assoc (Loc.content c) (assigns @ cell_subs)
          )
        |> List.of_seq
      in
      let l =
        T_app (Path.of_string "St", `Global 0,
               [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
               ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix pred')))
               ; T_tuple (None, frame_l)
               ],
               None)
        ::
        l
      in
      let r =
        if Int_set.mem k leaves then
          r
        else
          T_app (Path.of_string "St", `Global 0,
                 [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                 ; T_value (Loc.untagged
                              (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k)))
                 ; T_tuple (None, frame_r)
                 ],
                 None)
          ::
          r
      in
      D_rule {
        binding =
          Binding.make
            (Loc.untagged @@ Fmt.str "TgRule%a_%dto%d"
               pp_name_of_proc binding pred' k)
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

