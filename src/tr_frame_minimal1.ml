open Tr_utils

let rule_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  let roots = Int_set.of_seq @@ Graph.roots g in
  let state_preds_to_add = ref Int_map.empty in
  let rules =
    Graph.edge_seq g
    |> Seq.map (fun (k, k') ->
        let ru = Graph.find k g in
        let cells_to_carry_over_before =
          Int_map.find k spec.cells_to_carry_over_before
        in
        let cells_to_carry_over_before_succ =
          Int_map.find k' spec.cells_to_carry_over_before
        in
        let cell_subs = cell_subs_of_rule spec g k in
        let l = clean_up_l cell_subs ru.l in
        let a = clean_up_a cell_subs ru.a in
        let r, assigns =
          clean_up_r cell_subs ru.r
        in
        let frame_l =
          String_tagged_set.to_seq cells_to_carry_over_before
          |> Seq.map (fun c ->
              List.assoc (Loc.content c) cell_subs
            )
          |> List.of_seq
        in
        let frame_r =
          String_tagged_set.to_seq cells_to_carry_over_before_succ
          |> Seq.map (fun c ->
              List.assoc (Loc.content c) (assigns @ cell_subs)
            )
          |> List.of_seq
        in
        let l =
          if Int_set.mem k roots then
            l
          else (
            T_app { path = Path.of_string (Fmt.str "%s%d" Params.state_pred_prefix k);
                    name = `Global 0;
                    named_args = [];
                    args = T_var (Path.of_string "pid", `Global 0, Some `Fresh) :: frame_l;
                    anno = None;
                  }
            ::
            l
          )
        in
        let r =
          T_app { path = Path.of_string (Fmt.str "%s%d" Params.state_pred_prefix k');
                  name = `Global 0;
                  named_args = [];
                  args = T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                         :: frame_r;
                  anno = None;
                }
          ::
          r
        in
        state_preds_to_add := Int_map.add k' (1 + List.length frame_r) !state_preds_to_add;
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
                r;
              }
        }
      )
    |> List.of_seq
  in
  Seq.append
    (Seq.map (fun (k, size) ->
         D_fun (Binding.make (Loc.untagged @@ Fmt.str "%s%d" Params.state_pred_prefix k) size))
        (Int_map.to_seq !state_preds_to_add))
    (List.to_seq rules)

let end_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  Graph.leaves g
  |> Seq.map (fun k ->
      let ru = Graph.find k g in
      let cells_to_carry_over_before =
        Int_map.find k spec.cells_to_carry_over_before
      in
      let cell_subs = cell_subs_of_rule spec g k in
      let l = clean_up_l cell_subs ru.l in
      let a = clean_up_a cell_subs ru.a in
      let r, _assigns =
        clean_up_r cell_subs ru.r
      in
      let frame_l =
        String_tagged_set.to_seq cells_to_carry_over_before
        |> Seq.map (fun c ->
            List.assoc (Loc.content c) cell_subs
          )
        |> List.of_seq
      in
      let l =
        T_app { path = Path.of_string (Fmt.str "%s%d" Params.state_pred_prefix k);
                name = `Global 0;
                named_args = [];
                args = T_var (Path.of_string "pid", `Global 0, Some `Fresh) :: frame_l;
                anno = None;
              }
        ::
        l
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

