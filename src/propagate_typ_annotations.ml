let fill_in_typ_annotations_for_term (typ_ctx : Typ.Ctx.t) (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ | T_symbol _ -> term
    | T_cell_assign (cell, x) ->
      T_cell_assign (cell, aux x)
    | T_cell_pat_match _
    | T_name_as _
    | T_let _
    | T_let_macro _
    | T_temporal_a_lt_b _
    | T_temporal_eq _
    | T_action _
    | T_quantified _ ->
      failwith "Unexpected case"
    | T_var (path, name, _) ->
        Fmt.pf "name: %a" pp_name name;
      T_var (path, name,
             Some (CCOption.get_exn_or
                     (Fmt.str "Unexpected failure in type lookup for %a" Printers.pp_path path)
                     (Typ.Ctx.find name typ_ctx)))
    | T_tuple (loc, l) -> T_tuple (loc, List.map aux l)
    | T_app (path, name, args, anno) ->
      T_app (path, name, List.map aux args, anno)
    | T_unary_op (op, x) ->
      T_unary_op (op, aux x)
    | T_binary_op (op, x, y) ->
      T_binary_op (op, aux x, aux y)
  in
  aux term

let aux_rule (ru : Tg_ast.rule) : Tg_ast.rule =
  let open Tg_ast in
  let typ_ctx =
    List.fold_left
      (fun typ_ctx x ->
         Typ.Ctx.add (Binding.name x) (Binding.get x) typ_ctx)
      Typ.Ctx.empty ru.vars_in_l
  in
  { ru with
    a = List.map (fill_in_typ_annotations_for_term typ_ctx) ru.a;
    r = List.map (fill_in_typ_annotations_for_term typ_ctx) ru.r;
  }

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  Seq.fold_left (fun spec (proc_name, g) ->
      let g = Graph.map aux_rule g in
      Spec.{
        spec with
        proc_graphs = Name_map.add proc_name g spec.proc_graphs;
      }
    )
    spec
    (Name_map.to_seq spec.proc_graphs)
  |> Result.ok
