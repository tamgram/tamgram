let normalize_matches
    (matches : (string Loc.tagged * Tg_ast.term) list)
  =
  let rec aux
      (cell_free_matches : (string Loc.tagged * Tg_ast.term) list)
      matches
    =
    match matches with
    | [] -> cell_free_matches
    | _ ->
      let cell_free_matches', matches =
        List.partition (fun (_, t) ->
            String_tagged_set.is_empty (Term.cells_in_term t))
          matches
      in
      match cell_free_matches' with
      | [] ->
        cell_free_matches @ matches
      | _ ->
        let cell_free_matches =
          cell_free_matches' @ cell_free_matches
        in
        let matches =
          List.map (fun (c, t) ->
              (c,
               Term.replace_cells_in_term
                 (List.map (fun (cell, x) -> (Loc.content cell, x)) cell_free_matches) t
              ))
            matches
        in
        aux cell_free_matches matches
  in
  aux [] matches

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  Seq.fold_left (fun spec (proc_name, g) ->
      let g, user_specified_cell_pat_matches =
        Seq.fold_left (fun (g, user_specified_cell_pat_matches) (k, ru) ->
            let matches, l =
              List.partition_map (fun x ->
                  match x with
                  | T_cell_pat_match (name, y) ->
                    Left (name, y)
                  | _ ->
                    Right x
                )
                ru.l
            in
            let matches = normalize_matches matches in
            let ru = { ru with l } in
            (Graph.add_vertex_with_id k ru g,
             Int_map.add k matches
               user_specified_cell_pat_matches
            )
          )
          (g, Spec.(spec.user_specified_cell_pat_matches))
          (Graph.vertex_seq g)
      in
      Spec.{
        spec with
        proc_graphs = Name_map.add proc_name g spec.proc_graphs;
        user_specified_cell_pat_matches;
      }
    )
    spec
    (Name_map.to_seq spec.proc_graphs)
  |> Result.ok
