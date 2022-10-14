let aux_path
    (g : Tg_graph.t)
    (path : int list)
  : (int * Tg_ast.cell_data_shape String_map.t) list =
  let open Tg_ast in
  let rec aux
      (known_shapes : Tg_ast.cell_data_shape String_map.t)
      (acc : (int * Tg_ast.cell_data_shape String_map.t) list)
      path
    =
    match path with
    | [] -> List.rev acc
    | k :: ks ->
      let ru = Graph.find k g in
      let new_shapes =
        ru.r
        |> List.to_seq
        |> Seq.filter_map (fun x ->
            match x with
            | T_cell_assign (cell, x) ->
              Some (Loc.content cell, x)
            | _ -> None
          )
        |> Seq.map (fun (cell, x) ->
            let s =
              if !Params.analyze_possible_cell_data_shapes then
                Cell_data_shape.of_term known_shapes x
              else
                let name_str, name = Lexical_ctx.fresh_local_name () in
                S_var (name_str, name)
            in
            (cell, s)
          )
      in
      let new_known_shapes =
        Seq.fold_left (fun known_shapes (cell, shape) ->
            String_map.add cell shape known_shapes
          )
          known_shapes
          new_shapes
      in
      aux new_known_shapes ((k, known_shapes) :: acc) ks
  in
  aux String_map.empty [] path

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let step_and_shapes : (int * Tg_ast.cell_data_shape String_map.t) Seq.t =
    Seq.flat_map (fun (_name, g) ->
        let paths = Graph.paths_from_roots ~max_loop_count:2 g in
        Seq.flat_map (fun path ->
            List.to_seq
              (aux_path g path))
          paths
      )
      (Name_map.to_seq spec.proc_graphs)
  in
  let cell_data_most_general_shape =
    step_and_shapes
    |> Seq.fold_left (fun m (k, known_shapes) ->
        let known_shapes : Tg_ast.cell_data_shape String_map.t =
          match Int_map.find_opt k m with
          | None -> known_shapes
          | Some known_shapes' ->
            String_map.union (fun _cell shape1 shape2 ->
                Some (Cell_data_shape.common_part shape1 shape2))
              known_shapes known_shapes'
        in
        Int_map.add k known_shapes m
      )
      Int_map.empty
  in
  let cell_data_possible_shapes =
    step_and_shapes
    |> Seq.map (fun (k, known_shapes) ->
        (k,
         String_map.map (fun x ->
             Cell_data_shape_set.(add x empty)
           )
           known_shapes
        )
      )
    |> Seq.fold_left (fun m (k, possible_shapes) ->
        let possible_shapes =
          match Int_map.find_opt k m with
          | None -> possible_shapes
          | Some possible_shapes' ->
            String_map.union (fun _cell s1 s2 ->
                Some (Cell_data_shape_set.union s1 s2))
              possible_shapes possible_shapes'
        in
        Int_map.add k possible_shapes m
      )
      Int_map.empty
  in
  Ok {
    spec with
    cell_data_most_general_shape; 
    cell_data_possible_shapes;
  }
