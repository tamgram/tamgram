open Result_let

let match_is_possible
    (possible_shapes : Cell_data_shape_set.t String_map.t)
    ((cell, b) : string Loc.tagged * Tg_ast.cell_data_shape)
  =
  String_map.find (Loc.content cell) possible_shapes
  |> Cell_data_shape_set.exists (fun a ->
      Cell_data_shape.compatible a b
    )

let check_matches
    (possible_shapes : Cell_data_shape_set.t String_map.t)
    matches =
  let rec aux matches =
    match matches with
    | [] -> Ok ()
    | (c, term, shape) :: xs ->
      if match_is_possible possible_shapes (c, shape) then
        aux xs
      else
        Error
          (Error_msg.make
             (Loc.tag c)
             (Fmt.str
                "Cell '%s never matches pattern %a" (Loc.content c) Printers.pp_term term
             )
          )
  in
  aux matches

let propagate_shape_until_assign_or_joining_lines
    (spec : Spec.t)
    (g : Tg_graph.t)
    (path : int list)
    (cell : string)
    (shape : Tg_ast.cell_data_shape)
  : Spec.t =
  let rec aux last_k
      (most_general_shape_store : Tg_ast.cell_data_shape String_map.t Int_map.t)
      path
    =
    match path with
    | [] -> most_general_shape_store
    | k :: ks ->
      let most_general_shape = Int_map.find k most_general_shape_store in
      let no_other_preds =
        match last_k with
        | None ->
          Int_set.is_empty (Graph.pred k g)
        | Some last_k ->
          Int_set.is_empty
            (Int_set.remove last_k (Graph.pred k g))
      in
      let at_start_of_provided_path =
        Option.is_none last_k
      in
      let most_general_shape =
        if at_start_of_provided_path || no_other_preds then
          String_map.add cell shape most_general_shape
        else
          most_general_shape
      in
      let most_general_shape_store =
        Int_map.add k most_general_shape
          most_general_shape_store
      in
      let cell_is_assigned_again =
        String_tagged_set.mem (Loc.untagged cell)
          (Cell_lifetime.Usage.defines_cells
             (Int_map.find k spec.cell_usages))
      in
      let keep_going =
        no_other_preds
        && not cell_is_assigned_again
      in
      if keep_going then
        aux (Some k) most_general_shape_store ks
      else
        most_general_shape_store
  in
  let cell_data_most_general_shape =
    aux None spec.cell_data_most_general_shape path
  in
  { spec with cell_data_most_general_shape }

let perform_subs_on_rule (spec : Spec.t) (proc_name : Name.t) g (k : int) subs : Spec.t =
  let open Tg_ast in
  let subs =
    Name_map.to_seq subs
    |> Seq.map (fun (name, x) ->
        (name, Cell_data_shape.to_term x))
    |> List.of_seq
  in
  let ru = Graph.find k g in
  let f_sub = Term.sub ~loc:None subs in
  let ru = { ru with
             l = List.map f_sub ru.l;
             a = List.map f_sub ru.a;
             r = List.map f_sub ru.r;
           }
  in
  let g =
    Graph.add_vertex_with_id k ru g
  in
  Spec.{
    spec with
    proc_graphs =
      Name_map.add proc_name g spec.proc_graphs
  }

let perform_subs_on_most_general_shape_store (spec : Spec.t) g subs : Spec.t =
  Seq.fold_left (fun spec (k, _) ->
      let most_general_shape_store =
        Int_map.find k Spec.(spec.cell_data_most_general_shape)
        |> String_map.map (fun shape ->
            Cell_data_shape.sub subs shape
          )
      in
      Spec.{
        spec with
        cell_data_most_general_shape =
          Int_map.add k most_general_shape_store spec.cell_data_most_general_shape;
      }
    )
    spec
    (Graph.vertex_seq g)

let aux_path
    (spec : Spec.t)
    (proc_name : Name.t)
    (path : int list)
  : (Spec.t, Error_msg.t) result =
  let rec aux spec path =
    match path with
    | [] -> Ok spec
    | k :: ks ->
      let g = Name_map.find proc_name Spec.(spec.proc_graphs) in
      let most_general_shape_store =
        Int_map.find k Spec.(spec.cell_data_most_general_shape)
      in
      let matches =
        Int_map.find k spec.user_specified_cell_pat_matches
        |> List.map (fun (cell, term) ->
            (cell, term, Cell_data_shape.of_term most_general_shape_store term))
      in
      let* () =
        if !Params.analyze_possible_cell_data_shapes then (
          let possible_shapes =
            Int_map.find k Spec.(spec.cell_data_possible_shapes)
          in
          check_matches possible_shapes matches
        )
        else
          Ok ()
      in
      let spec =
        if !Params.use_most_general_cell_data_shape then (
          List.fold_left (fun spec (cell, _term, shape) ->
              let cell = Loc.content cell in
              let most_general_shape =
                String_map.find cell most_general_shape_store
              in
              if Cell_data_shape.a_covers_b ~a:shape ~b:most_general_shape then (
                let subs =
                  Cell_data_shape.subs_for_a_to_become_b ~a:shape
                    ~b:most_general_shape
                in
                let spec = perform_subs_on_rule spec proc_name g k subs in
                perform_subs_on_most_general_shape_store spec g subs
              ) else (
                propagate_shape_until_assign_or_joining_lines spec g path cell shape
              )
            )
            spec
            matches
        ) else
          spec
      in
      aux spec ks
  in
  aux spec path

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let rec aux_paths spec proc_name (s : int list Seq.t) =
    match s () with
    | Seq.Nil -> Ok spec
    | Seq.Cons (path, rest) ->
      let* spec = aux_path spec proc_name path in
      aux_paths spec proc_name rest
  in
  let rec aux spec (s : (Name.t * Tg_graph.t) Seq.t) =
    match s () with
    | Seq.Nil -> Ok spec
    | Seq.Cons ((proc_name, g), rest) ->
      let* spec =
        aux_paths spec proc_name
          (Graph.paths_from_roots ~max_loop_count:2 g)
      in
      aux spec rest
  in
  aux spec (Name_map.to_seq spec.proc_graphs)
