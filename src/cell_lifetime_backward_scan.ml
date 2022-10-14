let add_to_store (k : int) (s : String_tagged_set.t) (m : String_tagged_set.t Int_map.t) =
  match Int_map.find_opt k m with
  | None ->
    Int_map.add k s m
  | Some s' ->
    Int_map.add k (String_tagged_set.union s s') m

let ctx_required_for_path
    (spec : Spec.t)
    (m : String_tagged_set.t Int_map.t)
    (path : int list)
  : String_tagged_set.t Int_map.t =
  let rec aux cells_needed_later m path =
    match path with
    | [] -> m
    | k :: ks ->
      let usage = Int_map.find k spec.cell_usages in
      let cells_needed_including_current =
        String_tagged_set.union
          (String_tagged_set.diff
             cells_needed_later
             (Cell_lifetime.Usage.defines_cells usage))
          (Cell_lifetime.Usage.requires_cells usage)
      in
      let m =
        add_to_store k cells_needed_including_current m
      in
      aux cells_needed_including_current m ks
  in
  aux String_tagged_set.empty m (List.rev path)

let aux_process_graph
    spec
    m_before
    m_after
    (g : Tg_graph.t)
  =
  let m_before =
    Graph.vertex_seq g
    |> Seq.flat_map (fun (id, _ru) ->
        Graph.paths_from_id ~max_loop_count:0 id g
      )
    |> Seq.fold_left (fun m_before path ->
        ctx_required_for_path spec m_before path
      )
      m_before
  in
  let m_after =
    Graph.vertex_seq g
    |>
    Seq.fold_left (fun m_after (id, _ru) ->
        let ctx_required_afterward =
          Graph.succ_seq id g
          |> Seq.map (fun id' ->
              Int_map.find id' m_before
            )
          |> Seq.fold_left String_tagged_set.union String_tagged_set.empty
        in
        Int_map.add id ctx_required_afterward m_after
      )
      m_after
  in
  (m_before, m_after)

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let cells_to_carry_over_before, cells_to_carry_over_after =
    Seq.fold_left (fun (m_before, m_after) (_proc_name, g) ->
        aux_process_graph spec m_before m_after g
      )
      (Int_map.empty, Int_map.empty)
      (Name_map.to_seq spec.proc_graphs)
  in
  Ok Spec.{
      spec with
      cells_to_carry_over_before;
      cells_to_carry_over_after;
    }
