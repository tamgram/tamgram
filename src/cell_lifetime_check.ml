open Result_infix

let check_path
    (spec : Spec.t)
    (well_defined_cells : String_tagged_set.t Int_map.t ref)
    (path : int list)
  : (unit, Error_msg.t) result =
  let rec aux ctx (path : int list) =
    match path with
    | [] -> Ok ()
    | x :: xs ->
      let usage = Int_map.find x spec.cell_usages in
      match Cell_lifetime.check_usage_is_satisfied ctx usage with
      | Ok () ->
        let defined_cells =
          Cell_lifetime.Ctx.defined_cells ctx
        in
        (match Int_map.find_opt x !well_defined_cells with
         | None ->
           well_defined_cells := Int_map.add x defined_cells !well_defined_cells
         | Some s ->
           well_defined_cells :=
             Int_map.add x (String_tagged_set.inter s defined_cells) !well_defined_cells
        );
        aux (Cell_lifetime.Ctx.update_from_usage usage ctx) xs
      | Error unsat_cell ->
        Error
          (Error_msg.make
             (Loc.tag unsat_cell)
             (Fmt.str "Cell '%s may not be well defined here"
                (Loc.content unsat_cell)))
  in
  aux Cell_lifetime.Ctx.empty path

let check_process_graph
    spec
    (well_defined_cells : String_tagged_set.t Int_map.t ref)
    (g : Tg_graph.t)
  : (unit, Error_msg.t) result =
  let rec aux (paths : int list Seq.t) =
    match paths () with
    | Seq.Nil -> Ok ()
    | Seq.Cons (path, rest) ->
      let* () = check_path spec well_defined_cells path in
      aux rest
  in
  aux (Graph.paths_from_roots ~max_loop_count:2 g)

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let well_defined_cells = ref Int_map.empty in
  let rec aux decls =
    let open Tg_ast in
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process { binding } ->
          let g = Name_map.find (Binding.name binding) spec.proc_graphs in
          check_process_graph spec well_defined_cells g
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_equation _ | D_lemma _
        | D_restriction _ | D_rule _ | D_open _ | D_insert _ ->
          Ok ()
        | D_process_macro _
        | D_let _ | D_macro _ -> failwith "Unexpected case"
        | D_modul (_, m) -> aux m
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux ds
  in
  let+ () = aux spec.root in
  { spec with
    well_defined_cells = !well_defined_cells
  }
