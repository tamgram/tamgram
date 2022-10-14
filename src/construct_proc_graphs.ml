open Result_infix

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  let proc_graphs = ref Name_map.empty in
  let rule_tags = ref Int_map.empty in
  let rec aux (decls : decl list) =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process { binding } ->
          let+ g, tags = Tg_graph.of_proc (Binding.get binding) in
          proc_graphs :=
            Name_map.add (Binding.name binding) g !proc_graphs;
          rule_tags :=
            Int_map.union (fun _ _ _ -> failwith "Unexpected case") !rule_tags tags
        | D_rule { binding } ->
          let proc =
            P_line { tag = None; rule = Binding.get binding; next = P_null }
          in
          let+ g, tags = Tg_graph.of_proc proc in
          proc_graphs :=
            Name_map.add (Binding.name binding) g !proc_graphs;
          rule_tags :=
            Int_map.union (fun _ _ _ -> failwith "Unexpected case") !rule_tags tags
        | D_modul (_, decls) ->
          aux decls
        | _ -> Ok ()
      in
      aux ds
  in
  let+ () = aux spec.root in
  {
    spec with
    proc_graphs = !proc_graphs;
    rule_tags = !rule_tags;
  }
