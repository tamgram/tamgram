let make_args_untagged (l : string list) : Tg_ast.term list =
  let open Tg_ast in
  l
  |> List.sort_uniq String.compare
  |> List.map (fun name -> T_symbol (Loc.untagged name, `Cell))

let make_args (s : String_tagged_set.t) : Tg_ast.term list =
  String_tagged_set.to_list s |> List.map Loc.content |> make_args_untagged

let make_state_fact name args : Tg_ast.term =
  T_app
    ( [ Loc.untagged (Printf.sprintf "%s%s" Params.state_pred_prefix name) ],
      `Global (Update_node_ids.get_new_node_id ()),
      args )

let make_line_rule ~carryover ~next_carryover base_rule =
  let open Tg_ast in
  let { l; vars_in_l; bindings_before_a; a; bindings_before_r; r } =
    base_rule
  in
  let l = match carryover with None -> l | Some x -> x :: l in
  let r = next_carryover :: r in
  { l; vars_in_l; bindings_before_a; a; bindings_before_r; r }

let aux_proc (to_appear_after : String_tagged_set.t Int_map.t)
    (proc : Tg_ast.proc) : Tg_ast.proc =
  let open Tg_ast in
  let rec aux (carryover : term option) (add_to_r_end : term option) proc =
    match proc with
    | P_null -> (
        match add_to_r_end with
        | None -> P_null
        | Some add_to_r_end ->
          let rule =
            {
              l = (match carryover with None -> [] | Some x -> [ x ]);
              vars_in_l = [];
              bindings_before_a = [];
              a = [];
              bindings_before_r = [];
              r = [ add_to_r_end ];
            }
          in
          P_line (Update_node_ids.get_new_node_id (), rule, P_null))
    | P_goto _ -> P_null
    | P_let _ | P_let_macro _ | P_scoped _ ->
      failwith "Unexpected case"
    | P_entry_point { node_id; name; next } -> (
        let next_carryover =
          make_state_fact
            (Printf.sprintf "From%d" node_id)
            (make_args (Int_map.find node_id to_appear_after))
        in
        let default_rule =
          make_line_rule ~carryover ~next_carryover
            {
              l = [];
              vars_in_l = [];
              bindings_before_a = [];
              a = [];
              bindings_before_r = [];
              r = [];
            }
        in
        let cells_required =
          Int_map.find node_id to_appear_after
          |> String_tagged_set.to_list
          |> List.map Loc.content
        in
        match
          Hashtbl.find_opt Cell_lifetime_analysis_loops.entry_point_names
            node_id
        with
        | None ->
          P_line
            ( Update_node_ids.get_new_node_id (),
              default_rule,
              aux (Some next_carryover) add_to_r_end next )
        | Some pred_name ->
          let entry_point_rule =
            let vars =
              List.mapi
                (fun i x -> T_var ([ Loc.untagged x ], `Local i, None))
                cells_required
            in
            {
              l =
                [
                  T_app
                    ( [
                      Loc.untagged
                        (Fmt.str "%s%s%d" Params.entry_point_pred_prefix
                           (Loc.content name) node_id);
                    ],
                      pred_name,
                      vars );
                ];
              vars_in_l =
                List.mapi
                  (fun i x ->
                     Binding.make ~name:(`Local i) (Loc.untagged x) `Bitstring)
                  cells_required;
              bindings_before_a = [];
              a = [];
              bindings_before_r = [];
              r =
                next_carryover
                :: List.mapi
                  (fun i x ->
                     T_cell_assign
                       ( Loc.untagged x,
                         T_var ([ Loc.untagged x ], `Local i, None) ))
                  cells_required;
            }
          in
          P_line
            ( Update_node_ids.get_new_node_id (),
              default_rule,
              P_line
                ( Update_node_ids.get_new_node_id (),
                  entry_point_rule,
                  aux (Some next_carryover) add_to_r_end next ) ))
    | P_line (node_id, rule, next) ->
      let next_carryover =
        make_state_fact
          (Printf.sprintf "From%d" node_id)
          (make_args (Int_map.find node_id to_appear_after))
      in
      let rule = make_line_rule ~carryover ~next_carryover rule in
      P_line (node_id, rule, aux (Some next_carryover) add_to_r_end next)
    | P_branch (node_id, procs, next) ->
      let to_appear_after_branch = Int_map.find node_id to_appear_after in
      let carryover_for_procs = carryover in
      let add_to_r_end' =
        make_state_fact
          (Printf.sprintf "EndOfChoice%d" node_id)
          (make_args to_appear_after_branch)
      in
      let carryover_for_next = add_to_r_end' in
      let procs =
        List.map (aux carryover_for_procs (Some add_to_r_end')) procs
      in
      P_branch
        (node_id, procs, aux (Some carryover_for_next) add_to_r_end next)
  in
  aux None None proc

let aux_modul (to_appear_after : String_tagged_set.t Int_map.t)
    (decls : Tg_ast.modul) : Tg_ast.modul =
  let open Tg_ast in
  let rec aux acc decls =
    match decls with
    | [] -> List.rev acc
    | d :: ds ->
      let d =
        match d with
        | D_process { node_id; binding } ->
          D_process
            {
              node_id;
              binding = Binding.map (aux_proc to_appear_after) binding;
            }
        | D_fun _ | D_pred _ | D_apred _ | D_equation _ | D_lemma _
        | D_restriction _ | D_rule _ | D_open _ | D_insert _ ->
          d
        | D_let _ | D_macro _ -> failwith "Unexpected case"
        | D_modul (name, m) -> D_modul (name, aux [] m)
      in
      aux (d :: acc) ds
  in
  aux [] decls

let map_spec (spec : Spec.t) : (Spec.t, string) result =
  Ok { spec with root = aux_modul spec.cells_to_appear_after spec.root }
