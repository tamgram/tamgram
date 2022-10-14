open Result_infix

type t = Tg_ast.rule Graph.t

let link_backward ~(last_ids : int list) (id : int) (g : t) =
  List.fold_left (fun g x ->
      Graph.add_edge (x, id) g
    )
    g last_ids

let empty_rule =
  Tg_ast.{ l = [];
           vars_in_l = [];
           bindings_before_a = [];
           a = [];
           bindings_before_r = [];
           r = [];
         }

let normalize_rule_tag (s : string) =
  CCString.map (fun c ->
      match c with
      | 'A' .. 'Z'
      | 'a' .. 'z'
      | '0' .. '9'
      | '_'
        -> c
      | _ -> '_'
    ) s

let of_proc (proc : Tg_ast.proc) : (t * string Int_map.t, Error_msg.t) result =
  let tags : string Int_map.t ref = ref Int_map.empty in
  let rec aux
      (entry_points : int String_map.t) (last_ids : int list) (g : t) (proc : Tg_ast.proc)
    : (int String_map.t * t, Error_msg.t) result =
    let open Tg_ast in
    match proc with
    | P_null -> Ok (entry_points, g)
    | P_goto { dest } ->
      let id = Graph.get_id () in
      let entry_point_id =
        String_map.find (Loc.content dest) entry_points
      in
      let g =
        g
        |> link_backward ~last_ids id
        |> Graph.add_vertex_with_id id empty_rule
        |> Graph.add_edge (id, entry_point_id)
      in
      Ok (entry_points, g)
    | P_let _
    | P_let_macro _
    | P_scoped _
    | P_app _
      -> failwith "Unexpected case"
    | P_entry_point { name; next; } ->
      let id = Graph.get_id () in
      let g =
        g
        |> link_backward ~last_ids id
        |> Graph.add_vertex_with_id id empty_rule
      in
      aux (String_map.add (Loc.content name) id entry_points) [id] g next
    | P_line { tag; rule; next } ->
      let id = Graph.get_id () in
      (match tag with
       | None -> ()
       | Some tag -> tags := Int_map.add id (normalize_rule_tag @@ Loc.content tag) !tags
      );
      let g =
        g
        |> link_backward ~last_ids id
        |> Graph.add_vertex_with_id id rule
      in
      aux entry_points [id] g next
    | P_branch (loc, procs, next) -> (
        let* entry_points_and_gs =
          aux_list entry_points last_ids g [] procs
        in
        let entry_points, gs =
          List.split entry_points_and_gs
        in
        let entry_points =
          List.fold_left (fun acc e ->
              String_map.union (fun _k x y ->
                  assert (x = y);
                  Some x
                )
                acc
                e
            )
            String_map.empty
            entry_points
        in
        let last_ids =
          CCList.flat_map (fun g ->
              Graph.leaves g
              |> List.of_seq
            )
            gs
        in
        let g = List.fold_left (fun acc x -> Graph.union acc x) Graph.empty gs in
        let default () =
          aux entry_points last_ids g next
        in
        match last_ids with
        | [] -> (
            match next with
            | P_null ->
              aux entry_points last_ids g next
            | _ ->
              Error (
                Error_msg.make
                  loc
                  "the process after choice here is not reachable"
              )
          )
        | [_] -> default ()
        | _ -> (
            match next with
            | P_branch _ ->
              if !Params.merge_branches then (
                let id = Graph.get_id () in
                let g =
                  g
                  |> link_backward ~last_ids id
                  |> Graph.add_vertex_with_id id empty_rule
                in
                aux entry_points [id] g next
              )
              else (
                default ()
              )
            | _ -> default ()
          )
      )
  and aux_list entry_points last_ids g acc procs =
    match procs with
    | [] -> Ok (List.rev acc)
    | p :: ps ->
      let* p = aux entry_points last_ids g p in
      aux_list entry_points last_ids g (p :: acc) ps
  in
  let+ _, g = aux String_map.empty [] Graph.empty proc in
  (g, !tags)
