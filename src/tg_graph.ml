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
      (last_ids : int list) (g : t) (proc : Tg_ast.proc)
    : (t, Error_msg.t) result =
    let open Tg_ast in
    match proc with
    | P_null -> Ok g
    | P_let _
    | P_let_macro _
    | P_scoped _
    | P_app _
      -> failwith "Unexpected case"
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
      aux [id] g next
    | P_branch (loc, procs, next) -> (
        let* gs =
          aux_list last_ids Graph.empty [] procs
        in
        let last_ids =
          CCList.flat_map (fun g ->
              Graph.leaves g
              |> List.of_seq
            )
            gs
        in
        let g = List.fold_left (fun acc x -> Graph.union acc x) g gs in
        let default () =
          aux last_ids g next
        in
        match last_ids with
        | [] -> (
            match next with
            | P_null ->
              aux last_ids g next
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
                aux [id] g next
              )
              else (
                default ()
              )
            | _ -> default ()
          )
      )
    | P_while_cell_cas { cell; term; proc; next } -> (
        let true_branch_first_rule_id = Graph.get_id () in
        let true_branch_first_rule =
          Tg_ast.{ empty_rule with
                   l = [ T_cell_pat_match (cell, term) ];
                 }
        in
        let false_branch_first_rule_id = Graph.get_id () in
        let false_branch_first_rule = Tg_ast.{
            empty_rule with
            a = [T_app (Path.of_string Params.while_cell_neq_apred_name,
                        `Local 0,
                        [ T_symbol (cell, `Cell); term ],
                        None)];
          }
        in
        let g =
          g
          |> Graph.add_vertex_with_id
            true_branch_first_rule_id
            true_branch_first_rule
          |> link_backward ~last_ids true_branch_first_rule_id
          |> Graph.add_vertex_with_id
            false_branch_first_rule_id
            false_branch_first_rule
          |> link_backward ~last_ids false_branch_first_rule_id
        in
        let* proc_g =
          aux [true_branch_first_rule_id] Graph.empty proc
        in
        let true_branch_leaves =
          Graph.leaves proc_g
          |> List.of_seq
        in
        let g =
          g
          |> Graph.union proc_g
          |> link_backward ~last_ids:true_branch_leaves true_branch_first_rule_id
          |> link_backward ~last_ids:true_branch_leaves false_branch_first_rule_id
        in
        aux [false_branch_first_rule_id] g next
      )
  and aux_list last_ids g acc procs =
    match procs with
    | [] -> Ok (List.rev acc)
    | p :: ps ->
      let* p = aux last_ids g p in
      aux_list last_ids g (p :: acc) ps
  in
  let+ g = aux [] Graph.empty proc in
  (g, !tags)
