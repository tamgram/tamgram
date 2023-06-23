open Result_syntax

type t = Tg_ast.rule Graph.t

type loop_skeleton = {
  true_branch_guard_rule_id : int;
  false_branch_guard_rule_id : int option;
  after_loop_rule_id : int;
}

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

let loop_find
    ~(keyword : string Loc.tagged)
    ~(label : string Loc.tagged option)
    (labelled_loops : loop_skeleton String_map.t)
    (loop_stack : loop_skeleton list)
  : (loop_skeleton, Error_msg.t) result =
  match loop_stack with
  | [] -> Error (
      Error_msg.make
        (Loc.tag keyword)
        (Fmt.str "%s can only be used inside a loop" (Loc.content keyword))
    )
  | inner_most_loop_skeleton :: _ -> (
      match label with
      | None -> (
          Ok inner_most_loop_skeleton
        )
      | Some label -> (
          match String_map.find_opt (Loc.content label) labelled_loops with
          | None -> Error (
              Error_msg.make
                (Loc.tag label)
                (Fmt.str "Loop with label \"%s\" not found" (Loc.content label))
            )
          | Some skeleton -> Ok skeleton
        )
    )

type restrictions_required = {
  cell_neq : bool;
  cell_pat_match_restrictions : Tg_ast.term Int_map.t;
}

let restrictions_empty = {
  cell_neq = false;
  cell_pat_match_restrictions = Int_map.empty;
}

let restrictions_required_union x y : restrictions_required =
  {
    cell_neq = x.cell_neq || y.cell_neq;
    cell_pat_match_restrictions =
      Int_map.union (fun _ _ -> failwith "Unexpected case")
        x.cell_pat_match_restrictions y.cell_pat_match_restrictions;
  }

let of_proc (proc : Tg_ast.proc) : (t * string Int_map.t * restrictions_required, Error_msg.t) result =
  let tags : string Int_map.t ref = ref Int_map.empty in
  let add_cell_neq_restriction = ref false in
  let cell_pat_match_restrictions : Tg_ast.term Int_map.t ref =
    ref Int_map.empty
  in
  let cond_cell_match_matching_rule cell term vars_in_term =
    Tg_ast.{ empty_rule with
             l = [ T_cell_pat_match (cell, term) ];
             vars_in_l = List.map (Binding.update `Bitstring) vars_in_term;
           }
  in
  let cond_cell_match_not_matching_rule cell term vars_in_term =
    match vars_in_term with
    | [] -> (
        add_cell_neq_restriction := true;
        Tg_ast.{
          empty_rule with
          a = [T_app { path = Path.of_string Params.cell_neq_apred_name;
                       name = `Local 0;
                       named_args = [];
                       args = [ T_symbol (cell, `Cell); term ];
                       anno = None;
                     } ];
        }
      )
    | _ -> (
        let id = Graph.get_id () in
        cell_pat_match_restrictions := Int_map.add id term !cell_pat_match_restrictions;
        Tg_ast.{
          empty_rule with
          a = [T_app { path = Path.of_string (Fmt.str "%s%d" Params.cell_pat_match_apred_prefix id);
                       name = `Local 0;
                       named_args = [];
                       args = [ T_symbol (cell, `Cell) ];
                       anno = None;
                     }];
        }
      )
  in
  let rec aux
      (labelled_loops : loop_skeleton String_map.t)
      (loop_stack : loop_skeleton list)
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
      aux labelled_loops loop_stack [id] g next
    | P_branch (loc, procs, next) -> (
        let* gs =
          aux_list labelled_loops loop_stack last_ids Graph.empty [] procs
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
          aux labelled_loops loop_stack last_ids g next
        in
        match last_ids with
        | [] -> (
            match next with
            | P_null ->
              aux labelled_loops loop_stack last_ids g next
            | _ ->
              Error (
                Error_msg.make
                  loc
                  "The process after choice here is not reachable"
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
                aux labelled_loops loop_stack [id] g next
              )
              else (
                default ()
              )
            | _ -> default ()
          )
      )
    | P_loop { label; mode; proc; next } -> (
        let enter_loop (loop_skeleton : loop_skeleton) (proc : Tg_ast.proc) =
          let labelled_loops =
            match label with
            | None -> labelled_loops
            | Some label ->
              String_map.add (Loc.content label) loop_skeleton labelled_loops
          in
          let loop_stack =
            loop_skeleton :: loop_stack
          in
          aux labelled_loops loop_stack [loop_skeleton.true_branch_guard_rule_id] Graph.empty proc
        in
        match mode with
        | `While { mode; cell; term; vars_in_term } -> (
            let matching_rule =
              cond_cell_match_matching_rule cell term vars_in_term
            in
            let not_matching_rule =
              cond_cell_match_not_matching_rule cell term vars_in_term
            in
            let true_branch_guard_rule_id = Graph.get_id () in
            let false_branch_guard_rule_id = Graph.get_id () in
            let after_loop_rule_id = Graph.get_id () in
            let true_branch_guard_rule, false_branch_guard_rule =
              match mode with
              | `Matching -> matching_rule, not_matching_rule
              | `Not_matching -> not_matching_rule, matching_rule
            in
            let g =
              g
              |> Graph.add_vertex_with_id
                true_branch_guard_rule_id
                true_branch_guard_rule
              |> link_backward ~last_ids true_branch_guard_rule_id
              |> Graph.add_vertex_with_id
                false_branch_guard_rule_id
                false_branch_guard_rule
              |> link_backward ~last_ids false_branch_guard_rule_id
            in
            let loop_skeleton : loop_skeleton =
              { true_branch_guard_rule_id;
                false_branch_guard_rule_id = Some false_branch_guard_rule_id;
                after_loop_rule_id;
              }
            in
            let* proc_g = enter_loop loop_skeleton proc in
            let true_branch_leaves =
              Graph.leaves proc_g
              |> Seq.filter (fun k ->
                  not (List.mem k [ true_branch_guard_rule_id
                                  ; false_branch_guard_rule_id
                                  ; after_loop_rule_id])
                )
              |> List.of_seq
            in
            let g =
              g
              |> Graph.union proc_g
              |> link_backward ~last_ids:true_branch_leaves true_branch_guard_rule_id
              |> link_backward ~last_ids:true_branch_leaves false_branch_guard_rule_id
              |> link_backward ~last_ids:[false_branch_guard_rule_id] after_loop_rule_id
              |> Graph.add_vertex_with_id after_loop_rule_id empty_rule
            in
            aux labelled_loops loop_stack [after_loop_rule_id] g next
          )
        | `Unconditional -> (
            let true_branch_guard_rule_id = Graph.get_id () in
            let after_loop_rule_id = Graph.get_id () in
            let g =
              g
              |> Graph.add_vertex_with_id
                true_branch_guard_rule_id
                empty_rule
              |> link_backward ~last_ids true_branch_guard_rule_id
            in
            let loop_skeleton : loop_skeleton =
              { true_branch_guard_rule_id;
                false_branch_guard_rule_id = None;
                after_loop_rule_id ;
              }
            in
            let* proc_g = enter_loop loop_skeleton proc in
            let true_branch_leaves =
              Graph.leaves proc_g
              |> Seq.filter (fun k ->
                  not (List.mem k [ true_branch_guard_rule_id
                                  ; after_loop_rule_id])
                )
              |> List.of_seq
            in
            let g =
              g
              |> Graph.union proc_g
              |> link_backward ~last_ids:true_branch_leaves true_branch_guard_rule_id
              |> Graph.add_vertex_with_id after_loop_rule_id empty_rule
            in
            aux labelled_loops loop_stack [after_loop_rule_id] g next
          )
      )
    | P_break (loc, label) -> (
        let+ skeleton =
          loop_find
            ~keyword:Loc.{ loc; content = "break" }
            ~label
            labelled_loops loop_stack
        in
        g
        |> link_backward ~last_ids skeleton.after_loop_rule_id
      )
    | P_continue (loc, label) -> (
        let+ skeleton =
          loop_find
            ~keyword:Loc.{ loc; content = "continue" }
            ~label
            labelled_loops loop_stack
        in
        g
        |> link_backward ~last_ids skeleton.true_branch_guard_rule_id
        |> (fun g ->
            match skeleton.false_branch_guard_rule_id with
            | None -> g
            | Some id ->
              link_backward ~last_ids id g
          )
      )
    | P_if_then_else { loc;
                       cond = { mode; cell; term; vars_in_term };
                       true_branch;
                       false_branch;
                       next;
                     } -> (
        let matching_rule =
          cond_cell_match_matching_rule cell term vars_in_term
        in
        let not_matching_rule =
          cond_cell_match_not_matching_rule cell term vars_in_term
        in
        let true_branch_guard_rule_id = Graph.get_id () in
        let false_branch_guard_rule_id = Graph.get_id () in
        let true_branch_guard_rule, false_branch_guard_rule =
          match mode with
          | `Matching -> matching_rule, not_matching_rule
          | `Not_matching -> not_matching_rule, matching_rule
        in
        let g =
          g
          |> Graph.add_vertex_with_id
            true_branch_guard_rule_id
            true_branch_guard_rule
          |> link_backward ~last_ids true_branch_guard_rule_id
          |> Graph.add_vertex_with_id
            false_branch_guard_rule_id
            false_branch_guard_rule
          |> link_backward ~last_ids false_branch_guard_rule_id
        in
        let* true_branch_g =
          aux labelled_loops loop_stack [true_branch_guard_rule_id] Graph.empty true_branch
        in
        let* false_branch_g =
          aux labelled_loops loop_stack [false_branch_guard_rule_id] Graph.empty false_branch
        in
        let true_branch_leaves = Graph.leaves true_branch_g in
        let false_branch_leaves = Graph.leaves false_branch_g in
        let g =
          Graph.union g
            (Graph.union true_branch_g false_branch_g)
        in
        let last_ids =
          Seq.append true_branch_leaves false_branch_leaves
          |> List.of_seq
        in
        let default () =
          aux labelled_loops loop_stack last_ids g next
        in
        match last_ids with
        | [] -> (
            match next with
            | P_null ->
              aux labelled_loops loop_stack last_ids g next
            | _ ->
              Error (
                Error_msg.make
                  loc
                  "The process after if then else here is not reachable"
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
                aux labelled_loops loop_stack [id] g next
              )
              else (
                default ()
              )
            | _ -> default ()
          )
      )
  and aux_list labelled_loops loop_stack last_ids g acc procs =
    match procs with
    | [] -> Ok (List.rev acc)
    | p :: ps ->
      let* p = aux labelled_loops loop_stack last_ids g p in
      aux_list labelled_loops loop_stack last_ids g (p :: acc) ps
  in
  let+ g = aux String_map.empty [] [] Graph.empty proc in
  (g,
   !tags,
   { cell_neq = !add_cell_neq_restriction;
     cell_pat_match_restrictions = !cell_pat_match_restrictions }
  )
