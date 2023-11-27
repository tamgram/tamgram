open Tr_utils

type exit_bias = [
  | `Forward
  | `Backward
  | `Empty
]

let rule_is_empty (spec : Spec.t) (g : Tg_graph.t) (k : int) =
  let ru = Graph.find k g in
  let cell_pat_matches =
    Option.value ~default:[]
      (Int_map.find_opt k spec.user_specified_cell_pat_matches)
  in
  cell_pat_matches = []
  && ru.l = [] && ru.a = [] && ru.r = []

let exit_fact_to_empty_rule (spec : Spec.t) g (k : int) ~empty_rule : Tg_ast.term =
  let ctx_r =
    Int_map.find empty_rule spec.cells_to_carry_over_before
  in
  let ru = Graph.find k g in
  let cell_subs = cell_subs_of_rule spec g k in
  let _r, assigns =
    clean_up_r cell_subs Tg_ast.(ru.r)
  in
  let frame =
    String_tagged_set.to_seq ctx_r
    |> Seq.map (fun c ->
        List.assoc (Loc.content c) (assigns @ cell_subs)
      )
    |> List.of_seq
  in
  T_app { path = Path.of_string "St";
          name = `Global 0;
          named_args = [];
          args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                 ; T_value (Loc.untagged (`Str
                                            (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix empty_rule)))
                 ; T_tuple (None, frame)
                 ];
          anno = None;
        }

let entry_fact_from_empty_rule (spec : Spec.t) g (k : int) ~empty_rule : Tg_ast.term =
  let ctx_r =
    Int_map.find empty_rule spec.cells_to_carry_over_before
  in
  let cell_subs = cell_subs_of_rule spec g k in
  let frame =
    String_tagged_set.to_seq ctx_r
    |> Seq.map (fun c ->
        List.assoc (Loc.content c) cell_subs
      )
    |> List.of_seq
  in
  T_app { path = Path.of_string "St";
          name = `Global 0;
          named_args = [];
          args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                 ; T_value (Loc.untagged (`Str
                                            (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix empty_rule)))
                 ; T_tuple (None, frame)
                 ];
          anno = None;
        }

module Forward_biased = struct
  let entry_fact (spec : Spec.t) g (k : int) : Tg_ast.term =
    let ctx_r =
      Int_map.find k spec.cells_to_carry_over_before
    in
    let cell_subs = cell_subs_of_rule spec g k in
    let frame_l =
      String_tagged_set.to_seq ctx_r
      |> Seq.map (fun c ->
          List.assoc (Loc.content c) cell_subs
        )
      |> List.of_seq
    in
    T_app { path = Path.of_string "StF";
            name = `Global 0;
            named_args = [];
            args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                   ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k)))
                   ; T_tuple (None, frame_l)
                   ];
            anno = None;
          }

  let exit_fact (spec : Spec.t) (g : Tg_graph.t) (k : int) ~succ : Tg_ast.term =
    let ru = Graph.find k g in
    let ctx_r_of_succ =
      Int_map.find succ spec.cells_to_carry_over_before
    in
    let cell_subs = cell_subs_of_rule spec g k in
    let _r, assigns =
      clean_up_r cell_subs ru.r
    in
    let frame_r =
      String_tagged_set.to_seq ctx_r_of_succ
      |> Seq.map (fun c ->
          List.assoc (Loc.content c) (assigns @ cell_subs)
        )
      |> List.of_seq
    in
    T_app { path = Path.of_string "StF";
            name = `Global 0;
            named_args = [];
            args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                   ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix succ)))
                   ; T_tuple (None, frame_r)
                   ];
            anno = None;
          }
end

module Backward_biased = struct
  let entry_fact (spec : Spec.t) g ~pred (k : int) : Tg_ast.term =
    let ctx_ra_of_pred =
      Int_map.find pred spec.cells_to_carry_over_after
    in
    let cell_subs = cell_subs_of_rule spec g k in
    let frame_l =
      String_tagged_set.to_seq ctx_ra_of_pred
      |> Seq.map (fun c ->
          List.assoc (Loc.content c) cell_subs
        )
      |> List.of_seq
    in
    T_app { path = Path.of_string "StB";
            name = `Global 0;
            named_args = [];
            args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                   ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix pred)))
                   ; T_tuple (None, frame_l)
                   ];
            anno = None;
          }

  let exit_fact (spec : Spec.t) (g : Tg_graph.t) (k : int) : Tg_ast.term =
    let ru = Graph.find k g in
    let ctx_ra =
      Int_map.find k spec.cells_to_carry_over_after
    in
    let cell_subs = cell_subs_of_rule spec g k in
    let _r, assigns =
      clean_up_r cell_subs ru.r
    in
    let frame_r =
      String_tagged_set.to_seq ctx_ra
      |> Seq.map (fun c ->
          List.assoc (Loc.content c) (assigns @ cell_subs)
        )
      |> List.of_seq
    in
    T_app { path = Path.of_string "StB";
            name = `Global 0;
            named_args = [];
            args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
                   ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix k)))
                   ; T_tuple (None, frame_r)
                   ];
            anno = None;
          }
end

let exit_bias (spec : Spec.t) (g : Tg_graph.t) (k : int) : exit_bias =
  let rule_is_empty x = rule_is_empty spec g x in
  let pred = Graph.pred k g in
  let succ = Graph.succ k g in
  let no_pred_is_empty () =
    not (Int_set.exists rule_is_empty pred)
  in
  let no_succ_is_empty () =
    not (Int_set.exists rule_is_empty succ)
  in
  if rule_is_empty k && no_pred_is_empty () && no_succ_is_empty () then
    `Empty
  else (
    if Int_set.cardinal succ <= 1 then
      `Forward
    else
      `Backward
  )

let compute_possible_exit_facts spec g k : (int option * Tg_ast.term) Seq.t =
  let empty_rule_exit_facts =
    Graph.succ_seq k g
    |> Seq.filter (fun x -> exit_bias spec g x = `Empty)
    |> Seq.map (fun empty_rule ->
        (Some empty_rule, exit_fact_to_empty_rule spec g k ~empty_rule))
  in
  match exit_bias spec g k with
  | `Empty -> Seq.empty
  | `Forward -> (
      Graph.succ_seq k g
      |> Seq.filter (fun x -> exit_bias spec g x <> `Empty)
      |> Seq.map (fun succ ->
          (Some succ, Forward_biased.exit_fact spec g k ~succ)
        )
      |> Seq.append empty_rule_exit_facts
    )
  | `Backward ->
    Seq.cons (None, Backward_biased.exit_fact spec g k)
      empty_rule_exit_facts

let compute_possible_entry_facts spec g k : (int option * Tg_ast.term) Seq.t =
  match exit_bias spec g k with
  | `Empty -> Seq.empty
  | _ -> (
      let
        forward_biased_exit_preds,
        backward_biased_exit_preds,
        empty_rule_exit_preds
        =
        Int_set.fold (fun x (f, b, e) ->
            match exit_bias spec g x with
            | `Forward -> (Int_set.add x f, b, e)
            | `Backward -> (f, Int_set.add x b, e)
            | `Empty -> (f, b, Int_set.add x e)
          )
          (Graph.pred k g)
          (Int_set.empty, Int_set.empty, Int_set.empty)
      in
      [
        (if Int_set.is_empty forward_biased_exit_preds then Seq.empty
         else (
           Seq.return (None, Forward_biased.entry_fact spec g k)
         )
        );
        (Int_set.to_seq backward_biased_exit_preds
         |> Seq.map (fun pred ->
             (Some pred, Backward_biased.entry_fact spec g k ~pred)
           )
        );
        (Int_set.to_seq empty_rule_exit_preds
         |> Seq.map (fun empty_rule ->
             (Some empty_rule, entry_fact_from_empty_rule spec g k ~empty_rule)
           )
        );
      ]
      |> List.to_seq
      |> Seq.flat_map Fun.id
    )

let pp_rule_id
    ~(pred : [ `None | `Many | `Index of int ])
    ~k
    ~(succ: [ `None | `Many | `Index of int ])
    formatter
    ()
  =
  Fmt.pf formatter "%sTo%dTo%s"
    (match pred with
     | `None -> "None"
     | `Many -> "Many"
     | `Index x -> string_of_int x
    )
    k
    (match succ with
     | `None -> "None"
     | `Many -> "Many"
     | `Index x -> string_of_int x
    )

let start_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  Graph.roots g
  |> Seq.flat_map (fun k ->
      let ru = Graph.find k g in
      let cell_subs = cell_subs_of_rule spec g k in
      let l = clean_up_l cell_subs ru.l in
      let a = clean_up_a cell_subs ru.a in
      let r, _assigns =
        clean_up_r cell_subs ru.r
      in
      compute_possible_exit_facts spec g k
      |> Seq.map (fun (dst, exit_fact) ->
          let r = exit_fact :: r in
          let rule_name =
            Fmt.str "%a___%a%s" pp_name_of_proc binding
              (pp_rule_id
                 ~pred:`None
                 ~k
                 ~succ:(match dst with
                     | None -> `Many
                     | Some x -> `Index x))
              ()
              (match Int_map.find_opt k spec.rule_tags with
               | None -> ""
               | Some s -> "___" ^ s
              )
          in
          D_rule {
            binding =
              Binding.make
                (Loc.untagged rule_name)
                {
                  l;
                  vars_in_l = [];
                  bindings_before_a = [];
                  a;
                  bindings_before_r = [];
                  r;
                }
          }
        )
    )

let rule_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  Graph.vertex_seq g
  |> Seq.flat_map (fun (k, _) ->
      let ru = Graph.find k g in
      let cell_subs = cell_subs_of_rule spec g k in
      let l = clean_up_l cell_subs ru.l in
      let a = clean_up_a cell_subs ru.a in
      let r, _assigns =
        clean_up_r cell_subs ru.r
      in
      compute_possible_exit_facts spec g k
      |> Seq.flat_map (fun (dst, exit_fact) ->
          let r = exit_fact :: r in
          compute_possible_entry_facts spec g k
          |> Seq.map (fun (src, entry_fact) ->
              let l = entry_fact :: l in
              let rule_name =
                Fmt.str "%a___%a%s" pp_name_of_proc binding
                  (pp_rule_id
                     ~pred:(match src with
                         | None -> `Many
                         | Some x -> `Index x)
                     ~k
                     ~succ:(match dst with
                         | None -> `Many
                         | Some x -> `Index x))
                  ()
                  (match Int_map.find_opt k spec.rule_tags with
                   | None -> ""
                   | Some s -> "___" ^ s
                  )
              in
              D_rule {
                binding =
                  Binding.make
                    (Loc.untagged rule_name)
                    {
                      l;
                      vars_in_l = [];
                      bindings_before_a = [];
                      a;
                      bindings_before_r = [];
                      r;
                    }
              }
            )
        )
    )

let end_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let open Tg_ast in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  Graph.leaves g
  |> Seq.flat_map (fun k ->
      let ru = Graph.find k g in
      let cell_subs = cell_subs_of_rule spec g k in
      let l = clean_up_l cell_subs ru.l in
      let a = clean_up_a cell_subs ru.a in
      let r, _assigns =
        clean_up_r cell_subs ru.r
      in
      compute_possible_entry_facts spec g k
      |> Seq.map (fun (src, entry_fact) ->
          let l = entry_fact :: l in
          let rule_name =
            Fmt.str "%a___%a%s" pp_name_of_proc binding
              (pp_rule_id
                 ~pred:(match src with
                     | None -> `Many
                     | Some x -> `Index x)
                 ~k
                 ~succ:`None)
              ()
              (match Int_map.find_opt k spec.rule_tags with
               | None -> ""
               | Some s -> "___" ^ s
              )
          in
          D_rule {
            binding =
              Binding.make
                (Loc.untagged rule_name)
                {
                  l;
                  vars_in_l = [];
                  bindings_before_a = [];
                  a;
                  bindings_before_r = [];
                  r;
                }
          }
        )
    )
