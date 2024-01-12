open Tr_utils

type exit_bias = [
  | `Forward
  | `Backward
]

let rule_is_empty (spec : Spec.t) (g : Tg_graph.t) (k : int) =
  let ru = Graph.find k g in
  let cell_pat_matches =
    Option.value ~default:[]
      (Int_map.find_opt k spec.user_specified_cell_pat_matches)
  in
  cell_pat_matches = []
  && ru.l = [] && ru.a = [] && ru.r = []

module State_fact_IR = struct
  type t = {
    bias : exit_bias;
    k : int;
    frame : Tg_ast.term list;
  }

  let equal (t1 : t) (t2 : t) : bool =
    t1.bias = t2.bias
    && t1.k = t2.k

  let to_term (t : t) : Tg_ast.term =
    T_app {
      path = (match t.bias with
          | `Forward -> Path.of_string "StF"
          | `Backward -> Path.of_string "StB");
      name = `Global 0;
      named_args = [];
      args = [ T_var (Path.of_string "pid", `Global 0, Some `Fresh)
             ; T_value (Loc.untagged (`Str (Printf.sprintf "%s%d" Params.graph_vertex_label_prefix t.k)))
             ; T_tuple (None, t.frame)
             ];
      anno = None;
    }
end

module Forward_biased = struct
  let entry_fact (spec : Spec.t) g (k : int) : State_fact_IR.t =
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
    {
      bias = `Forward;
      k;
      frame = frame_l;
    }

  let exit_fact (spec : Spec.t) (g : Tg_graph.t) (k : int) ~succ : State_fact_IR.t =
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
    {
      bias = `Forward;
      k = succ;
      frame = frame_r;
    }
end

module Backward_biased = struct
  let entry_fact (spec : Spec.t) g ~pred (k : int) : State_fact_IR.t =
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
    {
      bias = `Backward;
      k = pred;
      frame = frame_l;
    }

  let exit_fact (spec : Spec.t) (g : Tg_graph.t) (k : int) : State_fact_IR.t =
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
    {
      bias = `Backward;
      k;
      frame = frame_r;
    }
end

let exit_bias (spec : Spec.t) (g : Tg_graph.t) (k : int) : exit_bias =
  let succ = Graph.succ k g in
  if Int_set.cardinal succ <= 1 then
    `Forward
  else
    `Backward

let compute_possible_exit_facts spec g k : (int option * State_fact_IR.t) Seq.t =
  match exit_bias spec g k with
  | `Forward -> (
      Graph.succ_seq k g
      |> Seq.map (fun succ ->
          (Some succ, Forward_biased.exit_fact spec g k ~succ)
        )
    )
  | `Backward -> (
      Seq.return (None, Backward_biased.exit_fact spec g k)
    )

let compute_possible_entry_facts spec g k : (int option * State_fact_IR.t) Seq.t =
  let
    forward_biased_exit_preds,
    backward_biased_exit_preds
    =
    Int_set.fold (fun x (f, b) ->
        match exit_bias spec g x with
        | `Forward -> (Int_set.add x f, b)
        | `Backward -> (f, Int_set.add x b)
      )
      (Graph.pred k g)
      (Int_set.empty, Int_set.empty)
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
  ]
  |> List.to_seq
  |> Seq.flat_map Fun.id

type link_target = [
  | `None
  | `Many
  | `Index of int
]

let pp_link_target formatter (x : link_target) =
  match x with
  | `Many -> Fmt.pf formatter "Many"
  | `None -> Fmt.pf formatter "None"
  | `Index x -> Fmt.pf formatter "%d" x

let pp_rule_id
    ~(pred : link_target)
    ~k
    ~(succ: link_target)
    formatter
    ()
  =
  Fmt.pf formatter "%aTo%dTo%a"
    pp_link_target pred
    k
    pp_link_target succ

module Rule_IR = struct
  type t = {
    k : int;
    pred : link_target;
    succ : link_target;
    rule_name_base : string;
    entry_fact : State_fact_IR.t option;
    l : Tg_ast.term list;
    a : Tg_ast.term list;
    r : Tg_ast.term list;
    exit_fact : State_fact_IR.t option;
  }

  let compare (t1 : t) (t2 : t) : int =
    let n0 = Int.compare t1.k t2.k in
    let n1 =
      match t1.entry_fact, t2.entry_fact with
      | None, None -> 0
      | Some t1_fact, Some t2_fact -> (
          Int.compare t1_fact.k t2_fact.k
        )
      | None, Some _ -> -1
      | Some _, None -> 1
    in
    let n2 =
      match t1.exit_fact, t2.exit_fact with
      | None, None -> 0
      | Some t1_fact, Some t2_fact -> (
          Int.compare t1_fact.k t2_fact.k
        )
      | None, Some _ -> -1
      | Some _, None -> 1
    in
    match n0, n1, n2 with
    | 0, 0, x -> x
    | 0, x, _ -> x
    | x, _, _ -> x

  let equal (t1 : t) (t2 : t) : bool =
    compare t1 t2 = 0

  let to_decl (spec : Spec.t) (t : t) : Tg_ast.decl =
    let l = match t.entry_fact with
      | None -> t.l
      | Some entry_fact ->
        State_fact_IR.to_term entry_fact :: t.l
    in
    let a = t.a in
    let r = match t.exit_fact with
      | None -> t.r
      | Some exit_fact ->
        State_fact_IR.to_term exit_fact :: t.r
    in
    let rule_name =
      Fmt.str "%s___%a%s" t.rule_name_base
        (pp_rule_id
           ~pred:t.pred
           ~k:t.k
           ~succ:t.succ)
        ()
        (match Int_map.find_opt t.k spec.rule_tags with
         | None -> ""
         | Some s -> "___" ^ s
        )
    in
    let open Tg_ast in
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
end

module Rule_IR_store = struct
  type t = Rule_IR.t list Int_map.t

  let remove (rule_ir : Rule_IR.t) (t : t) : t =
    match Int_map.find_opt rule_ir.k t with
    | None -> t
    | Some l -> (
        Int_map.add
          rule_ir.k
          (List.filter (fun x -> not (Rule_IR.equal x rule_ir)) l)
          t
      )

  let add (rule_ir : Rule_IR.t) (t : t) : t =
    let l =
      Option.value ~default:[]
        (Int_map.find_opt rule_ir.k t)
    in
    Int_map.add rule_ir.k
      (List.sort_uniq Rule_IR.compare (rule_ir :: l))
      t

  let of_seq (s : Rule_IR.t Seq.t) : t =
    Seq.fold_left (fun m x ->
        add x m
      )
      Int_map.empty
      s

  let to_seq (t : t) : Rule_IR.t Seq.t =
    Int_map.to_seq t
    |> Seq.flat_map (fun (_k, l) ->
        List.to_seq l
      )

  let union (m1 : t) (m2 : t) : t =
    Int_map.union (fun _k l1 l2 ->
        Some (l1 @ l2)
      )
      m1 m2

  let maximal_candidates_for_empty_rule_optmizations (spec : Spec.t) (g : Tg_graph.t) (t : t) =
    to_seq t
    |> Seq.fold_left (fun s (rule_ir : Rule_IR.t) ->
        if rule_is_empty spec g rule_ir.k then
          Int_set.add rule_ir.k s
        else
          s
      )
      Int_set.empty

  let compress_start_rules
      (spec : Spec.t) ((g, t) : Tg_graph.t * t)
    : Tg_graph.t * t =
    let rewrite_term (x : Tg_ast.term) =
      Term.replace_free_vars_via_name_strs_in_term
        [ (placeholder_var_name_of_cell Params.pid_cell_name,
           T_var (Path.of_string Params.pid_cell_name, `Global 0, Some `Fresh)) ]
        x
    in
    let rewrite_state_fact_ir ({ bias; k; frame } : State_fact_IR.t) : State_fact_IR.t =
      { bias;
        k;
        frame = List.map rewrite_term frame;
      }
    in
    Graph.roots g
    |> Seq.fold_left (fun ((g, t) : Tg_graph.t * t) k ->
        let start_ru = Graph.find k g in
        let t =
          Graph.succ_seq k g
          |> Seq.fold_left (fun (t : t) succ ->
              let succ_irs =
                Int_map.find succ t
                |> List.map (fun (succ_ir : Rule_IR.t) ->
                    let exit_fact =
                      Option.map rewrite_state_fact_ir succ_ir.exit_fact
                    in
                    let l = start_ru.l @ List.map rewrite_term succ_ir.l in
                    let a = List.map rewrite_term succ_ir.a in
                    let r = List.map rewrite_term succ_ir.r in
                    { succ_ir with
                      pred = `None;
                      entry_fact = None;
                      exit_fact;
                      l;
                      a;
                      r;
                    }
                  )
              in
              Int_map.add succ succ_irs t
            )
            t
        in
        (Graph.remove_vertex k g,
         Int_map.remove k t)
      )
      (g, t)

  let remove_end_rules
      (spec : Spec.t) ((g, t) : Tg_graph.t * t)
    : Tg_graph.t * t =
    Graph.leaves g
    |> Seq.fold_left (fun ((g, t) : Tg_graph.t * t) k ->
        if rule_is_empty spec g k then (
          let t =
            Graph.pred_seq k g
            |> Seq.fold_left (fun t pred ->
                let pred_irs =
                  Int_map.find pred t
                  |> List.map (fun (ir : Rule_IR.t) ->
                      match ir.entry_fact, ir.exit_fact with
                      | Some entry_fact, Some exit_fact -> (
                          if exit_fact.bias = `Forward && exit_fact.k = k then (
                            { ir with
                              exit_fact = None;
                              succ = `None;
                            }
                          ) else (
                            ir
                          )
                        )
                      | _, _ -> ir
                    )
                in
                Int_map.add pred pred_irs t
              )
              t
          in
          (Graph.remove_vertex k g,
           Int_map.remove k t)
        ) else (
          (g, t)
        )
      )
      (g, t)

  let has_empty_non_end_succ (spec : Spec.t) (g : Tg_graph.t) (k : int) =
    let leaves = Int_set.of_seq (Graph.leaves g) in
    let s =
      Graph.succ k g
      |> Int_set.to_seq
      |> Seq.filter (fun succ ->
          rule_is_empty spec g succ
          &&
          not (Int_set.mem succ leaves)
        )
    in
    match s () with
    | Seq.Nil -> false
    | _ -> true


  let compress_middle_empty_rules ~entry_bias ~exit_bias
      (spec : Spec.t) ((g, t) : Tg_graph.t * t)
    : Tg_graph.t * t =
    let exception Break in
    let maximal_candidates =
      maximal_candidates_for_empty_rule_optmizations spec g t
    in
    let t = ref t in
    let g = ref g in
    let rec aux () =
      let usable_rule_found = ref false in
      (try
         maximal_candidates
         |> Int_set.to_seq
         |> Seq.flat_map (fun k ->
             let l =
               Option.value ~default:[]
                 (Int_map.find_opt k !t)
             in
             List.to_seq l
           )
         |> Seq.iter (fun (rule_ir : Rule_IR.t) ->
             if Option.is_some (Graph.find_opt rule_ir.k !g)
             && rule_is_empty spec !g rule_ir.k
             && not (has_empty_non_end_succ spec !g rule_ir.k) then (
               match rule_ir.entry_fact, rule_ir.exit_fact with
               | Some entry_fact, Some exit_fact -> (
                   if entry_fact.bias = entry_bias && exit_fact.bias = exit_bias then (
                     usable_rule_found := true;
                     Graph.pred rule_ir.k !g
                     |> Int_set.to_seq
                     |> Seq.iter (fun pred_k ->
                         match Int_map.find_opt pred_k !t with
                         | None -> ()
                         | Some pred_rule_irs -> (
                             let pred_rule_irs =
                               List.map (fun (pred_rule_ir : Rule_IR.t) ->
                                   match pred_rule_ir.exit_fact with
                                   | None -> pred_rule_ir
                                   | Some pred_exit_fact -> (
                                       if State_fact_IR.equal pred_exit_fact entry_fact then (
                                         { pred_rule_ir with
                                           succ = (match exit_bias with
                                               | `Forward -> `Index exit_fact.k
                                               | `Backward -> `Many);
                                           exit_fact = Some { exit_fact with
                                                              frame = pred_exit_fact.frame };
                                           (* Some (match exit_bias with
                                              | `Forward -> { exit_fact with
                                                             frame = pred_exit_fact.frame }
                                              | `Backward -> { exit_fact with
                                                              k = pred_k;
                                                              frame = pred_exit_fact.frame
                                                            }
                                              ) *)
                                         }
                                       ) else (
                                         pred_rule_ir
                                       )
                                     )
                                 )
                                 pred_rule_irs
                             in
                             t := Int_map.add pred_k pred_rule_irs !t;
                             g := Graph.succ_seq rule_ir.k !g
                                  |> Seq.fold_left (fun g succ ->
                                      Graph.add_edge (pred_k, succ) g
                                    )
                                    !g;
                           )
                       );
                     t := remove rule_ir !t;
                     g := Graph.remove_vertex rule_ir.k !g;
                     raise Break
                   )
                 )
               | _, _ -> ()
             )
           )
       with
       | Break -> ());
      if !usable_rule_found then (
        aux ()
      )
    in
    aux ();
    (!g, !t)

  let compress_middle_empty_rules_StF_StF spec (g, t) =
    compress_middle_empty_rules ~entry_bias:`Forward ~exit_bias:`Forward spec (g, t)

  let compress_middle_empty_rules_StF_StB spec (g, t) =
    compress_middle_empty_rules ~entry_bias:`Forward ~exit_bias:`Backward spec (g, t)
end

let start_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Rule_IR_store.t =
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
          let rule_name_base =
            Fmt.str "%a" pp_name_of_proc binding
          in
          Rule_IR.{ k;
                    pred = `None;
                    succ = (match dst with
                        | None -> `Many
                        | Some x -> `Index x);
                    rule_name_base;
                    entry_fact = None;
                    l;
                    a;
                    r;
                    exit_fact = Some exit_fact;
                  }
        )
    )
  |> Rule_IR_store.of_seq

let rule_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Rule_IR_store.t =
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
          compute_possible_entry_facts spec g k
          |> Seq.map (fun (src, entry_fact) ->
              let rule_name_base =
                Fmt.str "%a" pp_name_of_proc binding
              in
              Rule_IR.{
                k;
                pred = (match src with
                    | None -> `Many
                    | Some x -> `Index x);
                succ = (match dst with
                    | None -> `Many
                    | Some x -> `Index x);
                rule_name_base;
                entry_fact = Some entry_fact;
                l;
                a;
                r;
                exit_fact = Some exit_fact;
              }
            )
        )
    )
  |> Rule_IR_store.of_seq

let end_tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Rule_IR_store.t =
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
          let rule_name_base =
            Fmt.str "%a" pp_name_of_proc binding
          in
          Rule_IR.{
            k;
            pred = (match src with
                | None -> `Many
                | Some x -> `Index x);
            succ = `None;
            rule_name_base;
            entry_fact = Some entry_fact;
            l;
            a;
            r;
            exit_fact = None;
          }
        )
    )
  |> Rule_IR_store.of_seq

let tr (binding : Tg_ast.proc Binding.t) (spec : Spec.t) : Tg_ast.decl Seq.t =
  let rule_irs =
    List.fold_left Rule_IR_store.union
      Int_map.empty
      [ start_tr binding spec;
        rule_tr binding spec;
        end_tr binding spec;
      ]
  in
  let g = Name_map.find (Binding.name binding) spec.proc_graphs in
  (g, rule_irs)
  |> Rule_IR_store.compress_middle_empty_rules_StF_StF spec
  |> Rule_IR_store.compress_middle_empty_rules_StF_StB spec
  |> Rule_IR_store.remove_end_rules spec
  |> Rule_IR_store.compress_start_rules spec
  |> (fun (_g, t) -> Rule_IR_store.to_seq t)
  |> Seq.map (Rule_IR.to_decl spec)
