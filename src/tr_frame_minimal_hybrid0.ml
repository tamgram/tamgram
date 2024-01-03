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
  let pred = Graph.pred k g in
  let succ = Graph.succ k g in
  (
    if Int_set.cardinal succ <= 1 then
      `Forward
    else
      `Backward
  )

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
    rule_name : string;
    entry_fact : State_fact_IR.t option;
    l : Tg_ast.term list;
    a : Tg_ast.term list;
    r : Tg_ast.term list;
    exit_fact : State_fact_IR.t option;
  }

  let to_decl (t : t) : Tg_ast.decl =
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
    let open Tg_ast in
    D_rule {
      binding =
        Binding.make
          (Loc.untagged t.rule_name)
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

  let of_seq (s : (int * Rule_IR.t) Seq.t) : t =
    Seq.fold_left (fun m (k, x) ->
        let l =
          Option.value ~default:[]
            (Int_map.find_opt k m)
        in
        Int_map.add k (x :: l) m
      )
      Int_map.empty
      s

  let to_seq (t : t) : (int * Rule_IR.t) Seq.t =
    Int_map.to_seq t
    |> Seq.flat_map (fun (k, l) ->
        List.to_seq l
        |> Seq.map (fun ir -> (k, ir))
      )

  let union (m1 : t) (m2 : t) : t =
    Int_map.union (fun _k l1 l2 ->
        Some (l1 @ l2)
      )
      m1 m2
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
          (k,
           Rule_IR.{ k;
                     rule_name;
                     entry_fact = None;
                     l;
                     a;
                     r;
                     exit_fact = Some exit_fact;
                   }
          )
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
              (k,
               Rule_IR.{
                 k;
                 rule_name;
                 entry_fact = Some entry_fact;
                 l;
                 a;
                 r;
                 exit_fact = Some exit_fact;
               }
              )
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
          (k,
           Rule_IR.{
             k;
             rule_name;
             entry_fact = Some entry_fact;
             l;
             a;
             r;
             exit_fact = None;
           }
          )
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
  Rule_IR_store.to_seq rule_irs
  |> Seq.map (fun (_k, rule_ir) -> Rule_IR.to_decl rule_ir)
