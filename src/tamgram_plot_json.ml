type exit_bias = Tr_frame_minimal_hybrid0.exit_bias

  type rule = {
    name : string;
    l : (string * Tg_ast.term list) list;
    a_sub_node_name : string;
    a_timepoint : string;
    a : Tg_ast.term list;
    r : (string * Tg_ast.term list) list;
  }

  type rule_node = {
    name : string;
    rule : rule;
    attrs : (string * string) list;
  }

  type node = {
    name : string;
    attrs : (string * string) list;
  }

  type edge = {
    src : string * string option;
    dst : string * string option;
    attrs : (string * string) list;
  }

  type item =
    | Kv of (string * string)
    | Node_settings of (string * string) list
    | Edge_settings of (string * string) list
    | Rule_node of rule_node
    | Node of node
    | Edge of edge

  module Dot_printers = struct
    let bar formatter _ =
      Fmt.pf formatter "|"

    let pp_path formatter (path : string Loc.tagged list) : unit =
      let s = Loc.content (List.hd (List.rev path)) in
      Fmt.pf formatter "%s" s

    let pp_term formatter (x : Tg_ast.term) =
      let open Tg_ast in
      let rec aux formatter x =
        match x with
        | T_value x -> (
            match Loc.content x with
            | `Str s -> Fmt.pf formatter "'%s'" s
            | `T -> Fmt.pf formatter "T"
            | `F -> Fmt.pf formatter "F")
        | T_symbol (name, symbol_sort) ->
          Fmt.pf formatter "%s%s"
            (match symbol_sort with
             | `Pub -> "$"
             | `Cell ->
               failwith (Fmt.str "Unexpected case: sees cell '%s at %a\n "
                           (Loc.content name)
                           Loc.pp_loc_of_tagged name ))
            (Loc.content name)
        | T_var (path, _name, typ) -> (
            let prefix =
              match typ with
              | None -> ""
              | Some typ -> Printers.prefix_of_typ typ
            in
            Fmt.pf formatter "%s%a" prefix pp_path
              path
          )
        | T_app { path; args; _ } -> (
            Fmt.pf formatter "%a(@[<h>%a@])" pp_path path
              Fmt.(list ~sep:comma aux)
              args
          )
        | T_tuple (_loc, l) -> (
            match l with
            | [] -> Fmt.pf formatter "'empty_tuple'"
            | _ -> (
                Fmt.pf formatter "@[<h>\\<%a\\>@]" Fmt.(list ~sep:comma aux) l
              )
          )
        | T_unary_op (op, x) ->
          Fmt.pf formatter "%s%a"
            (match op with `Persist -> "!" | `Not -> "not ")
            aux x
        | T_binary_op (op, x, y) -> (
            Fmt.pf formatter "((%a) %s (%a))" aux x
              (match op with
               | `Exp -> "^"
               | `Eq -> "="
               | `Iff -> "<=>"
               | `Imp -> "==>"
               | `Or -> "|"
               | `And -> "&"
               | `Plus -> "+"
               | `Xor -> "XOR"
              )
              aux y
          )
        | _ -> failwith "Unexpected case"
      in
      aux formatter x

    let pp_sub_node formatter ((sub_node, terms) : (string * Tg_ast.term list)) =
      Fmt.pf formatter "<%s> %a" sub_node
        (fun formatter terms ->
           match terms with
           | [] -> Fmt.pf formatter "ctx"
           | _ -> Fmt.(list ~sep:comma pp_term) formatter terms) terms

    let pp_l_r_row formatter (l : (string * Tg_ast.term list) list) =
      Fmt.pf formatter "%a"
        Fmt.(list ~sep:bar pp_sub_node)
        l

    let pp_a_row formatter (rule : rule) =
      let sep formatter () =
        Fmt.pf formatter ",\\l"
      in
      Fmt.pf formatter "<%s> #%s : %s[%a]"
        rule.a_sub_node_name
        rule.a_timepoint
        rule.name
        Fmt.(list ~sep pp_term)
        rule.a

    let pp_rule formatter (rule : rule) =
      Fmt.pf formatter "{{%a}|{%a}|{%a}}"
        pp_l_r_row rule.l
        pp_a_row rule
        pp_l_r_row rule.r

    let pp_kv formatter ((k, v) : string * string) =
      Fmt.pf formatter "%s=\"%s\"" k v

    let pp_attrs formatter (attrs : (string * string) list) =
      Fmt.pf formatter "%a" Fmt.(list ~sep:comma pp_kv) attrs

    let pp_attrs_prefix_with_comma formatter (attrs : (string * string) list) =
      match attrs with
      | [] -> ()
      | _ -> (
          Fmt.pf formatter ",%a" pp_attrs attrs
        )

    let pp_rule_node formatter (x : rule_node) =
      Fmt.pf formatter "%s[label=\"%a\"%a]"
        x.name
        pp_rule x.rule
        pp_attrs_prefix_with_comma
        x.attrs

    let pp_node formatter (x : node) =
      Fmt.pf formatter "%s[%a]"
        x.name
        pp_attrs x.attrs

    let pp_edge_target formatter ((node, sub_node) : string * string option) =
      match sub_node with
      | None -> Fmt.pf formatter "%s" node
      | Some sub_node -> Fmt.pf formatter "%s:%s" node sub_node

    let pp_edge formatter (x : edge) =
      Fmt.pf formatter "%a -> %a[%a]"
        pp_edge_target
        x.src
        pp_edge_target
        x.dst
        pp_attrs x.attrs

    let pp_item formatter (item : item) =
      Fmt.pf formatter "@[<h>";
      (match item with
       | Kv (k, v) -> (
           pp_kv formatter (k, v)
         )
       | Node_settings attrs -> (
           Fmt.pf formatter "node[%a]"
             pp_attrs attrs
         )
       | Edge_settings attrs -> (
           Fmt.pf formatter "edge[%a]"
             pp_attrs attrs
         )
       | Rule_node rule_node -> (
           pp_rule_node formatter rule_node
         )
       | Node node -> (
           pp_node formatter node
         )
       | Edge edge -> (
           pp_edge formatter edge
         )
      );
      Fmt.pf formatter ";@,@]"

    let pp_full formatter (items : item list) =
      Fmt.pf formatter "@[<v>digraph G {@,@]";
      Fmt.pf formatter "  @[<v>%a"
        Fmt.(list pp_item) items;
      Fmt.pf formatter "@]@,}@]"
  end

let call_dot (args : string list) =
  Sys.command (Fmt.str "dot %s" (String.concat " " args))

module JSON_parsers = struct
  let get_string_under_key ~k (l : (string * Yojson.Safe.t) list) : string =
    match List.assoc k l with
    | `String v -> v
    | _ -> invalid_arg (Fmt.str "get_string_under_key: Value under key %s is not string" k)

  let fact_of_json (x : Yojson.Safe.t) : Tg_ast.term =
    match x with
    | `Assoc l -> (
      let f = List.assoc "jgnFactName" l in
    )
    | _ -> invalid_arg "fact_of_json: Expected input to be an assoc list"

  let rule_of_json (x : Yojson.Safe.t) : rule =
    match x with
    | `Assoc l -> (
      let jgn_metadata = List.assoc "jgnMetadata" l in
      match jgn_metadata with
      | `Assoc l -> (
        let row_a = List.assoc "jgnActs" l in
        let row_r = List.assoc "jgnConcs" l in
        let row_l = List.assoc "jgnPrems" l in
      )
      | _ -> invalid_arg "rule_of_json: Expected jgnMetadata to be an assoc list"
    )
    | _ -> invalid_arg "rule_of_json: Expected an assoc list"
end

module Rewrite = struct
  type row = [ `L | `R ]

  let write_cell_operations
      (spec : Spec.t)
      (row : row)
      ~k
      (exit_bias : exit_bias)
    : Tg_ast.term list =
    let open Tg_ast in
    let cell_usage = Int_map.find k spec.cell_usages in
    let cells_defined = Cell_lifetime.Usage.defines_cells cell_usage in
    let cells_undefined = Cell_lifetime.Usage.defines_cells cell_usage in
    match row with
    | `L -> (
        match exit_bias with
        | `Forward -> (
            []
          )
        | `Backward -> (
            []
          )
        | `Empty -> (
            []
          )
      )
    | `R -> (
        Seq.append
          (cells_defined
           |> String_tagged_set.to_seq
           |> Seq.map (fun cell ->
               T_cell_assign (cell, T_value (Loc.untagged `T))
             ))
          (cells_undefined
           |> String_tagged_set.to_seq
           |> Seq.map (fun cell ->
               T_app {
                 path = [ Loc.untagged "undef" ];
                 name = `Local 0;
                 named_args = [];
                 args = [T_symbol (cell, `Cell)];
                 anno = None;
               }
             ))
        |> List.of_seq
      )


  let rewrite_state_fact (spec : Spec.t) (row : row) (x : Tg_ast.term) : Tg_ast.term list =
    let open Tg_ast in
    CCIO.with_out_a "tamgram-test.log" (fun oc ->
        let formatter = Format.formatter_of_out_channel oc in
        Fmt.pf formatter "@[<v>%a@,@]@." Printers.pp_term x;
        flush oc
      );
    let default = [ x ] in
    let exception Fail in
    try
      let (path, args) =
        match x with
        | T_app { path; args; _ } -> (path, args)
        | _ -> raise Fail
      in
      let name =
        match path with
        | [ name ] -> Loc.content name
        | _ -> raise Fail
      in
      CCIO.with_out_a "tamgram-test.log" (fun oc ->
          let formatter = Format.formatter_of_out_channel oc in
          Fmt.pf formatter "@[<v>name: %s@,@]@." name;
          flush oc
        );
      let exit_bias =
        match name with
        | "StF" -> `Forward
        | "StB" -> `Backward
        | "St" -> `Empty
        | _ -> raise Fail
      in
      (* let (pid, vertex, frame) =
         match args with
         | [ pid; T_value vertex; frame ] -> (
            (pid,
             (match Loc.content vertex with
              | `Str vertex -> vertex
              | _ -> raise Fail),
             (match frame with
              | T_value x -> (
                  match Loc.content x with
                  | `Str "empty_tuple" -> []
                  | _ -> raise Fail
                )
              | T_tuple (_loc, l) -> l
              | _ -> raise Fail)
            )
          )
         | _ -> raise Fail
         in *)
      let vertex =
        match args with
        | [ pid; T_value vertex; frame ] -> (
            match Loc.content vertex with
            | `Str vertex -> vertex
            | _ -> raise Fail
          )
        | _ -> raise Fail
      in
      let k =
        if String.length vertex > 3
        && StringLabels.sub ~pos:0 ~len:3 vertex = Params.graph_vertex_label_prefix
        then (
          match
            int_of_string_opt
              (StringLabels.sub ~pos:3 ~len:(String.length vertex-3) vertex)
          with
          | None -> raise Fail
          | Some k -> k
        ) else (
          raise Fail
        )
      in
      CCIO.with_out_a "tamgram-test.log" (fun oc ->
          let formatter = Format.formatter_of_out_channel oc in
          Fmt.pf formatter "vertex: %s@," vertex
        );
      write_cell_operations spec row ~k exit_bias
    with
    | Fail -> default

  (* let rewrite_rule (spec : Spec.t) (rule : rule) : rule =
    let rewrite_sub_nodes (row : row) (sub_nodes : (string * Tg_ast.term list) list) =
      CCList.map (fun (sub_node, terms) ->
          (sub_node,
           CCList.flat_map (fun term ->
               rewrite_state_fact spec row term
             ) terms
          )
        )
        sub_nodes
    in
    let l = rewrite_sub_nodes `L rule.l in
    let r = rewrite_sub_nodes `R rule.r in
    { rule with l; r } *)

  (* let item (spec : Spec.t) (x : item) : item =
    match x with
    | Rule_node { name; rule; attrs } -> (
        Rule_node { name; rule = rewrite_rule spec rule; attrs }
      )
    | _ -> x *)
end

let run () =
  let open Result_syntax in
  let argv =
    match Array.to_list Sys.argv with
    | [] -> failwith "Unexpected case"
    | _self :: rest -> rest
  in
  CCIO.with_out_a "tamgram-test.log" (fun oc ->
      let formatter = Format.formatter_of_out_channel oc in
      Fmt.pf formatter "argv: %s@," (String.concat " " argv)
    );
  let call () =
    exit (call_dot argv)
  in
  match Sys.getenv_opt "TG_FILE" with
  | None -> call ()
  | Some tg_file -> (
      match argv with
      | [] | [ "-V" ] -> call ()
      | _ -> (
          match List.filter (fun s -> Filename.extension s = ".json") argv with
          | [] -> call ()
          | json_file :: _ -> (
              Sys.command (Fmt.str "cp %s %s" json_file "tamgram-test0.json") |> ignore
              (* let res =
                 let* root = Modul_load.from_file tg_file in
                 let* spec =  Tg.run_pipeline (Spec.make root) in
                 let+ items = load_dot_file dot_file in
                 List.map (Rewrite.item spec) items
                 in
                 match res with
                 | Error _ -> call ()
                 | Ok items -> (
                  Sys.command (Fmt.str "cp %s %s" json_file "tamgram-test0.json");
                  CCIO.with_out ~flags:[Open_creat; Open_trunc; Open_binary] dot_file (fun oc ->
                      let formatter = Format.formatter_of_out_channel oc in
                      Fmt.pf formatter "%a@." Printers.pp_full items
                    );
                  CCIO.with_out ~flags:[Open_creat; Open_trunc; Open_binary] "tamgram-test1.dot" (fun oc ->
                      let formatter = Format.formatter_of_out_channel oc in
                      Fmt.pf formatter "%a@." Printers.pp_full items
                    );
                  call ()
                 )
              *)
            )
        )
    )

let () = run ()
