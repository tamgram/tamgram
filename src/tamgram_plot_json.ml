type exit_bias = Tr_frame_minimal_hybrid0.exit_bias

let get_num : unit -> int =
  let counter = ref 0 in
  fun () ->
    let x = !counter in
    counter := x + 1;
    x

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

module Parsers = struct
  open Angstrom
  open Parser_components

  let ident_string =
    take_while1 (fun c ->
        is_alphanum c || c = '_' || c = '.')

  let quoted_p =
    char '"' *> take_while (fun c -> c <> '"') >>= fun s ->
    char '"' *> spaces *> return s

  let single_quoted_p =
    char '\'' *> take_while (fun c -> c <> '\'') >>= fun s ->
    char '\'' *> spaces *> return s

  let name_p =
    ident_string >>| fun name ->
    Loc.untagged name

  let term_p =
    let open Tg_ast in
    fix (fun exp ->
        let base =
          choice [
            (single_quoted_p >>| fun s ->
             T_value (Loc.untagged (`Str s))
            );
            (name_p >>= fun f ->
             spaces *> char '(' *> spaces *>
             sep_by comma exp >>= fun args ->
             spaces *> char ')' *>
             return (T_app {
                 path = [ f ];
                 name = `Local 0;
                 named_args = [];
                 args;
                 anno = None
               })
            );
            (string "\\<" *> spaces *> sep_by comma exp >>= fun terms ->
             string "\\>" *>
             return (T_tuple (None, terms))
            );
            (char '(' *> spaces *> exp <* spaces <* char ')');
            (char '$' *> spaces *> name_p >>| fun name ->
             T_symbol (name, `Pub)
            );
            (char '~' *> spaces *> name_p >>| fun name ->
             T_var ([name], `Local 0, Some `Fresh)
            );
            (name_p >>| fun name ->
             match Loc.content name with
             | "F" -> T_value (Loc.untagged `F)
             | "T" -> T_value (Loc.untagged `T)
             | _ -> T_var ([name], `Local 0, None)
            );
          ]
          <* spaces
        in
        let exp_op =
          char '^' *> spaces *>
          return (fun x y -> T_binary_op (`Exp, x, y))
        in
        let xor_op =
          string "\xc3\xa2\xc2\x8a\xc2\x95" *> spaces *>
          return (fun x y -> T_binary_op (`Xor, x, y))
        in
        let lvl1 = chainl1 base exp_op in
        let lvl2 = chainl1 lvl1 xor_op in
        lvl2 <* spaces
      )

  let fact_p =
    let open Tg_ast in
    choice [
      (char '!' *> spaces *> term_p >>| fun term ->
       T_unary_op (`Persist, term)
      );
      term_p
    ]
    <* spaces
end

let dot_node_name_of_json_node_name : string -> string =
  let tbl = Hashtbl.create 1024 in
  fun s ->
    match Hashtbl.find_opt tbl s with
    | None -> (
        let name = Fmt.str "n%d" (get_num ()) in
        Hashtbl.add tbl s name;
        name
      )
    | Some name -> name

module JSON_parsers = struct
  let get_string (x : Yojson.Safe.t) : string =
    match x with
    | `String v -> v
    | _ -> invalid_arg "get_string"

  let get_list (x : Yojson.Safe.t) : Yojson.Safe.t list =
    match x with
    | `List v -> v
    | _ -> invalid_arg "get_list"

  let get_assoc (x : Yojson.Safe.t) : (string * Yojson.Safe.t) list =
    match x with
    | `Assoc v -> v
    | _ -> invalid_arg "get_assoc"

  (* let rec term_of_json (x : Yojson.Safe.t) : Tg_ast.term =
     let l = get_assoc x in
        match List.assoc_opt "jgnFactName" l with
        | Some f -> (
          let f = get_string f in
            let args = List.assoc "jgnFactTerms" l
        |> get_list
                       |> List.map term_of_json
            in
            T_app { path = [ Loc.untagged f ]; name = `Local 0; named_args = []; args; anno = None }
          )
        | None -> (
            match List.assoc_opt "jgnFunct" l with
            | Some f -> (
              let f = get_string f in
            let args = List.assoc "jgnFactTerms" l
        |> get_list
                       |> List.map term_of_json
            in
            match f with
            | "pair" -> (
              T_tuple (None, args)
            )
            | _ -> (
            T_app { path = [ Loc.untagged f ]; name = `Local 0; named_args = []; args; anno = None }
            )
            )
            | None -> (
              match List.assoc_opt "jgnConst" l with
              | Some s -> (
                let s = get_string s in
                match Angstrom.parse_string ~consume:Angstrom.Consume.All Parsers.simple_term_p s with
                | Error msg -> invalid_arg msg
                | Ok x -> x
              )
              | None -> invalid_arg (Fmt.str "term_of_json: Unrecognized term structure %a" Yojson.Safe.pp x)
            )
          ) *)

  let fact_of_json (x : Yojson.Safe.t) : Tg_ast.term =
    let x = get_assoc x in
    let s = List.assoc "jgnFactShow" x
    |> get_string
    in
    match Angstrom.parse_string ~consume:Angstrom.Consume.All Parsers.term_p s with
    | Error msg -> invalid_arg msg
    | Ok x -> x

  let rule_of_json (x : Yojson.Safe.t) : rule =
    let x = get_assoc x in
    let metadata = List.assoc "jgnMetadata" x
                   |> get_assoc
    in
    let row_a = List.assoc "jgnActs" x
                |> get_list
                |> List.map fact_of_json
    in
    let row_r = List.assoc "jgnConcs" x
                |> get_list
                |> List.map (fun x ->
                    (x |> get_assoc |> List.assoc "jgnFactId" |> get_string, [ fact_of_json x ])
                  )
    in
    let row_l = List.assoc "jgnPrems" x
                |> get_list
                |> List.map (fun x ->
                    (x |> get_assoc |> List.assoc "jgnFactId" |> get_string, [ fact_of_json x ])
                  )
    in
    { name = get_string @@ List.assoc "jgnLabel" x;
      l = row_l;
      a_sub_node_name = Fmt.str "n%d" (get_num ());
      a_timepoint = get_string @@ List.assoc "jgnId" x;
      a = row_a;
      r = row_r;
    }

  let items_of_json (x : Yojson.Safe.t) : item list =
    let x = get_assoc x in
    let graph = List.assoc "graphs" x
                |> get_list
                |> List.hd
    in
    let edges =
      List.assoc "jgEdges" graph
      |> get_list
      |> List.map (fun x ->
          let x = get_assoc x in
          let src = List.assoc "jgeSource" x
      |> get_string
      |> dot_node_name_of_json_node_name
          in
          let dst = List.assoc "jgeTarget" x
      |> get_string
      |> dot_node_name_of_json_node_name
          in
          let attrs =
            match get_string @@ List.assoc "jgeRelation" x with
            | "default" ->
              [ ("color", "gray30"); ("style", "dashed") ]
            | "KFact" ->
              [ ("color", "oranged2"); ("style", "dashed") ]
            | "ProtoFact" ->
              [ ("style", "bold"); ("weight", "10.0") ]
            | "PersistentFact" ->
              [ ("style", "bold"); ("weight", "10.0"); ("color", "gray50") ]
            | "LessAtoms" ->
              [ ("color", "red"); ("style", "dashed")]
            | any -> invalid_arg (Fmt.str "items_of_json: Unrecognized jgeRelation: %s" any)
          in
          Edge { src; dst; attrs; }
        )
    in
    let nodes =
      List.assoc "jgNodes" graph
      |> get_list
      |> List.map (fun x ->
          let x = get_assoc x in
          let label = List.assoc "jgnLabel" x in
          let typ = List.assoc "jgnType" x in
          let metadata = List.assoc "jgnMetadata" x
                         |> get_assoc
          in
          match typ with
          | "isProtocolRule" -> (
              Rule_node (rule_of_json x)
            )
          | _ -> (
              match label with
              | "Send" -> Node { name = "send"; attrs = [] }
              | "Recv" -> Node { name = "recv"; attrs = [] }
              | "Coerce" -> Node { name = "send"; attrs = [] }
              | "FreshRule" -> (
                  let name = List.assoc "jgnConcs" metadata
                             |> get_list
                             |> List.hd
                             |> get_assoc
                             |> List.assoc "jgnFactShow"
                  in
                  Node { name; attrs = [] }
                )
              | x when CCString.prefix ~pre:"Constrc_" x -> (
                  let name = List.assoc "jgnConcs" metadata
                             |> get_list
                             |> List.hd
                             |> get_assoc
                             |> List.assoc "jgnFactShow"
                  in
                  Node { name; attrs = [] }
              )
              | x when CCString.prefix ~pre:"Destrd_" x -> (
                  let name = List.assoc "jgnConcs" metadata
                             |> get_list
                             |> List.hd
                             |> get_assoc
                             |> List.assoc "jgnFactShow"
                  in
                  Node { name; attrs = [] }
              )
              | _ -> invalid_arg (Fmt.str "Unrecognized label: %s" label)
            )
        )
    in
    nodes @@ edges
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
      Fmt.pf formatter "argv: @[%s@,@]" (String.concat " " argv)
    );
  match List.filter (fun s -> Filename.extension s = ".json") argv with
  | [] -> exit 1
  | json_file :: _ -> (
      Sys.command (Fmt.str "cp %s %s" json_file "tamgram-test0.json") |> ignore;
      let tg_file = "examples/csf18-xor/CH07.tg" in
      let res =
        let* root = Modul_load.from_file tg_file in
        let* spec =  Tg.run_pipeline (Spec.make root) in
        let+ items = load_dot_file dot_file in
        List.map (Rewrite.item spec) items
      in
      match res with
      | Error _ -> call ()
      | Ok items -> (
          (* Sys.command (Fmt.str "cp %s %s" json_file "tamgram-test0.json"); *)
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
    )

let () = run ()
