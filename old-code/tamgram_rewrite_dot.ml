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

module Printers = struct
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

module Parsers = struct
  open Angstrom
  open Parser_components

  let ident_string =
    take_while1 (fun c ->
        is_alphanum c || c = '_' || c = '.')

  let comment_line_p =
    string "//" *> skip_while (fun c -> c <> '\n') *> char '\n'

  let quoted_p =
    char '"' *> take_while (fun c -> c <> '"') >>= fun s ->
    char '"' *> spaces *> return s

  let single_quoted_p =
    char '\'' *> take_while (fun c -> c <> '\'') >>= fun s ->
    char '\'' *> spaces *> return s

  let kv_p : (string * string) t =
    ident_string >>= fun k ->
    spaces *> char '=' *> spaces *>
    quoted_p >>= fun v ->
    spaces *> return (k, v)

  let top_level_kv_p : item t =
    choice [
      string "nodesep";
      string "ranksep";
    ]
    >>= (fun k ->
        spaces *> char '=' *> spaces *>
        quoted_p >>= fun v ->
        return (Kv (k, v))
      )

  let square_bracket_kv_list_p =
    char '[' *> spaces *> sep_by comma kv_p >>= fun l ->
    char ']' *> spaces *> return l

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
          string "⊕" *> spaces *>
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

  let node_setting_p =
    string "node" *> spaces *> square_bracket_kv_list_p >>| fun l ->
    Node_settings l

  let edge_setting_p =
    string "edge" *> spaces *> square_bracket_kv_list_p >>| fun l ->
    Edge_settings l

  let rule_p : rule t =
    let sub_node_prefix_p =
      char '<' *> ident_string >>= fun sub_node_name ->
      char '>' *> spaces *> return sub_node_name
    in
    let sub_node_p =
      sub_node_prefix_p >>= fun sub_node_name ->
      fact_p >>= fun fact ->
      spaces *> return (sub_node_name, [fact])
    in
    let l_r_row_p =
      char '{' *> spaces *> sep_by (char '|') sub_node_p >>= fun l ->
      char '}' *> spaces *> return l
    in
    let a_row_p =
      char '{' *> sub_node_prefix_p >>= fun sub_node_name ->
      char '#' *> spaces *> ident_string >>= fun timepoint ->
      spaces *> char ':' *> spaces *> ident_string >>= fun name ->
      spaces *> char '[' *> sep_by comma fact_p >>= fun facts ->
      char ']' *> spaces *> char '}' *> spaces *>
      return (sub_node_name, timepoint, name, facts)
    in
    char '{' *> spaces *> l_r_row_p >>= fun l ->
    char '|' *> spaces *> a_row_p >>= fun (a_sub_node_name, a_timepoint, name, a) ->
    char '|' *> spaces *> l_r_row_p >>= fun r ->
    char '}' *> spaces *>
    return { name; a_sub_node_name; a_timepoint; l; a; r }

  let node_p =
    ident_string >>= fun name ->
    square_bracket_kv_list_p >>= (fun attrs ->
        match List.assoc_opt "shape" attrs with
        | None -> fail "Expected shape to be in list"
        | Some shape -> (
            if shape = "record" then (
              match List.assoc_opt "label" attrs with
              | None -> fail "Expected label to be in list"
              | Some label -> (
                  match parse_string ~consume:Consume.All rule_p label with
                  | Error _ -> fail "Failed to parse label"
                  | Ok rule -> (
                      let attrs = List.remove_assoc "label" attrs in
                      return (Rule_node { name; rule; attrs })
                    )
                )
            ) else (
              return (Node { name; attrs })
            )
          )
      )

  let edge_p =
    let target_p =
      ident_string >>= fun main ->
      option None (char ':' *> ident_string >>| Option.some) >>= fun sub ->
      return (main, sub)
    in
    target_p >>= fun src ->
    spaces *> string "->" *> spaces *>
    target_p >>= fun dst ->
    square_bracket_kv_list_p >>| fun attrs ->
    Edge { src; dst; attrs }

  let p : item list t =
    skip_many comment_line_p *>
    string "digraph" *> spaces *> string "G" *> spaces *> string "{" *>
    spaces *>
    many
      (
        (choice
           [ top_level_kv_p
           ; node_setting_p
           ; edge_setting_p
           ; node_p
           ; edge_p
           ])
        <* char ';' <* spaces
      )
    <* string "}" <* spaces
end

let load_dot_file file : (item list, Error_msg.t) result =
  CCIO.with_in file (fun ic ->
      let s = CCIO.read_all ic in
      match Angstrom.parse_string ~consume:Angstrom.Consume.All Parsers.p s with
      | Error msg -> Error (Error_msg.make_msg_only msg)
      | Ok l -> Ok l
    )

let call_dot (args : string list) =
  Sys.command (Fmt.str "dot %s" (String.concat " " args))

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

  let rewrite_rule (spec : Spec.t) (rule : rule) : rule =
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
    { rule with l; r }

  let item (spec : Spec.t) (x : item) : item =
    match x with
    | Rule_node { name; rule; attrs } -> (
        Rule_node { name; rule = rewrite_rule spec rule; attrs }
      )
    | _ -> x
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
  let call () =
    exit 1;
    exit (call_dot argv)
  in
  match Sys.getenv_opt "TG_FILE" with
  | None -> exit 1
  | Some tg_file -> (
      match argv with
      | [] | [ "-V" ] -> exit 1
      | _ -> (
          match List.filter (fun s -> Filename.extension s = ".dot") argv with
          | [] -> exit 1
          | dot_file :: _ -> (
              Sys.command (Fmt.str "cp %s %s" dot_file "tamgram-test0.dot");
              exit 0;
              let res =
                let* root = Modul_load.from_file tg_file in
                let* spec =  Tg.run_pipeline (Spec.make root) in
                let+ items = load_dot_file dot_file in
                List.map (Rewrite.item spec) items
              in
              match res with
              | Error _ -> call ()
              | Ok items -> (
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
        )
    )

(*let () =
   CCIO.with_in "test.dot" (fun ic ->
      let s = CCIO.read_all ic in
      match Angstrom.parse_string ~consume:Angstrom.Consume.All Parsers.p s with
      | Error msg -> Printf.printf "Error: %s\n" msg
      | Ok items -> (
          Fmt.pr "%a" Printers.pp_full items
      )
    )*)

let () = run ()
