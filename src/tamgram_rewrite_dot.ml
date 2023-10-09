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
    Node_settings l

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

(* let () =
   CCIO.with_in "examples/test.dot" (fun ic ->
      let s = CCIO.read_all ic in
      match Angstrom.parse_string ~consume:Angstrom.Consume.All Parsers.p s with
      | Error msg -> Printf.printf "Error: %s\n" msg
      | Ok l -> Printf.printf "item count: %d\n" (List.length l)
    ) *)

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

  let rewrite_frame
      (spec : Spec.t)
      (row : row)
      ~k
      (exit_bias : exit_bias)
      (frame : Tg_ast.term list)
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
               T_cell_assign (cell, T_value (Loc.untagged `T))
             ))
        |> List.of_seq
      )

  let rewrite_state_fact (spec : Spec.t) (row : row) (x : Tg_ast.term) : Tg_ast.term list =
    let open Tg_ast in
    let default = [ x ] in
    match x with
    | T_app { path; args; _ } -> (
        match path with
        | [ name ] -> (
            let name = Loc.content name in
            if List.mem name [ "StF"; "StB"; "St" ] then (
              let exit_bias =
                match name with
                | "StF" -> `Forward
                | "StB" -> `Backward
                | "St" -> `Empty
                | _ -> failwith "Unexpected case"
              in
              match args with
              | [ pid; T_value vertex; T_tuple (_loc, frame) ] -> (
                  let vertex = Loc.content vertex in
                  match vertex with
                  | `Str vertex -> (
                      if String.length vertex > 3
                      && StringLabels.sub ~pos:0 ~len:3 vertex = Params.graph_vertex_label_prefix
                      then (
                        match
                          int_of_string_opt
                            (StringLabels.sub ~pos:3 ~len:(String.length vertex-3) vertex)
                        with
                        | None -> default
                        | Some k -> (
                            rewrite_frame spec row ~k exit_bias frame
                          )
                      ) else (
                        default
                      )
                    )
                  | _ -> default
                )
              | _ -> default
            ) else (
              default
            )
          )
        | _ -> default
      )
    | _ -> default

  let rewrite_rule (spec : Spec.t) (rule : rule) : rule =
    let rewrite_sub_nodes (row : row) (sub_nodes : (string * Tg_ast.term list) list) =
      CCList.map (fun (sub_node, terms) ->
          (sub_node,
           CCList.flat_map (fun term ->
               rewrite_state_fact spec `L term
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
  let argv = Array.to_list Sys.argv in
  let call () =
    exit (call_dot argv)
  in
  match Sys.getenv_opt "TG_FILE" with
  | None -> call ()
  | Some tg_file -> (
      match argv with
      | [] | [ "-V" ] -> call ()
      | _ -> (
          match List.filter (fun s -> Filename.extension s = ".dot") argv with
          | [] -> call ()
          | dot_file :: _ -> (
              let* root = Modul_load.from_file tg_file in
              let* spec =  Tg.run_pipeline (Spec.make root) in
              let+ items = load_dot_file dot_file in
              List.map (Rewrite.item spec) items
            )
        )
    )

let () =
  match run () with
  | Error msg -> (
      Error_msg.print String_map.empty msg
    )
  | Ok items -> (
    )
