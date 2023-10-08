type rule = {
  name : string;
  l : (string * Tg_ast.term) list;
  a_sub_node_name : string;
  a_timepoint : string;
  a : Tg_ast.term list;
  r : (string * Tg_ast.term) list;
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

  let alphanum_string =
    take_while1 is_alphanum

  let comment_line_p =
    string "//" *> skip_while (fun c -> c <> '\n') *> char '\n'

  let quoted_p =
    char '"' *> take_while (fun c -> c <> '"') >>= fun s ->
    char '"' *> spaces *> return s

  let single_quoted_p =
    char '\'' *> take_while (fun c -> c <> '\'') >>= fun s ->
    char '\'' *> spaces *> return s

  let kv_p : (string * string) t =
    alphanum_string >>= fun k ->
    spaces *> char '=' *> spaces *>
    quoted_p >>= fun v ->
    spaces *> return (k, v)

  let top_level_kv_p : item t =
    choice [
      string "nodesep";
      string "ranksep";
    ]
    >>= fun k ->
    spaces *> char '=' *> spaces *>
    quoted_p >>= fun v ->
    return (Kv (k, v))

  let square_bracket_kv_list_p =
    char '[' *> spaces *> sep_by (char ',' *> spaces) kv_p >>= fun l ->
    char ']' *> spaces *> return l

  let name_p =
    alphanum_string >>| fun name ->
    Loc.untagged name

  let term_p =
    let open Tg_ast in
    fix (fun p ->
        choice [
          (single_quoted_p >>| fun s ->
           T_value (Loc.untagged (`Str s))
          );
          (char '$' *> spaces *> name_p >>| fun name ->
           T_symbol (name, `Pub)
          );
          (char '~' *> spaces *> name_p >>| fun name ->
           T_var ([name], `Local 0, Some `Fresh)
          );
          (char 'T' *>
           return (T_value (Loc.untagged `T))
          );
          (char 'F' *>
           return (T_value (Loc.untagged `F))
          );
          (name_p >>= fun f ->
           spaces *> char '(' *> spaces *>
           sep_by (char ',' *> spaces) p >>= fun args ->
           spaces *> char ')' *>
           return (T_app {
               path = [ f ];
               name = `Local 0;
               named_args = [];
               args;
               anno = None
             })
          );
        ]
        <* spaces
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
      char '<' *> alphanum_string >>= fun sub_node_name ->
      char '>' *> spaces *> return sub_node_name
    in
    let sub_node_p =
      sub_node_prefix_p >>= fun sub_node_name ->
      fact_p >>= fun fact ->
      spaces *> return (sub_node_name, fact)
    in
    let l_r_row_p =
      char '{' *> spaces *> many sub_node_p >>= fun l -> char '}' *> spaces *> return l
    in
    let a_row_p =
      char '{' *> sub_node_prefix_p >>= fun sub_node_name ->
      char '#' *> spaces *> alphanum_string >>= fun timepoint ->
      spaces *> char ':' *> spaces *> alphanum_string >>= fun name ->
      spaces *> char '[' *> many fact_p >>= fun facts ->
      char ']' *> spaces *>
      return (sub_node_name, timepoint, name, facts)
    in
    char '{' *> spaces *> l_r_row_p >>= fun l ->
    char '|' *> spaces *> a_row_p >>= fun (a_sub_node_name, a_timepoint, name, a) ->
    char '|' *> spaces *> l_r_row_p >>= fun r ->
    return { name; a_sub_node_name; a_timepoint; l; a; r }

  let node_p =
    alphanum_string >>= fun name ->
    square_bracket_kv_list_p >>= (fun attrs ->
        match List.assoc_opt "shape" attrs with
        | None -> fail ""
        | Some shape -> (
            if shape = "record" then (
              match List.assoc_opt "label" attrs with
              | None -> fail ""
              | Some label -> (
                  match parse_string ~consume:Consume.All rule_p label with
                  | Error _ -> fail ""
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
      alphanum_string >>= fun main ->
      option None (char ':' *> alphanum_string >>| Option.some) >>= fun sub ->
      return (main, sub)
    in
    target_p >>= fun src ->
    spaces *> string "->" *> spaces *>
    target_p >>= fun dst ->
    square_bracket_kv_list_p >>| fun attrs ->
    Edge { src; dst; attrs }

  let p : item list t =
    skip_many comment_line_p *>
    string "diagram" *> spaces *> string "G" *> spaces *> string "{" *>
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
    <* string "}"
end

let () =
  Array.iter (fun x ->
      Printf.printf "%s\n" x
    ) Sys.argv;
  exit 0
