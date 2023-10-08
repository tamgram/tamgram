type rule = {
  l : Tg_ast.term list;
  a : Tg_ast.term list;
  r : Tg_ast.term list;
}

type node = {
  label : rule;
  attrs : (string * string) list;
}

type edge = {
  src : string;
  dst : string;
  attrs : (string * string) list;
}

type item =
  | Kv of (string * string)
  | Node_settings of (string * string) list
  | Edge_settings of (string * string) list
  | Node of node
  | Edge of edge

module Parsers = struct
  open Angstrom
  open Parser_components

  let comment_line_p =
    string "//" *> skip_while (fun c -> c <> '\n') *> char '\n'

  let quoted_p =
    char '"' *> take_while (fun c -> c <> '"') >>= fun s ->
      char '"' *> spaces *> return s

  let kv_p : (string * string) t =
    take_while1 is_alphanum >>= fun k ->
      spaces *> char '=' *> spaces *>
      quoted_p >>= fun v ->
        spaces *> return (k, v)

  let top_level_kv_p : (string * string) t =
    choice [
      string "nodesep";
      string "ranksep";
    ]
    >>= fun k ->
      spaces *> char "=" *> spaces *>
      quoted_p >>= fun v ->
        return (k, v)

  let square_bracket_kv_list_p p =
    char '[' *> spaces *> sep_by (char ',' *> spaces) kv_p >>= fun l ->
    char ']' *> spaces *> return l

  let node_setting_p =
    string "node" *> spaces *> square_bracket_kv_list_p >>= fun l ->
      Node_settings l

  let edge_setting_p =
    string "edge" *> spaces *> square_bracket_kv_list_p >>= fun l ->
      Node_settings l

  let node_p =
    take_while1 is_alphanum >>= fun name ->
      square_bracket_kv_list_p >>= fun l ->
        Node

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
    *> string "}"
end

let () =
  Array.iter (fun x ->
    Printf.printf "%s\n" x
  ) Sys.argv;
  exit 0
