type exit_bias = Tr_frame_minimal_hybrid0.exit_bias

let get_num : unit -> int =
  let counter = ref 0 in
  fun () ->
    let x = !counter in
    counter := x + 1;
    x

type row_element = [
  | `Empty_init_ctx
  | `Defs_and_undefs of (string * Tg_ast.term) list * string list
  | `Pat_matches of (string * Tg_ast.term) list
  | `Term of Tg_ast.term
]

type rule = {
  name : string;
  l : (string * row_element) list;
  a_sub_node_name : string;
  a_timepoint : string;
  a : Tg_ast.term list;
  r : (string * row_element) list;
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

type row = [ `L | `R ]

module Params = struct
  let proc_ctx_color = "gray80"

  let in_fact_color = "skyblue"

  let out_fact_color = "orange"
end

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
           | `Cell -> "'"
          )
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
              Fmt.pf formatter "@[<h>&lt;%a&gt;@]" Fmt.(list ~sep:comma aux) l
            )
        )
      | T_unary_op (op, x) ->
        Fmt.pf formatter "%s%a"
          (match op with `Persist -> "!" | `Not -> "not ")
          aux x
      | T_binary_op (op, x, y) -> (
          Fmt.pf formatter "%a %s %a"
            pp_binary_op_sub_term x
            (match op with
             | `Exp -> "^"
             | `Eq -> "="
             | `Iff -> "<=>"
             | `Imp -> "==>"
             | `Or -> "|"
             | `And -> "&"
             | `Plus -> "+"
             | `Xor -> "⊕"
            )
            pp_binary_op_sub_term y
        )
      | T_cell_assign (cell, term) -> (
          Fmt.pf formatter "'%s := %a" (Loc.content cell) aux term
        )
      | T_cell_pat_match (cell, term) -> (
          Fmt.pf formatter "'%s cas %a" (Loc.content cell) aux term
        )
      | _ -> failwith (Fmt.str "Unexpected case: %a" Printers.pp_term x)
    and pp_binary_op_sub_term formatter (x : Tg_ast.term) =
      match x with
      | T_value _
      | T_symbol _
      | T_var _
      | T_app _
      | T_tuple _
      | T_unary_op _ -> Fmt.pf formatter "%a" aux x
      | _ -> Fmt.pf formatter "(%a)" aux x
    in
    aux formatter x

  let pp_row_element (row : row) formatter ((sub_node, row_element) : (string * row_element)) =
    let pp_def formatter ((cell, term) : string * Tg_ast.term) =
      Fmt.pf formatter {|<tr><td align="left">'%s := %a</td></tr>|} cell pp_term term
    in
    let pp_undef formatter (cell : string) =
      Fmt.pf formatter {|<tr><td align="left">undef('%s)</td></tr>|} cell
    in
    let pp_pat_match formatter ((cell, term) : string * Tg_ast.term) =
      Fmt.pf formatter "<tr><td>'%s cas %a</td></tr>" cell pp_term term
    in
    let pp_prop formatter ((k, v) : string * string) =
      Fmt.pf formatter "%s=\"%s\"" k v
    in
    let pp_props formatter l =
      Fmt.pf formatter "%a" Fmt.(list ~sep:sp pp_prop) l
    in
    let props =
      match row_element with
      | `Empty_init_ctx
      | `Defs_and_undefs _
      | `Pat_matches _ ->
        [ ("port", sub_node)
        ; ("border", "1")
        ; ("bgcolor", Params.proc_ctx_color) ]
      | `Term x -> (
          (match x with
           | T_app { path = [ name ]; args; _ } -> (
               let name = Loc.content name in
               match name with
               | "In" -> [ ("bgcolor", Params.in_fact_color) ]
               | "Out" -> [ ("bgcolor", Params.out_fact_color) ]
               | _ -> []
             )
           | _ -> []
          )
          @
          [ ("port", sub_node); ("border", "1") ]
        )
    in
    Fmt.pf formatter {|<td %a>%a</td>|}
      pp_props props
      (fun formatter row_element ->
         match row_element with
         | `Empty_init_ctx -> (
             Fmt.pf formatter "Empty init ctx"
           )
         | `Defs_and_undefs (defs, undefs) -> (
             match defs, undefs with
             | [], [] -> (
                 Fmt.pf formatter "Unchanged ctx"
               )
             | _, _ -> (
                 Fmt.pf formatter {|<table %a>|}
                   pp_props
                   [ ("border", "0")
                   ; ("cellborder", "0")
                   ; ("cellspacing", "0")
                   ; ("cellpadding", "0")
                   ];
                 Fmt.pf formatter "%a%a"
                   Fmt.(list ~sep:comma pp_def) defs
                   Fmt.(list ~sep:comma pp_undef) undefs;
                 Fmt.pf formatter "</table>"
               )
           )
         | `Pat_matches l -> (
             match l with
             | [] -> Fmt.pf formatter "..."
             | _ -> (
                 Fmt.pf formatter {|<table border="0" cellborder="0" cellspacing="0" cellpadding="0">|};
                 Fmt.pf formatter "%a" Fmt.(list pp_pat_match) l;
                 Fmt.pf formatter "</table>"
               )
           )
         | `Term x -> (
             Fmt.pf formatter "%a" pp_term x
           )
      )
      row_element

  let pp_l_row formatter (l : (string * row_element) list) =
    match l with
    | [] -> Fmt.pf formatter "<td></td>"
    | _ -> (
        Fmt.pf formatter "%a"
          Fmt.(list (pp_row_element `L))
          l
      )

  let pp_r_row formatter (l : (string * row_element) list) =
    match l with
    | [] -> Fmt.pf formatter "<td></td>"
    | _ -> (
        Fmt.pf formatter "%a"
          Fmt.(list (pp_row_element `R))
          l
      )

  let pp_a_row formatter (rule : rule) =
    let pp_term formatter x =
      Fmt.pf formatter
        {|<tr><td>%a</td></tr>|}
        pp_term x
    in
    let pp_terms formatter l =
      match l with
      | [] -> Fmt.pf formatter "<tr><td></td></tr>"
      | _ -> Fmt.pf formatter "%a" Fmt.(list pp_term) l
    in
    Fmt.pf formatter
      {|
      <td port="%s" border="1">
          #%s : %s
      </td>
      |}
      rule.a_sub_node_name
      rule.a_timepoint
      rule.name
    ;
    (match rule.a with
     | [] -> ()
     | _ -> (
         Fmt.pf formatter
           {|
      <td border="1">
          <table border="0" cellborder="0" cellspacing="0" cellpadding="0">
              %a
          </table>
      </td>
      |}
           pp_terms
           rule.a
       )
    )

  let pp_rule formatter (rule : rule) =
    Fmt.pf formatter {|<table border="0" cellborder="0" cellspacing="0" cellpadding="0">|};
    Fmt.pf formatter
      {|<tr>
              <td>
                  <table border="0" cellspacing="0">
                      <tr>%a</tr>
                  </table>
              </td>
        </tr>|}
      pp_l_row rule.l;
    Fmt.pf formatter
      {|<tr>
              <td>
                  <table border="0" cellspacing="0">
                      <tr>%a</tr>
                  </table>
              </td>
        </tr>|}
      pp_a_row rule;
    Fmt.pf formatter
      {|<tr>
              <td>
                  <table border="0" cellspacing="0">
                      <tr>%a</tr>
                  </table>
              </td>
        </tr>|}
      pp_r_row rule.r;
    Fmt.pf formatter {|</table>|}

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
    Fmt.pf formatter "%s[label=<%a>%a]"
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
            (string "<" *> spaces *> sep_by comma exp >>= fun terms ->
             string ">" *>
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

let term_of_string (s : string) : Tg_ast.term =
  match Angstrom.parse_string ~consume:Angstrom.Consume.All Parsers.fact_p s with
  | Error msg -> invalid_arg (Fmt.str "Failed to parse fact string: %s: %s" msg s)
  | Ok x -> x

let rule_indices_of_rule_name (s : string) : (int option * int * int option) option =
  let parts = String.split_on_char '_' s in
  let parse_rule_id (s : string) =
    let exception Fail in
    let parse_int s =
      match int_of_string_opt s with
      | None -> raise Fail
      | Some x -> x
    in
    try
      match CCString.split ~by:"To" s with
      | [ pred; k; succ ] -> (
          let k = parse_int k in
          let pred =
            match pred with
            | "None" | "Many" -> None
            | s -> Some (parse_int s)
          in
          let succ =
            match succ with
            | "None" | "Many" -> None
            | s -> Some (parse_int s)
          in
          Some (pred, k, succ)
        )
      | _ -> raise Fail
    with
    | Fail -> None
  in
  let rec aux possible parts =
    match parts with
    | [] | [_] -> possible
    | x :: y :: xs -> (
        match int_of_string_opt x, parse_rule_id y with
        | Some _, Some k -> aux (Some k) (y :: xs)
        | _, _ -> aux possible (y :: xs)
      )
  in
  aux None parts

let dot_node_name_of_json_node_id : string -> string * string option =
  let tbl : (string, string * string option) Hashtbl.t = Hashtbl.create 1024 in
  fun s ->
    let (node, sub_node) =
      match String.split_on_char ':' s with
      | [ node ] -> (node, None)
      | [ node; sub_node ] -> (node, Some sub_node)
      | _ -> invalid_arg (Fmt.str "Too many parts in node name: %s" s)
    in
    let dot_node =
      match Hashtbl.find_opt tbl node with
      | None -> (
          Fmt.str "n%d" (get_num ())
        )
      | Some (name, _) -> name
    in
    let dot_sub_node =
      match sub_node with
      | None -> None
      | Some sub_node -> (
          match Hashtbl.find_opt tbl s with
          | None -> (
              Some (Fmt.str "n%d" (get_num ()))
            )
          | Some (_, name) -> name
        )
    in
    Hashtbl.add tbl node (dot_node, None);
    Hashtbl.add tbl s (dot_node, dot_sub_node);
    (dot_node, dot_sub_node)

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
    term_of_string s

  let rule_of_json (x : Yojson.Safe.t) : rule =
    let x = get_assoc x in
    let metadata = List.assoc "jgnMetadata" x
                   |> get_assoc
    in
    let compute_sub_node_name x =
      x
      |> get_assoc
      |> List.assoc "jgnFactId"
      |> get_string
      |> dot_node_name_of_json_node_id
      |> snd
      |> Option.get
    in
    let row_a = List.assoc "jgnActs" metadata
                |> get_list
                |> List.map fact_of_json
    in
    let row_r = List.assoc "jgnConcs" metadata
                |> get_list
                |> List.map (fun x ->
                    (compute_sub_node_name x, `Term (fact_of_json x))
                  )
    in
    let row_l = List.assoc "jgnPrems" metadata
                |> get_list
                |> List.map (fun x ->
                    (compute_sub_node_name x, `Term (fact_of_json x))
                  )
    in
    let a_timepoint = List.assoc "jgnId" x
                      |> get_string
                      |> (fun s ->
                          Option.value ~default:s (CCString.chop_prefix ~pre:"#" s))
    in
    { name = get_string @@ List.assoc "jgnLabel" x;
      l = row_l;
      a_sub_node_name = Fmt.str "n%d" (get_num ());
      a_timepoint;
      a = row_a;
      r = row_r;
    }

  let items_of_json (x : Yojson.Safe.t) : item list =
    let x = get_assoc x in
    let graph = List.assoc "graphs" x
                |> get_list
                |> List.hd
                |> get_assoc
    in
    let edges =
      List.assoc "jgEdges" graph
      |> get_list
      |> List.map (fun x ->
          let x = get_assoc x in
          let src = List.assoc "jgeSource" x
                    |> get_string
                    |> dot_node_name_of_json_node_id
          in
          let dst = List.assoc "jgeTarget" x
                    |> get_string
                    |> dot_node_name_of_json_node_id
          in
          let attrs =
            match get_string @@ List.assoc "jgeRelation" x with
            | "default" ->
              [ ("color", "gray30"); ("style", "dashed") ]
            | "KFact" ->
              [ ("color", "orangered2"); ("style", "dashed") ]
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
    let clean_up_fact_label label =
      label
      |> term_of_string
      |> Fmt.str "%a" Dot_printers.pp_term
    in
    let nodes =
      List.assoc "jgNodes" graph
      |> get_list
      |> List.map (fun x' ->
          let x = get_assoc x' in
          let typ = List.assoc "jgnType" x |> get_string in
          let metadata = List.assoc "jgnMetadata" x
                         |> get_assoc
          in
          let jgn_label = List.assoc "jgnLabel" x |> get_string in
          let name = List.assoc "jgnId" x
                     |> get_string
                     |> dot_node_name_of_json_node_id
                     |> fst
          in
          match typ with
          | "isProtocolRule" | "isIntruderRule" | "isFreshRule" -> (
              let rule = rule_of_json x' in
              Rule_node { name; rule; attrs = [ ("shape", "none") ] }
            )
          | "unsolvedActionAtom" -> (
              Node { name; attrs = [ ("label", clean_up_fact_label jgn_label) ] }
            )
          | _ -> (
              match jgn_label with
              (* | "Send" -> Node { name; attrs = [ ("label", "send") ] }
                 | "Recv" -> Node { name; attrs = [ ("label", "recv") ] }
                 | "Coerce" -> Node { name; attrs = [ ("label", "coerce") ] } *)
              (* | "FreshRule" -> (
                  let label = List.assoc "jgnConcs" metadata
                             |> get_list
                             |> List.hd
                             |> get_assoc
                             |> List.assoc "jgnFactShow"
                             |> get_string
                  in
                  Node { name; attrs = [] }
                 ) *)
              | x when CCString.prefix ~pre:"Constrc_" x -> (
                  let label = List.assoc "jgnConcs" metadata
                              |> get_list
                              |> List.hd
                              |> get_assoc
                              |> List.assoc "jgnFactShow"
                              |> get_string
                  in
                  Node { name; attrs = [ ("label", clean_up_fact_label label) ] }
                )
              | x when CCString.prefix ~pre:"Destrd_" x -> (
                  let label = List.assoc "jgnConcs" metadata
                              |> get_list
                              |> List.hd
                              |> get_assoc
                              |> List.assoc "jgnFactShow"
                              |> get_string
                  in
                  Node { name; attrs = [ ("label", clean_up_fact_label label) ] }
                )
              | _ -> invalid_arg (Fmt.str "Unrecognized jgnLabel: %s" jgn_label)
            )
        )
    in
    nodes @ edges
end

module Rewrite = struct
  let write_cell_operations
      (spec : Spec.t)
      (row : row)
      ~pred
      ~k
      ~succ
      (exit_bias : exit_bias)
      ~(cell_contents : Tg_ast.term list)
    : row_element =
    let open Tg_ast in
    let cell_usage = Int_map.find k spec.cell_usages in
    let cells_defined = Cell_lifetime.Usage.defines_cells cell_usage in
    let cells_undefined = Cell_lifetime.Usage.undefines_cells cell_usage in
    let user_specified_pat_matches = Int_map.find k spec.user_specified_cell_pat_matches in
    match row with
    | `L -> (
        `Pat_matches
          (user_specified_pat_matches
           |> List.map (fun (cell, pat) -> (Loc.content cell, pat))
          )
      )
    | `R -> (
        let ctx =
          (match exit_bias with
           | `Forward -> (
               match succ with
               | None -> String_tagged_set.empty
               | Some succ -> (
                   Int_map.find succ spec.cells_to_carry_over_before
                 )
             )
           | `Backward -> (
               Int_map.find k spec.cells_to_carry_over_after
             )
           | `Empty -> String_tagged_set.empty)
        in
        let assigns =
          List.combine
            (ctx
             |> String_tagged_set.to_seq
             |> Seq.map Loc.content
             |> List.of_seq)
            cell_contents
        in
        let defs = String_tagged_set.inter cells_defined ctx
                   |> String_tagged_set.to_seq
                   |> Seq.map (fun cell ->
                       (Loc.content cell, List.assoc (Loc.content cell) assigns)
                     )
                   |> List.of_seq
        in
        let undefs = cells_undefined
                     |> String_tagged_set.to_seq
                     |> Seq.map Loc.content
                     |> List.of_seq
        in
        match defs, undefs with
        | [], [] -> (
            match pred with
            | None -> `Empty_init_ctx
            | _ -> `Defs_and_undefs (defs, undefs)
          )
        | _, _ -> `Defs_and_undefs (defs, undefs)
      )

  let rewrite_state_fact (spec : Spec.t) ~pred ~k ~succ (row : row) (x : row_element) : row_element =
    let open Tg_ast in
    (* CCIO.with_out_a "tamgram-test.log" (fun oc ->
        let formatter = Format.formatter_of_out_channel oc in
        Fmt.pf formatter "@[<v>%a@,@]@." Printers.pp_term x;
        flush oc
       ); *)
    let default = x in
    let exception Fail in
    try
      let x =
        match x with
        | `Term x -> x
        | _ -> raise Fail
      in
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
        | [ _pid; T_value vertex; _frame ] -> (
            match Loc.content vertex with
            | `Str vertex -> vertex
            | _ -> raise Fail
          )
        | _ -> raise Fail
      in
      let cell_contents =
        match args with
        | [ _pid; _vertex; frame ] -> (
            match frame with
            | T_value v -> (
                match Loc.content v with
                | `Str "empty_tuple" -> []
                | _ -> raise Fail
              )
            | T_tuple (_loc, l) -> l
            | x -> [ x ]
          )
        | _ -> raise Fail
      in
      CCIO.with_out_a "tamgram-test.log" (fun oc ->
          let formatter = Format.formatter_of_out_channel oc in
          Fmt.pf formatter "vertex: %s@," vertex
        );
      write_cell_operations spec row ~pred ~k ~succ exit_bias ~cell_contents
    with
    | Fail -> default

  let rewrite_rule (spec : Spec.t) (rule : rule) : rule =
    match rule_indices_of_rule_name rule.name with
    | None -> rule
    | Some (pred, k, succ) -> (
        let rewrite_sub_nodes (row : row) (sub_nodes : (string * row_element) list) =
          List.map (fun (sub_node, row_element) ->
              (sub_node,
               rewrite_state_fact spec ~pred ~k ~succ row row_element
              )
            )
            sub_nodes
        in
        let l = rewrite_sub_nodes `L rule.l in
        let r = rewrite_sub_nodes `R rule.r in
        { rule with l; r }
      )

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
  match List.filter (fun s -> Filename.extension s = ".json") argv with
  | [] -> invalid_arg "No JSON file provided"
  | json_file :: _ -> (
      (* Sys.command (Fmt.str "cp %s %s" json_file "tamgram-test0.json") |> ignore; *)
      let tg_file = "examples/csf18-xor/CH07.tg" in
      let json =
        CCIO.with_in json_file (fun ic ->
            CCIO.read_all ic
            |> Yojson.Safe.from_string
          )
      in
      let res =
        let* root = Modul_load.from_file tg_file in
        let+ spec =  Tg.run_pipeline (Spec.make root) in
        let items = JSON_parsers.items_of_json json
                    |> (fun l ->
                        [ Kv ("nodesep", "0.3"); Kv ("ranksep", "0.3") ] @ l
                      )
        in
        List.map (Rewrite.item spec) items
      in
      match res with
      | Error _ -> invalid_arg "Failed to parse Tamgram file"
      | Ok items -> (
          (* Sys.command (Fmt.str "cp %s %s" json_file "tamgram-test0.json"); *)
          CCIO.with_out ~flags:[Open_creat; Open_trunc; Open_binary] "tamgram-test1.dot" (fun oc ->
              let formatter = Format.formatter_of_out_channel oc in
              Fmt.pf formatter "%a@." Dot_printers.pp_full items
            );
          exit (call_dot [ "-Tpng"; "-o"; "tamgram-test1.png"; "tamgram-test1.dot" ])
        )
    )

let () = run ()
