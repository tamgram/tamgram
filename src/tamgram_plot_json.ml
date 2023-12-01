open Option_syntax

type exit_bias = Tr_frame_minimal_hybrid0.exit_bias

type link_target = Tr_frame_minimal_hybrid0.link_target

let pp_link_target = Tr_frame_minimal_hybrid0.pp_link_target

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

type rule_typ = [
  | `Protocol
  | `Intruder
  | `Fresh
]

type proc_step_info = {
  proc_name : string;
  pred : link_target;
  k : int;
  succ : link_target;
  step_tag : string;
}

let rule_indices_of_step_id (s : string) : (link_target * int * link_target) option =
  let parts = String.split_on_char '_' s in
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
          | "None" -> `None
          | "Many" -> `Many
          | s -> `Index (parse_int s)
        in
        let succ =
          match succ with
          | "None" -> `None
          | "Many" -> `Many
          | s -> `Index (parse_int s)
        in
        Some (pred, k, succ)
      )
    | _ -> raise Fail
  with
  | Fail -> None

let proc_step_info_of_string (s : string) =
  match CCString.split ~by:"___" s with
  | [ proc_name; step_id ] -> (
      let+ (pred, k, succ) = rule_indices_of_step_id step_id in
      { proc_name; pred; k; succ; step_tag = "" }
    )
  | [ proc_name; step_id; step_tag ] -> (
      let+ (pred, k, succ) = rule_indices_of_step_id step_id in
      { proc_name; pred; k; succ; step_tag }
    )
  | _ -> None

type rule = {
  name : string;
  typ : rule_typ;
  proc_step_info : proc_step_info option;
  l : (string * row_element) list;
  a_sub_node_name : string;
  a_timepoint : string;
  a : Tg_ast.term list;
  r : (string * row_element) list;
}

type rule_node = {
  root_node_name : string;
  rule : rule;
  attrs : (string * string) list;
}

type fact_node = {
  root_node_name : string;
  fact : Tg_ast.term;
  attrs : (string * string) list;
}

type text_node = {
  root_node_name : string;
  value : string;
  attrs : (string * string) list;
}

type node = [
  | `Rule of rule_node
  | `Intruder_fact of fact_node
  | `Intruder_text of text_node
]

type edge = {
  src : string * string option;
  dst : string * string option;
  attrs : (string * string) list;
}

type node_name = string * string option

let compare_node_name ((x_root, x_sub) : node_name) ((y_root, y_sub) : node_name) =
  let r = String.compare x_root y_root in
  if r = 0 then (
    match x_sub, y_sub with
    | None, None -> 0
    | Some _, None -> -1
    | None, Some _ -> 1
    | Some x, Some y -> String.compare x y
  ) else (
    r
  )

module Node_name_map = CCMap.Make (struct
    type t = node_name

    let compare = compare_node_name
  end)

module Node_name_set = CCSet.Make (struct
    type t = node_name

    let compare = compare_node_name
  end)

module Graph = struct
  type t = {
    key_values : string String_map.t;
    node_settings : string String_map.t;
    root_nodes : node String_map.t;
    sub_nodes_of_root_node : String_set.t String_map.t;
    edges : Node_name_set.t Node_name_map.t;
    edges_backward : Node_name_set.t Node_name_map.t;
  }

  let empty : t =
    { key_values = String_map.empty;
      node_settings = String_map.empty;
      root_nodes = String_map.empty;
      sub_nodes_of_root_node = String_map.empty;
      edges = Node_name_map.empty;
      edges_backward = Node_name_map.empty;
    }

  let record_node_name ((root, sub) : node_name) (t : t) : t =
    match sub with
    | None -> t
    | Some sub -> (
        let sub_nodes =
          Option.value ~default:String_set.empty
            (String_map.find_opt root t.sub_nodes_of_root_node)
          |> String_set.add sub
        in
        { t with
          sub_nodes_of_root_node = String_map.add root sub_nodes t.sub_nodes_of_root_node
        }
      )

  let add_kv (k : string) (v : string) (t : t) : t =
    { t with key_values = String_map.add k v t.key_values }

  let add_node_setting k v (t : t) =
    { t with node_settings = String_map.add k v t.node_settings }

  let add_edge (src : node_name) (dst : node_name) (t : t) : t =
    let t = t
            |> record_node_name src
            |> record_node_name dst
    in
    let edges =
      let destinations =
        Option.value ~default:Node_name_set.empty
          (Node_name_map.find_opt src t.edges)
        |> Node_name_set.add dst
      in
      Node_name_map.add src destinations t.edges
    in
    let edges_backward =
      let sources =
        Option.value ~default:Node_name_set.empty
          (Node_name_map.find_opt dst t.edges_backward)
        |> Node_name_set.add src
      in
      Node_name_map.add dst sources t.edges_backward
    in
    { t with
      edges;
      edges_backward;
    }

  let remove_edge (src : node_name) (dst : node_name) (t : t) : t =
    t
    |> (fun t ->
        match Node_name_map.find_opt src t.edges with
        | None -> t
        | Some dsts -> (
            let dsts = Node_name_set.remove dst dsts in
            { t with edges = Node_name_map.add src dsts t.edges }
          )
      )
    |> (fun t ->
        match Node_name_map.find_opt dst t.edges_backward with
        | None -> t
        | Some srcs -> (
            let srcs = Node_name_set.remove src srcs in
            { t with edges_backward = Node_name_map.add dst srcs t.edges_backward }
          )
      )

  let remove_edge' ({ src; dst; _ } : edge) (t : t) : t =
    remove_edge src dst t

  let add_rule_node (root_node_name : string) (rule : rule) (t : t) : t =
    let attrs = [ ("shape", "none") ] in
    { t with
      root_nodes = String_map.add root_node_name (`Rule { root_node_name; rule; attrs }) t.root_nodes
    }

  let add_intruder_fact_node (root_node_name : string) (fact : Tg_ast.term) (t : t) : t =
    let attrs = [] in
    { t with
      root_nodes = String_map.add root_node_name (`Intruder_fact { root_node_name; fact; attrs }) t.root_nodes
    }

  let add_intruder_text_node (root_node_name : string) (value : string) (t : t) : t =
    let attrs = [] in
    { t with
      root_nodes = String_map.add root_node_name (`Intruder_text { root_node_name; value; attrs }) t.root_nodes
    }

  let children (x : node_name) t : node_name Seq.t =
    match Node_name_map.find_opt x t.edges with
    | None -> Seq.empty
    | Some dsts -> (
        Node_name_set.to_seq dsts
      )

  let parents (x : node_name) t : node_name Seq.t =
    match Node_name_map.find_opt x t.edges_backward with
    | None -> Seq.empty
    | Some srcs -> (
        Node_name_set.to_seq srcs
      )

  let move_sub_node_edges_to_root_node (root : string) (t : t) : t =
    let sub_nodes = Option.value ~default:String_set.empty
        (String_map.find_opt root t.sub_nodes_of_root_node)
    in
    String_set.to_seq sub_nodes
    |> Seq.fold_left (fun t sub_node ->
        let self = (root, Some sub_node) in
        let upper = (root, None) in
        t
        |> (fun t ->
            children self t
            |> Seq.fold_left (fun t child ->
                t
                |> remove_edge self child
                |> add_edge upper child
              )
              t
          )
        |> (fun t ->
            parents self t
            |> Seq.fold_left (fun t parent ->
                t
                |> remove_edge parent self
                |> add_edge parent upper
              )
              t
          )
      ) t

  let remove_root_node ~bridge_over (root : string) (t : t) : t =
    t
    |> move_sub_node_edges_to_root_node root
    |> (fun t ->
        let parents = parents (root, None) t in
        let children = children (root, None) t in
        (if bridge_over then (
            Seq.fold_left (fun (t : t) parent ->
                Seq.fold_left (fun (t : t) child ->
                    add_edge parent child t
                  ) t children
              ) t
              parents
          ) else (
           t
         ))
        |> (fun t ->
            Seq.fold_left (fun t parent ->
                remove_edge parent (root, None) t
              ) t parents
          )
        |> (fun t ->
            Seq.fold_left (fun t child ->
                remove_edge (root, None) child t
              ) t children
          )
      )
    |> (fun t ->
        { t with root_nodes = String_map.remove root t.root_nodes }
      )

  let row_element_of_node ((root, sub) : node_name) (t : t) : row_element option =
    match String_map.find_opt root t.root_nodes with
    | None -> None
    | Some x -> (
        match x with
        | `Intruder_text _ -> None
        | `Intruder_fact x -> (
            match sub with
            | None -> Some (`Term x.fact)
            | Some _ -> None
          )
        | `Rule x -> (
            let rule = x.rule in
            match sub with
            | None -> None
            | Some sub -> (
                List.fold_left (fun res row ->
                    match res with
                    | None -> List.assoc_opt sub row
                    | Some _ -> res
                  )
                  None
                  [ rule.l; rule.r ]
              )
          )
      )

  let attrs_of_edge ((x_root, x_sub) : node_name) ((y_root, y_sub) : node_name) (t : t) : (string * string) list =
    let x_root_node = String_map.find x_root t.root_nodes in
    let y_root_node = String_map.find y_root t.root_nodes in
    match x_root_node, y_root_node with
    | _, `Intruder_fact _
    | _, `Intruder_text _ -> [ ("color", "orangered2"); ]
    | `Intruder_fact _, _
    | `Intruder_text _, _ -> [ ]
    | `Rule x_rule_node, `Rule y_rule_node -> (
        match x_sub, y_sub with
        | None, None -> [ ("color", "gray60"); ("style", "dashed") ]
        | _, _ -> (
            match
              row_element_of_node (x_root, x_sub) t,
              row_element_of_node (y_root, y_sub) t
            with
            | Some `Empty_init_ctx, _
            | Some (`Defs_and_undefs _), _
            | Some (`Pat_matches _), _ ->
              [ ("color", "black")
              ; ("penwidth", "2.0")
              ]
            | Some (`Term _), _ -> []
            | _, _ -> []
          )
      )
end

type row = [ `L | `R ]

module Params = struct
  let proc_ctx_color = "gray80"

  let additional_info_color = "lightslategray"

  let step_tag_font_size = 20.0

  let in_fact_color = "skyblue"

  let out_fact_color = "orange"

  let fr_fact_color = "darkseagreen2"
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
        ; ("bgcolor", Params.proc_ctx_color) ]
      | `Term x -> (
          (match x with
           | T_app { path = [ name ]; args; _ } -> (
               let name = Loc.content name in
               match name with
               | "In" -> [ ("bgcolor", Params.in_fact_color) ]
               | "Out" -> [ ("bgcolor", Params.out_fact_color) ]
               | "Fr" -> [ ("bgcolor", Params.fr_fact_color) ]
               | _ -> []
             )
           | _ -> []
          )
          @
          [ ("port", sub_node) ]
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
    (match rule.proc_step_info with
     | None -> ()
     | Some { step_tag; _ } -> (
         if step_tag <> "" then (
           Fmt.pf formatter {|
      <td>
          <font point-size="%f">%s</font><font color="%s">(step label)</font>
      </td>
      |}
             Params.step_tag_font_size
             step_tag
             Params.additional_info_color
         )
       )
    );
    Fmt.pf formatter
      {|
      <td>
          #%s : %a
      </td>
      |}
      rule.a_timepoint
      (fun formatter rule ->
         match rule.proc_step_info with
         | None -> Fmt.string formatter rule.name
         | Some { proc_name; pred; k; succ; step_tag } -> (
             Fmt.pf formatter {|<font>%s</font>|}
               proc_name;
             Fmt.pf formatter {|<font color="%s">%aTo%dTo%a</font>|}
               Params.additional_info_color
               pp_link_target pred
               k
               pp_link_target succ;
           )
      )
      rule;
    (match rule.a with
     | [] -> ()
     | _ -> (
         Fmt.pf formatter
           {|
      <td>
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
                  <table border="0" cellspacing="0" cellborder="1" cellpadding="0">
                      <tr>%a</tr>
                  </table>
              </td>
        </tr>|}
      pp_l_row rule.l;
    Fmt.pf formatter
      {|<tr>
              <td port="%s">
                  <table border="0" cellspacing="0" cellborder="1" cellpadding="0">
                      <tr>%a</tr>
                  </table>
              </td>
        </tr>|}
      rule.a_sub_node_name
      pp_a_row rule;
    Fmt.pf formatter
      {|<tr>
              <td>
                  <table border="0" cellspacing="0" cellborder="1" cellpadding="0">
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
      x.root_node_name
      pp_rule x.rule
      pp_attrs_prefix_with_comma
      x.attrs

  let pp_fact_node formatter (x : fact_node) =
    Fmt.pf formatter {|%s["label"="%a"%a]|}
      x.root_node_name
      pp_term x.fact
      pp_attrs_prefix_with_comma x.attrs

  let pp_text_node formatter (x : text_node) =
    Fmt.pf formatter {|%s["label"="%s"%a]|}
      x.root_node_name
      x.value
      pp_attrs_prefix_with_comma x.attrs

  let pp_node_name formatter ((node, sub_node) : node_name) =
    match sub_node with
    | None -> Fmt.pf formatter "%s" node
    | Some sub_node -> Fmt.pf formatter "%s:%s" node sub_node

  let pp_graph formatter (g : Graph.t) =
    Fmt.pf formatter "@[<v>digraph G {@,@]";
    Fmt.pf formatter "  @[<v>";
    String_map.iter (fun k v ->
        Fmt.pf formatter "@[<h>%a@]@," pp_kv (k, v)
      )
      g.key_values;
    String_map.iter (fun k v ->
        Fmt.pf formatter "node[@[<h>%a@]]@," pp_kv (k, v)
      )
      g.node_settings;
    String_map.iter (fun _name node ->
        match node with
        | `Rule node -> Fmt.pf formatter "@[<h>%a@]@," pp_rule_node node
        | `Intruder_fact node -> Fmt.pf formatter "@[<h>%a@]@," pp_fact_node node
        | `Intruder_text node -> Fmt.pf formatter "@[<h>%a@]@," pp_text_node node
      )
      g.root_nodes;
    Node_name_map.iter (fun src dsts ->
        Node_name_set.iter (fun dst ->
            let attrs = Graph.attrs_of_edge src dst g in
            Fmt.pf formatter "@[<h>%a -> %a[%a]@]@,"
              pp_node_name src
              pp_node_name dst
              pp_attrs attrs
          ) dsts
      )
      g.edges;
    Fmt.pf formatter "@]@,}@]"

  (* let pp_item formatter (item : item) =
     Fmt.pf formatter "@[<h>";
     (match item with
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
     Fmt.pf formatter ";@,@]" *)

  (* let pp_full formatter (items : item list) =
     Fmt.pf formatter "@[<v>digraph G {@,@]";
     Fmt.pf formatter "  @[<v>%a"
      Fmt.(list pp_item) items;
     Fmt.pf formatter "@]@,}@]" *)
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

let node_name_of_json_node_id : string -> node_name =
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
    let typ =
      match List.assoc "jgnType" x |> get_string with
      | "isProtocolRule" -> `Protocol
      | "isIntruderRule" -> `Intruder
      | "isFreshRule" -> `Fresh
      | x -> invalid_arg (Fmt.str "rule_of_json: Invalid jgnType for rule: %s" x)
    in
    let compute_sub_node_name x =
      x
      |> get_assoc
      |> List.assoc "jgnFactId"
      |> get_string
      |> node_name_of_json_node_id
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
    let jgn_label = get_string @@ List.assoc "jgnLabel" x in
    { name = jgn_label;
      proc_step_info = proc_step_info_of_string jgn_label;
      typ;
      l = row_l;
      a_sub_node_name = Fmt.str "n%d" (get_num ());
      a_timepoint;
      a = row_a;
      r = row_r;
    }

  let graph_of_json (x : Yojson.Safe.t) : Graph.t =
    let x = get_assoc x in
    let json_graph = List.assoc "graphs" x
                     |> get_list
                     |> List.hd
                     |> get_assoc
    in
    let graph = Graph.empty in
    let graph =
      List.assoc "jgEdges" json_graph
      |> get_list
      |> List.fold_left (fun graph x ->
          let x = get_assoc x in
          let src = List.assoc "jgeSource" x
                    |> get_string
                    |> node_name_of_json_node_id
          in
          let dst = List.assoc "jgeTarget" x
                    |> get_string
                    |> node_name_of_json_node_id
          in
          (* let attrs =
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
             in *)
          Graph.add_edge src dst graph
        )
        graph
    in
    (*let clean_up_fact_label label =
      label
      |> term_of_string
      |> Fmt.str "%a" Dot_printers.pp_term
      in*)
    let graph =
      List.assoc "jgNodes" json_graph
      |> get_list
      |> List.fold_left (fun graph x' ->
          let x = get_assoc x' in
          let typ = List.assoc "jgnType" x |> get_string in
          let metadata = List.assoc "jgnMetadata" x
                         |> get_assoc
          in
          let jgn_label = List.assoc "jgnLabel" x |> get_string in
          let name = List.assoc "jgnId" x
                     |> get_string
                     |> node_name_of_json_node_id
                     |> fst
          in
          match typ with
          | "isProtocolRule" | "isIntruderRule" | "isFreshRule" -> (
              Graph.add_rule_node name (rule_of_json x') graph
            )
          | "unsolvedActionAtom" -> (
              Graph.add_intruder_fact_node name (term_of_string jgn_label) graph
            )
          | _ -> (
              (* if CCString.prefix ~pre:"Constrc_" jgn_label then (
                 let label = List.assoc "jgnConcs" metadata
                            |> get_list
                            |> List.hd
                            |> get_assoc
                            |> List.assoc "jgnFactShow"
                            |> get_string
                 in
                 Graph.add_text_node name (clean_up_fact_label label) graph
                 ) else if CCString.prefix ~pre:"Destrd_" jgn_label then (
                 let label = List.assoc "jgnConcs" metadata
                            |> get_list
                            |> List.hd
                            |> get_assoc
                            |> List.assoc "jgnFactShow"
                            |> get_string
                 in
                 Graph.add_text_node name (clean_up_fact_label label) graph
                 ) else (
                 invalid_arg (Fmt.str "Unrecognized jgnLabel: %s" jgn_label)
                 ) *)
              invalid_arg (Fmt.str "Unrecognized jgnType: %s" typ)
            )
        )
        graph
    in
    graph
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
               | `None -> String_tagged_set.empty
               | `Many -> invalid_arg "write_cell_operations: Invalid combination of exit_bias and succ link target"
               | `Index succ -> (
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
            | `None -> `Empty_init_ctx
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
    match rule.proc_step_info with
    | None -> rule
    | Some { pred; k; succ; _ } -> (
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

  module Stages = struct
    let rewrite_rules (spec : Spec.t) (g : Graph.t) : Graph.t =
      let root_nodes =
        String_map.map (fun node ->
            match node with
            | `Rule { root_node_name; rule; attrs } ->
              `Rule { root_node_name; rule = rewrite_rule spec rule; attrs }
            | _ -> node
          )
          g.root_nodes
      in
      { g with root_nodes }

    let simplify_intruder_nodes (g : Graph.t) : Graph.t =
      String_map.to_seq g.root_nodes
      |> Seq.fold_left (fun g (_root_node_name, node) ->
          match node with
          | `Rule { root_node_name; rule; attrs } -> (
              match rule.typ with
              | `Protocol -> (
                  g
                )
              | `Intruder -> (
                  if CCString.equal rule.name "Send" then (
                    g
                    |> Graph.move_sub_node_edges_to_root_node root_node_name
                    |> Graph.add_intruder_text_node root_node_name
                      (Fmt.str "#%s : isend" rule.a_timepoint)
                  ) else if CCString.equal rule.name "Recv" then (
                    g
                    |> Graph.move_sub_node_edges_to_root_node root_node_name
                    |> Graph.add_intruder_text_node root_node_name
                      (Fmt.str "#%s : irecv" rule.a_timepoint)
                  ) else if CCString.prefix ~pre:"Destrd" rule.name then (
                    g
                    |> Graph.remove_root_node ~bridge_over:true root_node_name
                  ) else if CCString.prefix ~pre:"Constrc" rule.name then (
                    g
                  ) else (
                    g
                  )
                )
              | `Fresh -> (
                  Graph.remove_root_node ~bridge_over:false root_node_name g
                )
            )
          | `Intruder_fact _ | `Intruder_text _ -> g
        )
        g

    let clean_up_root_node_edges (g : Graph.t) : Graph.t =
      Node_name_map.to_seq g.edges
      |> Seq.flat_map (fun (src, dsts) ->
          Node_name_set.to_seq dsts
          |> Seq.map (fun dst ->
              (src, dst)
            )
        )
      |> Seq.fold_left
        (fun g ((x_root, x_sub), (y_root, y_sub)) ->
           let g =
             match x_sub with
             | None -> g
             | Some _ -> (
                 g
                 |> Graph.remove_edge (x_root, None) (y_root, y_sub)
                 |> Graph.remove_edge (x_root, None) (y_root, None)
               )
           in
           match y_sub with
           | None -> g
           | Some _ -> (
               g
               |> Graph.remove_edge (x_root, x_sub) (y_root, None)
               |> Graph.remove_edge (x_root, None) (y_root, None)
             )
        )
        g
  end

  let graph (spec : Spec.t) (g : Graph.t) : Graph.t =
    g
    |> Stages.rewrite_rules spec
    |> Stages.simplify_intruder_nodes
    |> Stages.clean_up_root_node_edges
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
        let graph = JSON_parsers.graph_of_json json
                    |> Graph.add_kv "nodesep" "0.3"
                    |> Graph.add_kv "ranksep" "0.5"
                    |> Graph.add_node_setting "fontsize" "14"
        in
        Rewrite.graph spec graph
      in
      match res with
      | Error _ -> invalid_arg "Failed to parse Tamgram file"
      | Ok graph -> (
          CCIO.with_out ~flags:[Open_creat; Open_trunc; Open_binary] "tamgram-test1.dot" (fun oc ->
              let formatter = Format.formatter_of_out_channel oc in
              Fmt.pf formatter "%a@." Dot_printers.pp_graph graph
            );
          exit (call_dot [ "-Tpng"; "-o"; "tamgram-test1.png"; "tamgram-test1.dot" ])
        )
    )

let () = run ()
