open Result_let
open Cell_lifetime

module Cell_deps = struct
  type t = String_tagged_set.t String_tagged_map.t

  let empty : t = String_tagged_map.empty

  let a_deps_on_b ~a ~b (t : t) =
    let rec aux a b t =
      let s =
        Option.value
          ~default:String_tagged_set.empty
          (String_tagged_map.find_opt a t)
      in
      String_tagged_set.mem b s
      ||
      String_tagged_set.exists
        (fun x -> aux x b t) s
    in
    aux a b t
end

let rec usage_in_term (term : Tg_ast.term) : (Usage.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ -> Ok Usage.empty
    | T_symbol (name, sort) -> (
        match sort with
        | `Cell -> Ok Usage.(add_require name empty)
        | _ -> Ok Usage.empty)
    | T_name_as (x, _) -> aux x
    | T_var _ -> Ok Usage.empty
    | T_tuple (_, l) -> usage_in_terms l
    | T_app { path; args; _ } -> (
        match path with
        | [ x ] when Loc.content x = "undef" -> (
            match List.hd args with
            | T_symbol (name, `Cell) ->
              Ok Usage.(empty
                        |> add_undefine name
                        |> add_require name)
            | _ -> failwith "Unexpected case")
        | _ -> usage_in_terms args)
    | T_unary_op (_, x) -> aux x
    | T_binary_op (_, x, y) ->
      let* usage_x = aux x in
      let+ usage_y = aux y in
      Usage.union usage_x usage_y
    | T_cell_pat_match (x, y) ->
      let+ usage_y = aux y in
      Usage.add_require x usage_y
    | T_cell_assign (x, y) ->
      let+ usage_y = aux y in
      Usage.add_define x usage_y
    | T_let _ | T_let_macro _ | T_action _ | T_temporal_a_lt_b _
    | T_temporal_eq _ | T_quantified _ ->
      failwith "Unexpected case"
  in
  aux term

and usage_in_terms terms : (Usage.t, Error_msg.t) result =
  let rec aux acc terms =
    match terms with
    | [] -> Ok acc
    | x :: xs ->
      let* usage_x = usage_in_term x in
      aux (Usage.union usage_x acc) xs
  in
  aux Usage.empty terms

let check_no_cell_dep_cycles (terms : Tg_ast.term list)
  : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux cell_deps terms =
    match terms with
    | [] -> Ok ()
    | x :: xs ->
      match x with
      | T_cell_pat_match (x, y) ->
        let* usage_y = usage_in_term y in
        let cell_deps =
          String_tagged_map.add x (Usage.requires_cells usage_y) 
            cell_deps
        in
        if Cell_deps.a_deps_on_b ~a:x ~b:x cell_deps then
          Error
            (Error_msg.make
               (Loc.tag x)
               (Fmt.str "matching of cell '%s here causes dependency cycle"
                  (Loc.content x))
            )
        else
          aux cell_deps xs
      | _ ->
        aux cell_deps xs
  in
  aux Cell_deps.empty terms

let check_no_dup_pat_matches terms =
  let open Tg_ast in
  let rec aux seen terms =
    match terms with
    | [] -> Ok ()
    | x :: xs -> (
        match x with
        | T_cell_pat_match (cell, _) ->
          if String_tagged_set.mem cell seen then
            Error
              (Error_msg.make
                 (Loc.tag cell)
                 (Fmt.str
                    "Cell '%s is already used in a pattern match in this rule"
                    (Loc.content cell)))
          else aux (String_tagged_set.add cell seen) xs
        | _ -> aux seen xs)
  in
  aux String_tagged_set.empty terms

let usage_in_terms_no_dup_defines_undefines terms =
  let rec aux usage terms =
    match terms with
    | [] -> Ok usage
    | x :: xs -> (
        let* usage' = usage_in_term x in
        match
          String_tagged_set.(
            min_elt_opt
              (inter (Usage.defines_cells usage') (Usage.defines_cells usage)))
        with
        | Some x ->
          Error
            (Error_msg.make
               (Loc.tag x)
               (Fmt.str "Cell '%s is already defined in this rule"
                  (Loc.content x)))
        | None -> (
            match
              String_tagged_set.(
                min_elt_opt
                  (inter
                     (Usage.undefines_cells usage')
                     (Usage.undefines_cells usage)))
            with
            | Some x ->
              Error
                (Error_msg.make
                   (Loc.tag x)
                   (Fmt.str "Cell '%s is already undefined in this rule"
                      (Loc.content x))
                )
            | None -> aux (Usage.union usage' usage) xs))
  in
  aux Usage.empty terms

let usage_in_rule (rule : Tg_ast.rule) : (Usage.t, Error_msg.t) result =
  let open Tg_ast in
  let { l; a; r; _ } = rule in
  let* () = check_no_dup_pat_matches l in
  let* () = check_no_cell_dep_cycles l in
  let* usage_in_r = usage_in_terms_no_dup_defines_undefines r in
  match
    String_tagged_set.(
      min_elt_opt
        (inter
           (Usage.defines_cells usage_in_r)
           (Usage.undefines_cells usage_in_r)))
  with
  | Some x ->
    Error
      (Error_msg.make
         (Loc.tag x)
         (Fmt.str
            "Cannot define and undefine a cell in the same rule, '%s in this case"
            (Loc.content x))
      )
  | None ->
    let* usage_in_l = usage_in_terms l in
    let* usage_in_a = usage_in_terms a in
    let* usage_in_r = usage_in_terms r in
    let usages =
      [ usage_in_l; usage_in_a; usage_in_r ]
    in
    Ok
      (List.fold_left
         (fun acc x -> Usage.update ~so_far:acc x)
         Usage.empty usages)

let aux_graph (usages : Usage.t Int_map.t) (g : Tg_graph.t) : (Usage.t Int_map.t, Error_msg.t) result =
  let rec aux usages vertices =
    match vertices () with
    | Seq.Nil -> Ok usages
    | Seq.Cons ((id, ru), rest) ->
      let* usage =
        usage_in_rule ru
      in
      let usages =
        Int_map.add id usage usages
      in
      aux usages rest
  in
  aux usages (Graph.vertex_seq g)

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let rec aux (usages : Usage.t Int_map.t) (proc_graphs : (Name.t * Tg_graph.t) Seq.t) =
    match proc_graphs () with
    | Seq.Nil -> Ok usages
    | Seq.Cons ((_k, g), rest) ->
      let* usages = aux_graph usages g in
      aux usages rest
  in
  let+ cell_usages = aux Int_map.empty (Name_map.to_seq spec.proc_graphs) in
  { spec with cell_usages }
