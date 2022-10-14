let pp_name_of_proc formatter (binding : 'a Binding.t) =
  Fmt.pf formatter "%s_%d"
    (Loc.content @@ Binding.name_str binding)
    (match Binding.name binding with
     | `Global x -> x
     | _ -> failwith "Unexpected case")

let placeholder_var_of_cell (c : string) : Tg_ast.term =
  T_var
    (Path.of_string (Printf.sprintf "%s%s" Params.cell_name_prefix c),
     `Global 0,
     None)

let replace_cells_with_placeholder_vars (x : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux x =
    match x with
    | T_value _ -> x
    | T_symbol (c', sort) -> (
        match sort with
        | `Cell ->
          placeholder_var_of_cell (Loc.content c')
        | _ -> x
      )
    | T_var _ -> x
    | T_tuple (loc, l) -> T_tuple (loc, List.map aux l)
    | T_app (path, name, args, anno) ->
      T_app (path, name, List.map aux args, anno)
    | T_unary_op (op, x) ->
      T_unary_op (op, aux x)
    | T_binary_op (op, x, y) ->
      T_binary_op (op, aux x, aux y)
    | T_cell_assign (c, x) ->
      T_cell_assign (c, aux x)
    | T_cell_pat_match (c, x) ->
      T_cell_pat_match (c, aux x)
    | T_name_as (x, name) ->
      T_name_as (aux x, name)
    | T_let _ | T_let_macro _ | T_action _
    | T_temporal_a_lt_b _
    | T_temporal_eq _
    | T_quantified _ -> x
  in
  aux x

let clean_up_l
    cell_subs
    (terms : Tg_ast.term list)
  : Tg_ast.term list =
  List.map (Term.replace_cells_in_term cell_subs)
    terms

let clean_up_a
    (cell_subs : (string * Tg_ast.term) list)
    (a : Tg_ast.term list)
  : Tg_ast.term list =
  List.map (Term.replace_cells_in_term cell_subs) a

let clean_up_r
    (cell_subs : (string * Tg_ast.term) list)
    (r : Tg_ast.term list)
  : Tg_ast.term list * (string * Tg_ast.term) list =
  let open Tg_ast in
  let facts, assigns =
    List.fold_left (fun (facts, assigns) term ->
        match term with
        | T_app ([name], _, _, _) ->
          if Loc.content name = "undef" then
            (facts, assigns)
          else
            (term :: facts, assigns)
        | T_cell_assign (cell, x) ->
          (facts, (Loc.content cell, x) :: assigns)
        | _ ->
          (term :: facts, assigns)
      )
      ([], [])
      r
  in
  (List.map (Term.replace_cells_in_term cell_subs) @@ List.rev facts,
   List.map (fun (c, x) -> (c, Term.replace_cells_in_term cell_subs x)) @@ List.rev assigns
  )

let cell_subs_of_rule (spec : Spec.t) g (k : int) =
  if !Params.use_most_general_cell_data_shape then (
    Int_map.find k spec.cell_data_most_general_shape
    |> String_map.to_seq
    |> Seq.map (fun (cell, shape) -> (cell, Cell_data_shape.to_term shape))
    |> List.of_seq
  ) else (
    let ctx_r_preds =
      Graph.pred_seq k g
      |> Seq.fold_left (fun acc k ->
          String_tagged_set.union acc
            (Int_map.find k spec.cells_to_carry_over_before)
        )
        String_tagged_set.empty
    in
    let ctx_ra_preds =
      Graph.pred_seq k g
      |> Seq.fold_left (fun acc k ->
          String_tagged_set.union acc
            (Int_map.find k spec.cells_to_carry_over_after)
        )
        String_tagged_set.empty
    in
    let ctx_r =
      Int_map.find k spec.cells_to_carry_over_before
    in
    let possible_cells =
      String_tagged_set.(union
                           (union ctx_r_preds ctx_ra_preds)
                           ctx_r)
    in
    let matches =
      Int_map.find k spec.user_specified_cell_pat_matches
      |> List.map (fun (c, x) ->
          (Loc.content c, replace_cells_with_placeholder_vars x)
        )
    in
    possible_cells
    |> String_tagged_set.to_seq
    |> Seq.map (fun c ->
        (Loc.content c,
         match List.assoc_opt (Loc.content c) matches with
         | None -> placeholder_var_of_cell (Loc.content c)
         | Some x -> x
        )
      )
    |> List.of_seq
  )
