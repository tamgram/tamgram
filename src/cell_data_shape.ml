let of_term (m : Tg_ast.cell_data_shape String_map.t) (t : Tg_ast.term) : Tg_ast.cell_data_shape =
  let open Tg_ast in
  let rec aux t =
    match t with
    | T_value v -> S_value (Loc.content v)
    | T_symbol (s, `Pub) -> S_pub (Loc.content s)
    | T_symbol (s, `Cell) -> String_map.find (Loc.content s) m
    | T_var (path, name, typ) -> (
        match typ with
        | Some `Fresh ->
          S_fresh (Loc.content @@ List.hd path, name)
        | _ ->
          S_var (Loc.content @@ List.hd path, name)
      )
    | T_tuple (_, l) -> S_tuple (List.map aux l)
    | T_app (path, name, args, _) -> S_app (Loc.content @@ List.hd path, name, List.map aux args)
    | T_unary_op (op, x) -> S_unary_op (op, aux x)
    | T_binary_op (op, x, y) -> S_binary_op (op, aux x, aux y)
    | _ -> failwith "Unexpected case"
  in
  aux t

let is_number (a : Tg_ast.cell_data_shape)  =
  let open Tg_ast in
  let rec aux a =
    match a with
    | S_value (`Str s) ->
      Option.is_some (int_of_string_opt s)
    | S_binary_op (`Plus, x, y) ->
      aux x && aux y
    | _ -> false
  in
  aux a

let compatible (a : Tg_ast.cell_data_shape) (b : Tg_ast.cell_data_shape) =
  let open Tg_ast in
  let rec aux a b =
    (is_number a && is_number b)
    ||
    (match a, b with
     | S_value v1, S_value v2 -> v1 = v2
     | S_pub s1, S_pub s2 -> s1 = s2
     | S_fresh _, S_fresh _ -> true
     | S_var _, _ | _, S_var _ -> true
     | S_tuple l1, S_tuple l2 ->
       List.length l1 = List.length l2
       && List.for_all2 aux l1 l2
     | S_app (_f1, name1, l1), S_app (_f2, name2, l2) ->
       name1 = name2
       && List.for_all2 aux l1 l2
     | S_unary_op (op1, x1), S_unary_op (op2, x2) ->
       op1 = op2 && aux x1 x2
     | S_binary_op (op1, x1, y1), S_binary_op (op2, x2, y2) ->
       op1 = op2 && aux x1 x2 && aux y1 y2
     | _, _ -> false
    )
  in
  aux a b

(* let height (s : Tg_ast.cell_data_shape) =
   let open Tg_ast in
   let rec aux s =
    match s with
    | S_value _ | S_pub _ | S_fresh _ | S_var _ -> 1
    | S_tuple l | S_app (_, _, l) ->
      1 + aux_list l
    | S_unary_op (_, x) ->
      1 + aux x
    | S_binary_op (_, x, y) ->
      1 + (max (aux x) (aux y))
   and aux_list l =
    List.map aux l
    |> List.fold_left Int.max 0
   in
   aux s *)

let a_covers_b ~(a : Tg_ast.cell_data_shape) ~(b : Tg_ast.cell_data_shape) : bool =
  let open Tg_ast in
  let rec aux a b =
    match a, b with
    | S_value v1, S_value v2 -> v1 = v2
    | S_pub s1, S_pub s2 -> s1 = s2
    | S_fresh _, S_fresh _
    | S_var _, _ -> true
    | S_tuple l1, S_tuple l2 ->
      List.length l1 = List.length l2
      && List.for_all2 aux l1 l2
    | S_app (_f1, name1, l1), S_app (_f2, name2, l2) ->
      name1 = name2
      && List.for_all2 aux l1 l2
    | S_unary_op (op1, x1), S_unary_op (op2, x2) ->
      op1 = op2 && aux x1 x2
    | S_binary_op (op1, x1, y1), S_binary_op (op2, x2, y2) ->
      op1 = op2 && aux x1 x2 && aux y1 y2
    | _, _ -> false
  in
  aux a b

let subs_for_a_to_become_b ~(a : Tg_ast.cell_data_shape) ~(b : Tg_ast.cell_data_shape)
  : Tg_ast.cell_data_shape Name_map.t =
  let open Tg_ast in
  let rec aux a b =
    match a, b with
    | S_value _, _
    | S_pub _, _ -> Name_map.empty
    | S_fresh (_s, name), S_fresh _ ->
      Name_map.(add name b empty)
    | S_var (_s, name), x ->
      Name_map.(add name x empty)
    | S_tuple l1, S_tuple l2 ->
      aux_list l1 l2
    | S_app (_, _, l1), S_app (_, _, l2) ->
      aux_list l1 l2
    | S_unary_op (_, x1), S_unary_op (_, x2) ->
      aux x1 x2
    | S_binary_op (_, x1, y1), S_binary_op (_, x2, y2) ->
      aux_list [x1; y1] [x2; y2]
    | _ -> failwith "Unexpected case"
  and aux_list l1 l2 =
    assert (List.length l1 = List.length l2);
    List.fold_left2 (fun m x1 x2 ->
        Name_map.union (fun _ x1 x2 ->
            if x1 = x2 then
              Some x1
            else
              None
          )
          m
          (aux x1 x2)
      )
      Name_map.empty
      l1 l2
  in
  aux a b


(* let sub_cells
    (m : Cell_data_shape_set.t String_map.t)
    (s : Tg_ast.cell_data_shape)
   : Tg_ast.cell_data_shape Seq.t =
   let open Tg_ast in
   let rec aux (s : Tg_ast.cell_data_shape)
    : Tg_ast.cell_data_shape Seq.t =
    match s with
    | S_value _
    | S_pub _
    | S_fresh _
    | S_var _ ->
      Seq.return s
    | S_symbol (c, `Cell) -> (
        match String_map.find_opt c m with
        | None -> failwith "Unexpected case"
        | Some x ->
          Cell_data_shape_set.to_seq x
      )
    | S_tuple l ->
      Seq.map (fun l ->
          S_tuple l
        )
        (aux_list l)
    | S_app (str, name, l) ->
      Seq.map (fun l ->
          S_app (str, name, l)
        )
        (aux_list l)
    | S_unary_op (op, x) ->
      Seq.map (fun x ->
          S_unary_op (op, x)
        )
        (aux x)
    | S_binary_op (op, x, y) ->
      OSeq.product (aux x) (aux y)
      |> Seq.map (fun (x, y) ->
          S_binary_op (op, x, y)
        )
   and aux_list (l : Tg_ast.cell_data_shape list)
    : Tg_ast.cell_data_shape list Seq.t =
    l
    |> List.to_seq
    |> Seq.map aux
    |> OSeq.cartesian_product
   in
   aux s *)

let to_term (s : Tg_ast.cell_data_shape) : Tg_ast.term =
  let open Tg_ast in
  let rec aux s =
    match s with
    | S_value v -> T_value (Loc.untagged v)
    | S_pub str -> T_symbol (Loc.untagged str, `Pub)
    | S_fresh (str, name) -> T_var (Path.of_string str, name, Some `Fresh)
    | S_var (str, name) -> T_var (Path.of_string str, name, None)
    | S_tuple l ->
      T_tuple (None, List.map aux l)
    | S_app (str, name, l) ->
      T_app (Path.of_string str, name, List.map aux l, None)
    | S_unary_op (op, x) ->
      T_unary_op (op, aux x)
    | S_binary_op (op, x, y) ->
      T_binary_op (op, aux x, aux y)
  in
  aux s

let common_part (s1 : Tg_ast.cell_data_shape) (s2 : Tg_ast.cell_data_shape) : Tg_ast.cell_data_shape =
  let open Tg_ast in
  let fresh_fresh () =
    let name_str, name = Lexical_ctx.fresh_local_name () in
    S_fresh (name_str, name)
  in
  let fresh_var () =
    let name_str, name = Lexical_ctx.fresh_local_name () in
    S_var (name_str, name)
  in
  let rec aux s1 s2 =
    match s1, s2 with
    | S_value v1, S_value v2 ->
      if v1 = v2 then
        S_value v1
      else
        fresh_var ()
    | S_pub v1, S_pub v2 ->
      if v1 = v2 then
        S_pub v1
      else
        fresh_var ()
    | S_fresh (v1_str, v1_name), S_fresh (_v2_str, v2_name) ->
      if v1_name = v2_name then
        S_fresh (v1_str, v1_name)
      else
        fresh_fresh ()
    | S_var (v1_str, v1_name), S_var (_v2_str, v2_name) ->
      if v1_name = v2_name then
        S_var (v1_str, v1_name)
      else
        fresh_var ()
    | S_tuple l1, S_tuple l2 ->
      if List.length l1 = List.length l2 then
        S_tuple (List.map2 aux l1 l2)
      else
        fresh_var ()
    | S_app (f1, f_name1, l1), S_app (_f2, f_name2, l2) ->
      if f_name1 = f_name2 then (
        assert (List.length l1 = List.length l2);
        S_app (f1, f_name1, List.map2 aux l1 l2)
      ) else
        fresh_var ()
    | S_unary_op (op1, x1), S_unary_op (op2, x2) ->
      if op1 = op2 then
        S_unary_op (op1, aux x1 x2)
      else
        fresh_var ()
    | S_binary_op (op1, x1, y1), S_binary_op (op2, x2, y2) ->
      if op1 = op2 then
        S_binary_op (op1, aux x1 x2, aux y1 y2)
      else
        fresh_var ()
    | _, _ ->
      fresh_var ()
  in
  aux s1 s2

let sub
    (subs : Tg_ast.cell_data_shape Name_map.t) (shape : Tg_ast.cell_data_shape)
  : Tg_ast.cell_data_shape =
  let open Tg_ast in
  let rec aux shape =
    match shape with
    | S_value _
    | S_pub _ -> shape
    | S_fresh (_, name) | S_var (_, name) -> (
        match Name_map.find_opt name subs with
        | None -> shape
        | Some x -> x
      )
    | S_tuple l -> S_tuple (List.map aux l)
    | S_app (str, name, l) -> S_app (str, name, List.map aux l)
    | S_unary_op (op, x) -> S_unary_op (op, aux x)
    | S_binary_op (op, x, y) -> S_binary_op (op, aux x, aux y)
  in
  aux shape
