let replace_free_vars_via_name_strs_in_term (subs : (string * Tg_ast.term) list)
    (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux bound term =
    match term with
    | T_value _ | T_symbol _ -> term
    | T_name_as (x, name) -> T_name_as (aux bound x, name)
    | T_var (path, _, _) -> (
        match path with
        | [] -> failwith "Unexpected case"
        | [ x ] -> (
            if String_tagged_set.mem x bound then term
            else
              match List.assoc_opt (Loc.content x) subs with
              | None -> term
              | Some x -> x)
        | _ -> term)
    | T_tuple (loc, l) -> T_tuple (loc, aux_list bound l)
    | T_app { path; name; named_args; args; anno } ->
      let named_args =
        List.map (fun (s, arg) ->
          (s, aux bound arg)
          )
        named_args
      in
      let args = aux_list bound args in
      T_app { path; name; named_args; args; anno }
    | T_unary_op (op, x) -> T_unary_op (op, aux bound x)
    | T_binary_op (op, x, y) -> T_binary_op (op, aux bound x, aux bound y)
    | T_cell_pat_match (x, y) -> T_cell_pat_match (x, aux bound y)
    | T_cell_assign (x, y) -> T_cell_assign (x, aux bound y)
    | T_let { binding; next } ->
      let bound_to = aux bound (Binding.get binding) in
      let bound = String_tagged_set.add (Binding.name_str binding) bound in
      let next = aux bound next in
      T_let { binding = Binding.update bound_to binding; next }
    | T_let_macro { binding; next } ->
        let { named_arg_and_typs; arg_and_typs; ret_typ; body } = Binding.get binding in
      let bound' =
        List.fold_left
          (fun acc x -> String_tagged_set.add (Binding.name_str x) acc)
          bound arg_and_typs
      in
      let body = aux bound' body in
      let next = aux bound next in
      T_let_macro
        {
          binding = Binding.update { arg_and_typs; ret_typ; body } binding;
          next;
        }
    | T_action { fact; temporal } ->
      let fact = aux bound fact in
      T_action { fact; temporal }
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> term
    | T_quantified { loc; quantifier; quant; formula } ->
      let bound =
        List.fold_left
          (fun acc x -> String_tagged_set.add (Binding.name_str x) acc)
          bound quant
      in
      let formula = aux bound formula in
      T_quantified { loc; quantifier; quant; formula }
  and aux_list bound terms = List.map (aux bound) terms in
  aux String_tagged_set.empty term

let replace_free_vars_via_name_strs_in_terms subs (terms : Tg_ast.term list) :
  Tg_ast.term list =
  List.map (replace_free_vars_via_name_strs_in_term subs) terms

let free_var_name_strs_in_term ?(ignore_name_as = false) (term : Tg_ast.term) :
  String_tagged_set.t =
  let open Tg_ast in
  let rec aux bound term =
    match term with
    | T_value _ | T_symbol _ -> String_tagged_set.empty
    | T_name_as (x, y) ->
      let inner = aux bound x in
      if ignore_name_as then inner else String_tagged_set.add y inner
    | T_var (path, _, _) -> (
        match path with
        | [] -> failwith "Unexpected case"
        | [ x ] ->
          if String_tagged_set.mem x bound then String_tagged_set.empty
          else String_tagged_set.(add x empty)
        | _ -> String_tagged_set.empty)
    | T_tuple (_, l) -> aux_list bound l
    | T_app (_, _, args, _) -> aux_list bound args
    | T_unary_op (_, x) -> aux bound x
    | T_binary_op (_, x, y) ->
      let s1 = aux bound x in
      let s2 = aux bound y in
      String_tagged_set.union s1 s2
    | T_cell_pat_match (_, x) -> aux bound x
    | T_cell_assign (_, x) -> aux bound x
    | T_let { binding; next; _ } ->
      let s1 = aux bound (Binding.get binding) in
      let bound = String_tagged_set.add (Binding.name_str binding) bound in
      let s2 = aux bound next in
      String_tagged_set.union s1 s2
    | T_let_macro { binding; next; _ } ->
      let ({ body; _ } : Tg_ast.macro) = Binding.get binding in
      let s1 = aux bound body in
      let bound = String_tagged_set.add (Binding.name_str binding) bound in
      let s2 = aux bound next in
      String_tagged_set.union s1 s2
    | T_action { fact; _ } -> aux bound fact
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> String_tagged_set.empty
    | T_quantified { formula; _ } -> aux bound formula
  and aux_list bound terms =
    CCList.fold_left
      (fun acc x -> String_tagged_set.union (aux bound x) acc)
      String_tagged_set.empty terms
  in
  aux String_tagged_set.empty term

let free_var_name_strs_in_terms ?ignore_name_as (terms : Tg_ast.term list) :
  String_tagged_set.t =
  CCList.fold_left
    (fun acc x ->
       String_tagged_set.union (free_var_name_strs_in_term ?ignore_name_as x) acc)
    String_tagged_set.empty terms

let free_var_name_str_and_typs_in_term (term : Tg_ast.term) :
  Typ.term Loc.tagged String_map.t =
  let open Tg_ast in
  let union = String_map.union (fun _ x _ -> Some x) in
  let rec aux bound term =
    match term with
    | T_value _ | T_symbol _ -> String_map.empty
    | T_name_as (x, _) -> aux bound x
    | T_var (path, _, typ) -> (
        match path with
        | [] -> failwith "Unexpected case"
        | [ x ] ->
          if String_tagged_set.mem x bound then String_map.empty
          else
            String_map.add (Loc.content x)
              (Loc.update_content (Option.value ~default:`Bitstring typ) x)
              String_map.empty
        | _ -> String_map.empty)
    | T_tuple (_, l) -> aux_list bound l
    | T_app (_, _, args, _) -> aux_list bound args
    | T_unary_op (_, x) -> aux bound x
    | T_binary_op (_, x, y) ->
      let s1 = aux bound x in
      let s2 = aux bound y in
      union s1 s2
    | T_cell_pat_match (_, y) -> aux bound y
    | T_cell_assign (_, y) -> aux bound y
    | T_let { binding; next; _ } ->
      let s1 = aux bound (Binding.get binding) in
      let bound = String_tagged_set.add (Binding.name_str binding) bound in
      let s2 = aux bound next in
      union s1 s2
    | T_let_macro { binding; next; _ } ->
      let ({ body; _ } : Tg_ast.macro) = Binding.get binding in
      let s1 = aux bound body in
      let bound = String_tagged_set.add (Binding.name_str binding) bound in
      let s2 = aux bound next in
      union s1 s2
    | T_action { fact; _ } -> aux bound fact
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> String_map.empty
    | T_quantified { formula; _ } -> aux bound formula
  and aux_list bound terms =
    CCList.fold_left
      (fun acc x -> union acc (aux bound x))
      String_map.empty terms
  in
  aux String_tagged_set.empty term

let free_var_name_str_and_typs_in_terms (terms : Tg_ast.term list) :
  Typ.term Loc.tagged String_map.t =
  CCList.fold_left
    (fun acc x ->
       String_map.union
         (fun _ x _ -> Some x)
         acc
         (free_var_name_str_and_typs_in_term x))
    String_map.empty terms

let free_var_names_in_term (term : Tg_ast.term) : string Loc.tagged Name_map.t =
  let union = Name_map.union (fun _ x _ -> Some x) in
  let rec aux bound term =
    let open Tg_ast in
    match term with
    | T_value _ | T_symbol _ -> Name_map.empty
    | T_name_as (x, _) -> aux bound x
    | T_var (path, name, _typ) -> (
        match path with
        | [] -> failwith "Unexpected case"
        | [ x ] ->
          if Name_set.mem name bound then Name_map.empty
          else
            Name_map.add name x Name_map.empty
        | _ -> Name_map.empty)
    | T_tuple (_, l) -> aux_list bound l
    | T_app (_, _, args, _) -> aux_list bound args
    | T_unary_op (_, x) -> aux bound x
    | T_binary_op (_, x, y) ->
      let s1 = aux bound x in
      let s2 = aux bound y in
      union s1 s2
    | T_cell_pat_match (_, y) -> aux bound y
    | T_cell_assign (_, y) -> aux bound y
    | T_let { binding; next; _ } ->
      let s1 = aux bound (Binding.get binding) in
      let bound = Name_set.add (Binding.name binding) bound in
      let s2 = aux bound next in
      union s1 s2
    | T_let_macro { binding; next; _ } ->
      let ({ body; _ } : Tg_ast.macro) = Binding.get binding in
      let s1 = aux bound body in
      let bound = Name_set.add (Binding.name binding) bound in
      let s2 = aux bound next in
      union s1 s2
    | T_action { fact; _ } -> aux bound fact
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> Name_map.empty
    | T_quantified { formula; _ } -> aux bound formula
  and aux_list bound terms =
    CCList.fold_left
      (fun acc x -> union acc (aux bound x))
      Name_map.empty terms
  in
  aux Name_set.empty term

let rec change_cell_names_in_term (subs : (string * string Loc.tagged) list)
    (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ -> term
    | T_symbol (name, sort) -> (
        match sort with
        | `Cell -> (
            match List.assoc_opt (Loc.content name) subs with
            | None -> term
            | Some x -> T_symbol (x, sort))
        | _ -> term)
    | T_name_as (x, name) -> T_name_as (aux x, name)
    | T_var _ -> term
    | T_tuple (loc, l) -> T_tuple (loc, change_cell_names_in_terms subs l)
    | T_app (path, name, args, anno) ->
      let args = change_cell_names_in_terms subs args in
      T_app (path, name, args, anno)
    | T_unary_op (op, x) -> T_unary_op (op, aux x)
    | T_binary_op (op, x, y) -> T_binary_op (op, aux x, aux y)
    | T_cell_pat_match (x, y) -> (
        let x = 
          match List.assoc_opt (Loc.content x) subs with
          | None -> x
          | Some x' -> x'
        in
        T_cell_pat_match (x, aux y)
      )
    | T_cell_assign (x, y) ->
      let x = 
        match List.assoc_opt (Loc.content x) subs with
        | None -> x
        | Some x' -> x'
      in
      T_cell_assign (x, aux y)
    | T_let { binding; next } ->
      let bound_to = aux (Binding.get binding) in
      let next = aux next in
      T_let { binding = Binding.update bound_to binding; next }
    | T_let_macro { binding; next } ->
      let { arg_and_typs; ret_typ; body } = Binding.get binding in
      let body = aux body in
      let next = aux next in
      T_let_macro
        {
          binding = Binding.update { arg_and_typs; ret_typ; body } binding;
          next;
        }
    | T_action { fact; temporal } -> T_action { fact = aux fact; temporal }
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> term
    | T_quantified { loc; quantifier; quant; formula } ->
      T_quantified { loc; quantifier; quant; formula = aux formula }
  in
  aux term

and change_cell_names_in_terms subs (terms : Tg_ast.term list) : Tg_ast.term list =
  List.map (change_cell_names_in_term subs) terms

let rec replace_cells_in_term (subs : (string * Tg_ast.term) list)
    (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ -> term
    | T_symbol (name, sort) -> (
        match sort with
        | `Cell -> (
            match List.assoc_opt (Loc.content name) subs with
            | None -> term
            | Some x -> x)
        | _ -> term)
    | T_name_as (x, name) -> T_name_as (aux x, name)
    | T_var _ -> term
    | T_tuple (loc, l) -> T_tuple (loc, replace_cells_in_terms subs l)
    | T_app (path, name, args, anno) ->
      let args = replace_cells_in_terms subs args in
      T_app (path, name, args, anno)
    | T_unary_op (op, x) -> T_unary_op (op, aux x)
    | T_binary_op (op, x, y) -> T_binary_op (op, aux x, aux y)
    | T_cell_pat_match (x, y) -> T_cell_pat_match (x, aux y)
    | T_cell_assign (x, y) -> T_cell_assign (x, aux y)
    | T_let { binding; next } ->
      let bound_to = aux (Binding.get binding) in
      let next = aux next in
      T_let { binding = Binding.update bound_to binding; next }
    | T_let_macro { binding; next } ->
      let { arg_and_typs; ret_typ; body } = Binding.get binding in
      let body = aux body in
      let next = aux next in
      T_let_macro
        {
          binding = Binding.update { arg_and_typs; ret_typ; body } binding;
          next;
        }
    | T_action { fact; temporal } -> T_action { fact = aux fact; temporal }
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> term
    | T_quantified { loc; quantifier; quant; formula } ->
      T_quantified { loc; quantifier; quant; formula = aux formula }
  in
  aux term

and replace_cells_in_terms subs (terms : Tg_ast.term list) : Tg_ast.term list =
  List.map (replace_cells_in_term subs) terms

let union_cell_rw m1 m2 =
  String_tagged_map.union (fun _ x y ->
      match x, y with
      | `R, `Rw | `Rw, `R -> Some `Rw
      | _ -> Some `R
    )
    m1 m2

let rec cells_in_term (term : Tg_ast.term) : Tg_ast.rw String_tagged_map.t =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ -> String_tagged_map.empty
    | T_symbol (name, sort) -> (
        match sort with
        | `Cell -> String_tagged_map.(add name `R empty)
        | _ -> String_tagged_map.empty)
    | T_name_as (x, _) -> aux x
    | T_var _ -> String_tagged_map.empty
    | T_tuple (_, l) -> cells_in_terms l
    | T_app (_, _, args, _) -> cells_in_terms args
    | T_unary_op (_, x) -> aux x
    | T_binary_op (_, x, y) -> union_cell_rw (aux x) (aux y)
    | T_cell_pat_match (x, y) -> String_tagged_map.add x `R (aux y)
    | T_cell_assign (x, y) -> String_tagged_map.add x `Rw (aux y)
    | T_let { binding; next; _ } ->
      union_cell_rw (aux (Binding.get binding)) (aux next)
    | T_let_macro { binding; next; _ } ->
      let ({ body; _ } : Tg_ast.macro) = Binding.get binding in
      union_cell_rw (aux body) (aux next)
    | T_action { fact; _ } -> aux fact
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> String_tagged_map.empty
    | T_quantified { formula; _ } -> aux formula
  in
  aux term

and cells_in_terms (terms : Tg_ast.term list) : Tg_ast.rw String_tagged_map.t =
  List.fold_left
    (fun acc x -> union_cell_rw acc (cells_in_term x))
    String_tagged_map.empty terms

let rec fill_in_default_typ_for_term ~default (term : Tg_ast.term) : Tg_ast.term
  =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ | T_symbol _ | T_temporal_a_lt_b _ | T_temporal_eq _
    | T_cell_assign _ ->
      term
    | T_cell_pat_match (cell, x) -> T_cell_pat_match (cell, aux x)
    | T_name_as (x, name) -> T_name_as (aux x, name)
    | T_var (path, name, typ) ->
      T_var (path, name, Some (Option.value ~default typ))
    | T_tuple (loc, l) -> T_tuple (loc, fill_in_default_typ_for_terms ~default l)
    | T_app (path, name, args, anno) ->
      T_app (path, name, fill_in_default_typ_for_terms ~default args, anno)
    | T_unary_op (op, x) -> T_unary_op (op, aux x)
    | T_binary_op (op, x, y) -> T_binary_op (op, aux x, aux y)
    | T_let { binding; next } ->
      T_let { binding = Binding.map aux binding; next = aux next }
    | T_let_macro { binding; next } ->
      let binding =
        Binding.map
          (fun (x : Tg_ast.macro) -> { x with body = aux x.body })
          binding
      in
      T_let_macro { binding; next = aux next }
    | T_action { fact; temporal } -> T_action { fact = aux fact; temporal }
    | T_quantified { loc; quantifier; quant; formula } ->
      T_quantified { loc; quantifier; quant; formula = aux formula }
  in
  aux term

and fill_in_default_typ_for_terms ~default terms =
  List.map (fill_in_default_typ_for_term ~default) terms

let loc (term : Tg_ast.term) : Loc.t option =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value x -> Loc.tag x
    | T_symbol (name, _) -> Loc.tag name
    | T_var ([], _, _) -> failwith "Unexpected case"
    | T_var (x :: _, _, _) -> Loc.tag x
    | T_tuple (loc, _) -> loc
    | T_app ([], _, _, _) -> failwith "Unexpected case"
    | T_app (x :: _, _, _, _) -> Loc.tag x
    | T_unary_op (_, x) -> aux x
    | T_binary_op (_, x, _) -> aux x
    | T_cell_pat_match (x, _) -> Loc.tag x
    | T_cell_assign (x, _) -> Loc.tag x
    | T_name_as (x, _) -> aux x
    | T_let { binding; _ } -> Binding.loc binding
    | T_let_macro { binding; _ } -> Binding.loc binding
    | T_action { fact; _ } -> aux fact
    | T_temporal_a_lt_b { a = (name_str, _name); _ } ->
      Loc.tag name_str
    | T_temporal_eq { a = (name_str, _name); _ } ->
      Loc.tag name_str
    | T_quantified { loc; _ } ->
      loc
  in
  aux term

let update_loc_of_term (loc : Loc.t option) (term : Tg_ast.term) : Tg_ast.term =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value x -> T_value (Loc.update_tag loc x)
    | T_symbol (name, sort) -> T_symbol (Loc.update_tag loc name, sort)
    | T_name_as (x, name) -> T_name_as (aux x, name)
    | T_var (path, name, typ) -> T_var (Loc.update_tag_multi loc path, name, typ)
    | T_tuple (_, l) -> T_tuple (loc, List.map aux l)
    | T_app (path, name, l, anno) -> T_app (Loc.update_tag_multi loc path, name, l, anno)
    | T_unary_op (op, x) -> T_unary_op (op, aux x)
    | T_binary_op (op, x, y) -> T_binary_op (op, aux x, aux y)
    | T_cell_pat_match (x, y) -> T_cell_pat_match (Loc.update_tag loc x, aux y)
    | T_cell_assign (x, y) -> T_cell_assign (Loc.update_tag loc x, aux y)
    | T_let { binding; next } ->
      T_let
        { binding = Binding.update_loc loc binding; next = aux next }
    | T_let_macro { binding; next } ->
      T_let_macro
        { binding = Binding.update_loc loc binding; next = aux next }
    | T_action { fact; temporal } -> T_action { fact = aux fact; temporal }
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> term
    | T_quantified { loc; quantifier; quant; formula } ->
      T_quantified { loc; quantifier; quant; formula = aux formula }
  in
  aux term

let sub
    ~loc
    (subs : (Name.t * Tg_ast.term) list) (term : Tg_ast.term) :
  Tg_ast.term =
  let open Tg_ast in
  let rec aux term =
    match term with
    | T_value _ | T_symbol _ -> term
    | T_name_as (x, y) -> T_name_as (aux x, y)
    | T_var (_path, name, _typ) -> (
        match List.assoc_opt name subs with
        | None -> term
        | Some term -> update_loc_of_term loc term)
    | T_tuple (loc, l) -> T_tuple (loc, List.map aux l)
    | T_app (path, name, l, anno) -> T_app (path, name, List.map aux l, anno)
    | T_unary_op (op, x) -> T_unary_op (op, aux x)
    | T_binary_op (op, x, y) -> T_binary_op (op, aux x, aux y)
    | T_cell_pat_match (x, y) -> T_cell_pat_match (x, aux y)
    | T_cell_assign (x, y) -> T_cell_assign (x, aux y)
    | T_let { binding; next } ->
      T_let { binding = Binding.map aux binding; next = aux next }
    | T_let_macro { binding; next } ->
      T_let_macro
        {
          binding =
            Binding.map
              (fun { arg_and_typs; ret_typ; body } ->
                 { arg_and_typs; ret_typ; body = aux body })
              binding;
          next = aux next;
        }
    | T_action { fact; temporal } -> T_action { fact = aux fact; temporal }
    | T_temporal_a_lt_b _ | T_temporal_eq _ -> term
    | T_quantified { loc; quantifier; quant; formula } ->
      T_quantified { loc; quantifier; quant; formula = aux formula }
  in
  aux term
