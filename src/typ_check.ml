open Result_infix

let compatible_typs_of_typ (a : Typ.term) : Typ.term list =
  a
  ::
  (match a with
   | `Bitstring -> [ `Cell; `Pub; `Fresh; ]
   | `Fact -> [ `Statement ]
   | _ -> [])

let typs_are_compatible (a : Typ.term) (b : Typ.term) : bool =
  List.mem b (compatible_typs_of_typ a)

let typ_ctx_find_exn path name typ_ctx =
  match Typ.Ctx.find name typ_ctx with
  | None ->
    failwith
      (Fmt.str "%a: unexpected error - failed to retrieve type of %a"
         Loc.pp_loc_of_tagged (List.hd path) Printers.pp_path path)
  | Some typ -> typ

let error_msg_for_path ~expected_one_of_typs ~actual_typ (path : Path.t) =
  match expected_one_of_typs with
  | [] -> failwith "Unexpected case"
  | [ x ] ->
    Error_msg.make
      (Loc.tag (List.hd path))
      (Fmt.str
         "@[<v>@[%a has type %a@, but an expression was expected of type@, %a@]@]"
         Printers.pp_path path
         Printers.pp_typ actual_typ Printers.pp_typ x)
  | _ ->
    Error_msg.make
      (Loc.tag (List.hd path))
      (Fmt.str
         "@[<v>@[%a has type %a@, but an expression was expected of one of the types@, @[<h>%a@]@]@]"
         Printers.pp_path
         path Printers.pp_typ actual_typ
         Fmt.(list ~sep:comma Printers.pp_typ)
         expected_one_of_typs)

let error_msg_for_term ~expected_one_of_typs ~actual_typ (term : Tg_ast.term) =
  match expected_one_of_typs with
  | [] -> failwith "Unexpected case"
  | [ x ] ->
    Error_msg.make
      (Term.loc term)
      (Fmt.str "expected type %a for term %a, got %a instead"
         Printers.pp_typ x Printers.pp_term term Printers.pp_typ
         actual_typ
      )
  | _ ->
    Error_msg.make
      (Term.loc term)
      (Fmt.str
         "expected one of the types [@[<h>%a@]] for term %a, got %a instead"
         Fmt.(list ~sep:comma Printers.pp_typ)
         expected_one_of_typs
         Printers.pp_term term
         Printers.pp_typ actual_typ)

let error_msg_for_fun ~actual_typ (path : Path.t) =
  Error_msg.make
    (Loc.tag (List.hd path))
    (Fmt.str "expected a function type for %a, got %a instead"
       Printers.pp_path path Printers.pp_typ
       actual_typ
    )

let rec typ_of_term (typ_ctx : Typ.Ctx.t) (term : Tg_ast.term) :
  (Typ.term, Error_msg.t) result =
  let open Tg_ast in
  let rec aux typ_ctx term =
    match term with
    | T_value x -> (
        match Loc.content x with
        | `Str _ -> Ok `Bitstring
        | `T | `F -> Ok `Formula)
    | T_temporal_a_lt_b { a; b } | T_temporal_eq { a; b } ->
      let+ () =
        check_all_are_one_of
          ~typs:(compatible_typs_of_typ `Temporal)
          typ_ctx
          [ T_var ([ fst a ], snd a, None); T_var ([ fst b ], snd b, None) ]
      in
      `Formula
    | T_symbol (_name, sort) -> (
        match sort with
        | `Cell ->
          Ok `Cell
        | `Pub -> Ok `Pub)
    | T_name_as (x, _) -> aux typ_ctx x
    | T_var (path, name, typ) -> (
        let actual_typ = typ_ctx_find_exn path name typ_ctx in
        (* match actual_typ with
           | `Fresh -> (
            match typ with
            | Some `Fresh -> Ok actual_typ
            | _ ->
              Error
                (Error_msg.make
                   (Loc.tag (List.hd path))
                   (Fmt.str
                      "@[<v>%a is missing %a type annotation@]"
                      Printers.pp_path path
                      Printers.pp_typ actual_typ)
                )
           )
           | _ -> *)
        match typ with
        | None -> Ok actual_typ
        | Some expected_typ ->
          let expected_typs = compatible_typs_of_typ expected_typ in
          if List.mem actual_typ expected_typs then Ok actual_typ
          else
            Error
              (error_msg_for_path ~expected_one_of_typs:expected_typs
                 ~actual_typ path))
    | T_tuple (_, l) ->
      let+ () =
        check_all_are_one_of
          ~typs:(compatible_typs_of_typ `Bitstring)
          typ_ctx l
      in
      `Bitstring
    | T_app (path, name, args, anno) -> (
        match typ_ctx_find_exn path name typ_ctx with
        | `Fun (arg_typs, ret_typ) -> (
            let* () = check_arg_typs path typ_ctx args arg_typs in
            match anno with
            | None -> Ok ret_typ
            | Some _ ->
              match ret_typ with
              | `Fact | `Afact -> Ok ret_typ
              | _ ->
                Error (Error_msg.make
                         (Loc.tag (List.hd path))
                         (Fmt.str "%a: annotation can only be applied to facts"
                            Loc.pp_loc_of_tagged (List.hd path))
                      )
          )
        | typ' -> Error (error_msg_for_fun ~actual_typ:typ' path))
    | T_unary_op (op, x) ->
      let* typ = aux typ_ctx x in
      let expected_typs =
        match op with
        | `Persist -> [`Pfact; `Pafact; ]
        | `Not -> compatible_typs_of_typ `Formula
      in
      if List.mem typ expected_typs then
        Ok (match op with
            | `Persist -> (
                match typ with
                | `Pfact -> `Fact
                | `Pafact -> `Afact
                | _ -> failwith "Unexpected case"
              )
            | `Not -> `Formula)
      else
        Error
          (error_msg_for_term ~expected_one_of_typs:expected_typs
             ~actual_typ:typ x)
    | T_binary_op (op, x, y) ->
      let* typ_x = aux typ_ctx x in
      let* typ_y = aux typ_ctx y in
      let expected_typ_x, expected_typ_y =
        match op with
        | `Exp | `Plus | `Xor | `Eq -> (`Bitstring, `Bitstring)
        | `Iff | `Imp | `Or | `And -> (`Formula, `Formula)
      in
      let expected_typs_x = compatible_typs_of_typ expected_typ_x in
      let expected_typs_y = compatible_typs_of_typ expected_typ_y in
      if List.mem typ_x expected_typs_x then
        if List.mem typ_y expected_typs_y then
          Ok
            (match op with
             | `Exp | `Plus | `Xor -> `Bitstring
             | `Eq -> `Formula
             | `Iff | `Imp | `Or | `And -> `Formula)
        else
          Error
            (error_msg_for_term ~expected_one_of_typs:expected_typs_y
               ~actual_typ:typ_y y)
      else
        Error
          (error_msg_for_term ~expected_one_of_typs:expected_typs_x
             ~actual_typ:typ_x x)
    | T_cell_pat_match (_, y) ->
      let* typ = aux typ_ctx y in
      let expected_typs = compatible_typs_of_typ `Bitstring in
      if List.mem typ expected_typs then Ok `Pat_match
      else
        Error
          (error_msg_for_term ~expected_one_of_typs:expected_typs
             ~actual_typ:typ y)
    | T_cell_assign (_, y) ->
      let* typ = aux typ_ctx y in
      let expected_typs = compatible_typs_of_typ `Bitstring in
      if List.mem typ expected_typs then Ok `Statement
      else
        Error
          (error_msg_for_term ~expected_one_of_typs:expected_typs
             ~actual_typ:typ y)
    | T_let { binding; next; _ } ->
      let* typ = aux typ_ctx (Binding.get binding) in
      let name = Binding.name binding in
      aux (Typ.Ctx.add name typ typ_ctx) next
    | T_let_macro { binding; next; _ } ->
      let* typ_ctx = check_macro typ_ctx binding in
      aux typ_ctx next
    | T_action { fact; temporal } ->
      let* () =
        check_all_are_one_of ~typs:[ `Afact ] typ_ctx [ fact ]
      in
      let* () =
        check_all_are_one_of ~typs:[ `Temporal ] typ_ctx
          [ T_var ([ fst temporal ], snd temporal, None) ]
      in
      Ok `Formula
    | T_quantified { quant; formula; _ } ->
      let typ_ctx =
        List.fold_left
          (fun typ_ctx x ->
             Typ.Ctx.add (Binding.name x) (Binding.get x) typ_ctx)
          typ_ctx quant
      in
      let* () =
        check_all_are_one_of
          ~typs:(compatible_typs_of_typ `Formula)
          typ_ctx [ formula ]
      in
      Ok `Formula
  in
  aux typ_ctx term

and check_arg_typs (path : string Loc.tagged list) (typ_ctx : Typ.Ctx.t)
    (args : Tg_ast.term list) (expected_typs : Typ.term list) :
  (unit, Error_msg.t) result =
  let arg_count = List.length args in
  let expected_arg_count = List.length expected_typs in
  let rec aux typ_ctx (l : (Tg_ast.term * Typ.term) list) =
    match l with
    | [] -> Ok ()
    | (arg, expected_typ) :: rest ->
      let* actual_typ = typ_of_term typ_ctx arg in
      if typs_are_compatible expected_typ actual_typ then aux typ_ctx rest
      else
        Error
          (error_msg_for_term
             ~expected_one_of_typs:(compatible_typs_of_typ expected_typ)
             ~actual_typ arg)
  in
  if arg_count <> expected_arg_count then
    Error
      (Error_msg.make
         (Loc.tag (List.hd path))
         (Fmt.str "expected %d arguments for %a, but got %d instead"
            expected_arg_count Printers.pp_path
            path arg_count)
      )
  else aux typ_ctx (List.combine args expected_typs)

and check_macro (typ_ctx : Typ.Ctx.t) (binding : Tg_ast.macro Binding.t) :
  (Typ.Ctx.t, Error_msg.t) result =
  let open Tg_ast in
  let { arg_and_typs; ret_typ; body } = Binding.get binding in
  let typ_ctx' =
    Typ.Ctx.add_multi
      (List.map (fun x -> (Binding.name x, Binding.get x)) arg_and_typs)
      typ_ctx
  in
  let* typ = typ_of_term typ_ctx' body in
  let name = Binding.name binding in
  if typs_are_compatible ret_typ typ then
    Ok
      (Typ.Ctx.add name
         (`Fun (List.map Binding.get arg_and_typs, ret_typ))
         typ_ctx)
  else
    Error
      (error_msg_for_term
         ~expected_one_of_typs:(compatible_typs_of_typ ret_typ)
         ~actual_typ:typ body)

and check_all_are_one_of ~typs typ_ctx (terms : Tg_ast.term list) :
  (unit, Error_msg.t) result =
  let rec aux typ_ctx terms =
    match terms with
    | [] -> Ok ()
    | x :: xs ->
      let* typ = typ_of_term typ_ctx x in
      if List.mem typ typs then aux typ_ctx xs
      else
        Error
          (error_msg_for_term ~expected_one_of_typs:typs ~actual_typ:typ x)
  in
  aux typ_ctx terms

let typ_of_term_exn (typ_ctx : Typ.Ctx.t) (term : Tg_ast.term) : Typ.term =
  Result.get_ok @@ typ_of_term typ_ctx term

let check_rule_bindings (typ_ctx : Typ.Ctx.t)
    (bindings : Tg_ast.term Binding.t list) : (Typ.Ctx.t, Error_msg.t) result =
  let rec aux typ_ctx bindings =
    match bindings with
    | [] -> Ok typ_ctx
    | x :: xs ->
      let* typ = typ_of_term typ_ctx (Binding.get x) in
      let name = Binding.name x in
      aux (Typ.Ctx.add name typ typ_ctx) xs
  in
  aux typ_ctx bindings

let check_rule_bindings (typ_ctx : Typ.Ctx.t)
    (bindings : Tg_ast.rule_binding list) : (Typ.Ctx.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux typ_ctx bindings =
    match bindings with
    | [] -> Ok typ_ctx
    | x :: xs -> (
        match x with
        | R_let x ->
          let* typ = typ_of_term typ_ctx (Binding.get x) in
          let name = Binding.name x in
          aux (Typ.Ctx.add name typ typ_ctx) xs
        | R_let_macro { binding; _ } ->
          let* typ_ctx = check_macro typ_ctx binding in
          aux typ_ctx xs)
  in
  aux typ_ctx bindings

let check_rule (typ_ctx : Typ.Ctx.t) (rule : Tg_ast.rule) :
  (unit, Error_msg.t) result =
  let open Tg_ast in
  let { l; vars_in_l; bindings_before_a; a; bindings_before_r; r } = rule in
  let l = Term.fill_in_default_typ_for_terms ~default:`Bitstring l in
  let typ_ctx =
    List.fold_left
      (fun typ_ctx x -> Typ.Ctx.add (Binding.name x) (Binding.get x) typ_ctx)
      typ_ctx vars_in_l
  in
  let* () = check_all_are_one_of ~typs:[ `Fact; `Pat_match ] typ_ctx l in
  let* typ_ctx = check_rule_bindings typ_ctx bindings_before_a in
  let* () = check_all_are_one_of ~typs:[ `Afact ] typ_ctx a in
  let* typ_ctx = check_rule_bindings typ_ctx bindings_before_r in
  let+ () = check_all_are_one_of ~typs:[ `Fact; `Statement ] typ_ctx r in
  ()

let check_proc (typ_ctx : Typ.Ctx.t) (proc : Tg_ast.proc) :
  (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux typ_ctx proc =
    match proc with
    | P_null | P_break _ | P_continue _ -> Ok ()
    | P_let { binding; next; _ } ->
      let* typ = typ_of_term typ_ctx (Binding.get binding) in
      let name = Binding.name binding in
      aux (Typ.Ctx.add name typ typ_ctx) next
    | P_let_macro { binding; next; _ } ->
      let* typ_ctx = check_macro typ_ctx binding in
      aux typ_ctx next
    | P_app (path, name, args, next) ->
      let* () =
        match typ_ctx_find_exn path name typ_ctx with
        | `Fun (arg_typs, ret_typ) -> (
            let* () = check_arg_typs path typ_ctx args arg_typs in
            match ret_typ with
            | `Process -> Ok ()
            | typ' ->
              Error (error_msg_for_term ~expected_one_of_typs:[`Process] ~actual_typ:typ'
                       (T_app (path, name, args, None))
                    )
          )
        | typ' -> Error (error_msg_for_fun ~actual_typ:typ' path)
      in
      aux typ_ctx next
    | P_line { tag = _; rule; next } ->
      let* () = check_rule typ_ctx rule in
      aux typ_ctx next
    | P_branch (_loc, procs, next) ->
      let* () = aux_list typ_ctx procs in
      aux typ_ctx next
    | P_scoped (proc, next) ->
      let* () = aux typ_ctx proc in
      aux typ_ctx next
    | P_while_cell_cas { mode = _; cell = _; term; proc; next } -> (
        let* typ = typ_of_term typ_ctx term in
        let expected_typs = compatible_typs_of_typ `Bitstring in
        if List.mem typ expected_typs then
          let* () = aux typ_ctx proc in
          aux typ_ctx next
        else (
          Error (error_msg_for_term ~expected_one_of_typs:expected_typs ~actual_typ:typ
                   term
                )
        )
      )
  and aux_list typ_ctx procs =
    match procs with
    | [] -> Ok ()
    | x :: xs ->
      let* () = aux typ_ctx x in
      aux_list typ_ctx xs
  in
  aux typ_ctx proc

let check_proc_macro (typ_ctx : Typ.Ctx.t) (binding : Tg_ast.proc_macro Binding.t) :
  (Typ.Ctx.t, Error_msg.t) result =
  let open Tg_ast in
  let { arg_and_typs; body } : proc_macro = Binding.get binding in
  let typ_ctx' =
    Typ.Ctx.add_multi
      (List.map (fun x -> (Binding.name x, Binding.get x)) arg_and_typs)
      typ_ctx
  in
  let+ () = check_proc typ_ctx' body in
  let name = Binding.name binding in
  Typ.Ctx.add name
    (`Fun (List.map Binding.get arg_and_typs, `Process))
    typ_ctx

let check_modul (typ_ctx : Typ.Ctx.t) (decls : Tg_ast.modul) :
  (Typ.Ctx.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux typ_ctx decls =
    match decls with
    | [] -> Ok typ_ctx
    | d :: ds -> (
        match d with
        | D_open _ | D_insert _ -> aux typ_ctx ds
        | D_process { binding; _ } ->
          let* () = check_proc typ_ctx (Binding.get binding) in
          aux (Typ.Ctx.add (Binding.name binding) `Process typ_ctx) ds
        | D_process_macro binding ->
          let* typ_ctx = check_proc_macro typ_ctx binding in
          aux typ_ctx ds
        | D_let { binding; _ } ->
          let* typ = typ_of_term typ_ctx (Binding.get binding) in
          aux (Typ.Ctx.add (Binding.name binding) typ typ_ctx) ds
        | D_fun binding ->
          let arg_typs =
            CCSeq.(0 --^ Binding.get binding)
            |> CCSeq.map (fun _ -> `Bitstring)
            |> CCSeq.to_list
          in
          aux
            (Typ.Ctx.add (Binding.name binding)
               (`Fun (arg_typs, `Bitstring))
               typ_ctx)
            ds
        | D_pred binding -> (
            let { arity; options = _ } = Binding.get binding in
            let arg_typs =
              match Loc.content (Binding.name_str binding) with
              | "Fr" ->
                assert (arity = 1);
                [ `Fresh ]
              | _ ->
                CCList.(0 --^ arity) |> CCList.map (fun _ -> `Bitstring)
            in
            aux
              (Typ.Ctx.add (Binding.name binding)
                 (`Fun (arg_typs, `Fact))
                 typ_ctx)
              ds
          )
        | D_ppred binding -> (
            let { arity; options = _ } = Binding.get binding in
            let arg_typs =
              match Loc.content (Binding.name_str binding) with
              | "Fr" ->
                assert (arity = 1);
                [ `Fresh ]
              | _ ->
                CCList.(0 --^ arity) |> CCList.map (fun _ -> `Bitstring)
            in
            aux
              (Typ.Ctx.add (Binding.name binding)
                 (`Fun (arg_typs, `Pfact))
                 typ_ctx)
              ds
          )
        | D_apred binding ->
          let arg_typs =
            CCSeq.(0 --^ Binding.get binding)
            |> CCSeq.map (fun _ -> `Bitstring)
            |> CCSeq.to_list
          in
          aux
            (Typ.Ctx.add (Binding.name binding)
               (`Fun (arg_typs, `Afact))
               typ_ctx)
            ds
        | D_papred binding ->
          let arg_typs =
            CCSeq.(0 --^ Binding.get binding)
            |> CCSeq.map (fun _ -> `Bitstring)
            |> CCSeq.to_list
          in
          aux
            (Typ.Ctx.add (Binding.name binding)
               (`Fun (arg_typs, `Pafact))
               typ_ctx)
            ds
        | D_macro { binding; _ } ->
          let* typ_ctx = check_macro typ_ctx binding in
          aux typ_ctx ds
        | D_lemma { binding; _ } ->
          let* () =
            check_all_are_one_of ~typs:[ `Formula ] typ_ctx
              [ (Binding.get binding).formula ]
          in
          aux (Typ.Ctx.add (Binding.name binding) `Lemma typ_ctx) ds
        | D_restriction { binding; _ } ->
          let* () =
            check_all_are_one_of ~typs:[ `Formula ] typ_ctx
              [ Binding.get binding ]
          in
          aux (Typ.Ctx.add (Binding.name binding) `Restriction typ_ctx) ds
        | D_equation { binding; _ } ->
          let* () =
            check_all_are_one_of ~typs:[ `Formula ] typ_ctx
              [ Binding.get binding ]
          in
          aux (Typ.Ctx.add (Binding.name binding) `Equation typ_ctx) ds
        | D_rule { binding; _ } ->
          let* () = check_rule typ_ctx (Binding.get binding) in
          aux (Typ.Ctx.add (Binding.name binding) `Rule typ_ctx) ds
        | D_modul (_, decls) ->
          let* typ_ctx = aux typ_ctx decls in
          aux typ_ctx ds
        | D_builtins _ -> failwith "Unexpected case"
      )
  in
  aux typ_ctx decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let+ root_typ_ctx = check_modul Typ.Ctx.empty spec.root in
  { spec with root_typ_ctx }
