open Result_syntax

let aux_proc (proc : Tg_ast.proc) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux usable_entry_points proc =
    match proc with
    | P_null -> Ok usable_entry_points
    | P_goto { dest; _ } ->
      if String_tagged_set.mem dest usable_entry_points then
        Ok usable_entry_points
      else
        Error
          (Error_msg.make
             (Loc.tag dest)
             (Fmt.str "entry point \"%s\" may not be well defined here"
                (Loc.content dest))
          )
    | P_entry_point { name; next; _ } ->
      if String_tagged_set.mem name usable_entry_points then
        Error
          (Error_msg.make
             (Loc.tag name)
             (Fmt.str "entry point \"%s\" already defined"
                (Loc.content name))
          )
      else aux (String_tagged_set.add name usable_entry_points) next
    | P_let { next; _ }
    | P_let_macro { next; _ }
    | P_app (_, _, _, next) ->
      aux usable_entry_points next
    | P_line { next; _ } ->
      aux usable_entry_points next
    | P_scoped (x, next) ->
      let* usable_entry_points = aux usable_entry_points x in
      aux usable_entry_points next
    | P_branch (_loc, procs, next) ->
      let* usable_entry_points' =
        CCList.fold_left
          (fun acc x ->
             let* acc = acc in
             let+ acc' = aux usable_entry_points x in
             String_tagged_set.union acc acc')
          (Ok String_tagged_set.empty) procs
      in
      let usable_entry_points =
        String_tagged_set.union usable_entry_points' usable_entry_points
      in
      aux usable_entry_points next
  in
  let+ _ = aux String_tagged_set.empty proc in
  ()

let aux_modul (decls : Tg_ast.modul) : (unit, Error_msg.t) result =
  let open Tg_ast in
  let rec aux decls =
    match decls with
    | [] -> Ok ()
    | d :: ds ->
      let* () =
        match d with
        | D_process { binding; _ } -> aux_proc (Binding.get binding)
        | D_process_macro binding -> aux_proc (Binding.get binding).body
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_equation _ | D_lemma _
        | D_restriction _ | D_rule _ | D_open _ | D_insert _ | D_let _
        | D_macro _ ->
          Ok ()
        | D_modul (_, m) -> aux m
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux ds
  in
  aux decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let+ () = aux_modul spec.root in
  spec
