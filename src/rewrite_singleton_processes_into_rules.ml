let warnings : Error_msg.t list ref = ref []

let aux_rule (ru : Tg_ast.rule) : Tg_ast.rule =
  let open Tg_ast in
  let r =
    List.filter (fun x ->
        match x with
        | T_cell_assign _ -> false
        | _ -> true
      )
      ru.r
  in
  { ru with r }

let aux_modul (decls : Tg_ast.modul) : Tg_ast.modul =
  let open Tg_ast in
  let rec aux acc decls =
    match decls with
    | [] -> List.rev acc
    | d :: ds ->
      let d =
        match d with
        | D_process { binding } -> (
            match Binding.get binding with
            | P_line { tag; rule; next = P_null } -> (
                (match tag with
                 | None -> ()
                 | Some s ->
                   warnings :=
                     Error_msg.make ~typ:`Warning (Loc.tag s)
                       (Printf.sprintf "Rule tag %s for singleton process is ignored" (Loc.content s))
                     :: !warnings
                );
                D_rule { binding = Binding.update (aux_rule rule) binding }
              )
            | _ -> d
          )
        | D_fun _ | D_pred _ | D_ppred _
        | D_apred _ | D_papred _ | D_equation _ | D_lemma _
        | D_restriction _ | D_rule _ | D_open _ | D_insert _ ->
          d
        | D_process_macro _
        | D_let _ | D_macro _ -> failwith "Unexpected case"
        | D_modul (name, m) -> D_modul (name, aux [] m)
        | D_builtins _ -> failwith "Unexpected case"
      in
      aux (d :: acc) ds
  in
  aux [] decls

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  warnings := [];
  Ok { spec with root = aux_modul spec.root; warnings = !warnings }
