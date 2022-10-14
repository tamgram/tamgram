open Result_infix

let check_name name (seen : String_tagged_set.t) :
  (String_tagged_set.t, Error_msg.t) result =
  match String_tagged_set.find_opt name seen with
  | None -> Ok (String_tagged_set.add name seen)
  | Some x ->
    Error
      (Error_msg.make
         (Loc.tag name)
         (Fmt.str
            "Uninterpreted symbol %s already defined at %a in the same module"
            (Loc.content name) Loc.pp_loc_of_tagged_uncapitalized x)
      )

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux (seen : String_tagged_set.t) decls =
    match decls with
    | [] -> Ok seen
    | d :: ds -> (
        match d with
        | D_process _ | D_process_macro _
        | D_let _ | D_macro _ | D_equation _
        | D_lemma _ | D_restriction _ | D_rule _ | D_open _ | D_insert _ ->
          aux seen ds
        | D_pred binding | D_ppred binding ->
          let* seen = check_name (Binding.name_str binding) seen in
          aux seen ds
        | D_fun binding | D_apred binding | D_papred binding ->
          let* seen = check_name (Binding.name_str binding) seen in
          aux seen ds
        | D_modul (_, l) ->
          let* seen = aux String_tagged_set.empty l in
          aux seen ds
        | D_builtins _ -> failwith "Unexpected case"
      )
  in
  let+ _ = aux String_tagged_set.empty spec.root in
  spec
