open Result_infix

let base =
  let open Tg_ast in
  (match !Params.translate_style with
   | `Frame | `Frame_minimal0 | `Frame_minimal1
   | `Frame_minimal_reversed_linking0 ->
     [ D_pred (Binding.make_untagged "St" { arity = 3; options = [] }) ]
   | `Cell_by_cell | `Persistent0 ->
     [ D_pred (Binding.make_untagged "St" { arity = 2; options = [] }) ]
   | `Mix0 ->
     [ D_pred (Binding.make_untagged "St" { arity = 3; options = [] })
     ; D_pred (Binding.make_untagged "StF" { arity = 3; options = [] })
     ; D_pred (Binding.make_untagged "StB" { arity = 3; options = [] })
     ]
  )
  @
  [
    D_pred
      (Binding.make_untagged "Fr" { arity = 1; options = [] });
    D_pred
      (Binding.make_untagged "In" { arity = 1; options = [] });
    D_pred
      (Binding.make_untagged "Out" { arity = 1; options = [] });
    D_papred
      (Binding.make_untagged "KU" 1);
    D_apred
      (Binding.make_untagged "K" 1);
    D_pred
      (Binding.make_untagged "undef" { arity = 1; options = [] });
    D_pred
      (Binding.make_untagged "Cell" { arity = 3; options = [] });
    D_ppred
      (Binding.make_untagged "Pcell" { arity = 4; options = [] });
    D_apred
      (Binding.make_untagged Params.pcell_read_apred_name 3);
    D_apred
      (Binding.make_untagged Params.pcell_freed_apred_name 4);
    D_fun (Binding.make_untagged "pair" 2);
    D_fun (Binding.make_untagged "fst" 1);
    D_fun (Binding.make_untagged "snd" 1);
  ]

let parse_builtins (l : string Loc.tagged list) : (Builtin.t Loc.tagged list, Error_msg.t) result =
  let rec aux acc l =
    match l with
    | [] -> Ok (List.rev acc)
    | x :: xs ->
      match Builtin.of_string (Loc.content x) with
      | None ->
        Error
          (Error_msg.make
             (Loc.tag x)
             (Fmt.str "Unrecognized builtin %s" (Loc.content x))
          )
      | Some b ->
        aux (Loc.update_content b x :: acc) xs
  in
  aux [] l

let map_spec (spec : Spec.t) : (Spec.t, Error_msg.t) result =
  let open Tg_ast in
  let rec aux
      (builtins : string Loc.tagged list option)
      (acc : Tg_ast.decl list)
      (decls : Tg_ast.decl list)
    : (string Loc.tagged list option * Tg_ast.decl list, Error_msg.t) result =
    match decls with
    | [] -> Ok (builtins, List.rev acc)
    | d :: ds ->
      match d with
      | D_builtins l -> (
          match builtins with
          | None -> aux (Some l) acc ds
          | Some l' ->
            Error (
              Error_msg.make
                (Loc.tag (List.hd l'))
                (Fmt.str "Builtins already specified at %a"
                   Loc.pp_opt_uncapitalized (Loc.tag (List.hd l))
                )
            )
        )
      | D_modul (name, m) ->
        let* builtins, m = aux builtins [] m in
        aux builtins (D_modul (name, m) :: acc) ds
      | _ ->
        aux builtins (d :: acc) ds
  in
  let* builtin_strings, root = aux None [] spec.root in
  let builtin_strings = Option.value ~default:[] builtin_strings in
  let* builtins = parse_builtins builtin_strings in
  let builtin_decls =
    builtins
    |> List.map Loc.content
    |> List.map Builtin.to_decls
    |> List.flatten
  in
  Ok
    {
      spec with
      root = builtin_decls @ base @ root;
      builtins;
    }
