type t = {
  names_external_to_modul : Name.t String_map.t;
  names : Name.t String_map.t;
  external_moduls : t String_map.t;
  submoduls : t String_map.t;
}

let empty : t =
  {
    names_external_to_modul = String_map.empty;
    names = String_map.empty;
    external_moduls = String_map.empty;
    submoduls = String_map.empty;
  }

let name_indices_given = ref 0

let reset_name_indices_given_count () = name_indices_given := 0

let incr_name_indices_given_count () =
  name_indices_given := succ !name_indices_given

let visible_names (t : t) : Name.t String_map.t =
  String_map.union (fun _ _ x -> Some x) t.names_external_to_modul t.names

let exposed_names (t : t) : Name.t String_map.t = t.names

let visible_moduls (t : t) : t String_map.t =
  String_map.union (fun _ _ x -> Some x) t.external_moduls t.submoduls

let exposed_moduls (t : t) : t String_map.t = t.submoduls

let get_new_name_index () : int =
  let id = !name_indices_given in
  incr_name_indices_given_count ();
  id

let update_name_index_of_decl (name_index : int) (decl : Tg_ast.decl) :
  Tg_ast.decl =
  let name = `Global name_index in
  match decl with
  | D_process x ->
    D_process { binding = Binding.update_name name x.binding }
  | D_process_macro x ->
    D_process_macro (Binding.update_name name x)
  | D_let x -> D_let { binding = Binding.update_name name x.binding }
  | D_fun x -> D_fun (Binding.update_name name x)
  | D_pred x -> D_pred (Binding.update_name name x)
  | D_ppred x -> D_ppred (Binding.update_name name x)
  | D_apred x -> D_apred (Binding.update_name name x)
  | D_papred x -> D_papred (Binding.update_name name x)
  | D_macro x -> D_macro { binding = Binding.update_name name x.binding }
  | D_lemma x -> D_lemma { binding = Binding.update_name name x.binding }
  | D_restriction x ->
    D_restriction { binding = Binding.update_name name x.binding }
  | D_equation x ->
    D_equation { binding = Binding.update_name name x.binding }
  | D_rule x -> D_rule { binding = Binding.update_name name x.binding }
  | D_modul _ | D_open _ | D_insert _ | D_builtins _ -> decl

let name_of_decl (decl : Tg_ast.decl) : Name.t =
  match decl with
  | D_process { binding; _ } -> Binding.name binding
  | D_process_macro binding -> Binding.name binding
  | D_let { binding; _ } -> Binding.name binding
  | D_fun x -> Binding.name x
  | D_pred x -> Binding.name x
  | D_ppred x -> Binding.name x
  | D_apred x -> Binding.name x
  | D_papred x -> Binding.name x
  | D_macro { binding; _ } -> Binding.name binding
  | D_lemma { binding; _ } -> Binding.name binding
  | D_restriction { binding; _ } -> Binding.name binding
  | D_equation { binding; _ } -> Binding.name binding
  | D_rule { binding; _ } -> Binding.name binding
  | D_modul _ | D_open _ | D_insert _ | D_builtins _ -> failwith "Unexpected case"

let add_decl ?(reuse_name_global = false) (decl : Tg_ast.decl) (t : t) :
  t * Tg_ast.decl =
  let name_str =
    let open Tg_ast in
    match decl with
    | D_process { binding; _ } -> Some (Binding.name_str_untagged binding)
    | D_process_macro binding -> Some (Binding.name_str_untagged binding)
    | D_let { binding; _ } -> Some (Binding.name_str_untagged binding)
    | D_fun binding -> Some (Binding.name_str_untagged binding)
    | D_pred binding -> Some (Binding.name_str_untagged binding)
    | D_ppred binding -> Some (Binding.name_str_untagged binding)
    | D_apred binding -> Some (Binding.name_str_untagged binding)
    | D_papred binding -> Some (Binding.name_str_untagged binding)
    | D_macro { binding; _ } -> Some (Binding.name_str_untagged binding)
    | D_lemma { binding; _ } -> Some (Binding.name_str_untagged binding)
    | D_restriction { binding; _ } -> Some (Binding.name_str_untagged binding)
    | D_equation { binding; _ } -> Some (Binding.name_str_untagged binding)
    | D_rule { binding; _ } -> Some (Binding.name_str_untagged binding)
    | D_modul _ | D_open _ | D_insert _ | D_builtins _ -> None
  in
  match name_str with
  | None -> (t, decl)
  | Some name_str ->
    if reuse_name_global then
      ( { t with names = String_map.add name_str (name_of_decl decl) t.names },
        decl )
    else
      let name_index = get_new_name_index () in
      let decl = update_name_index_of_decl name_index decl in
      ( { t with names = String_map.add name_str (`Global name_index) t.names },
        decl )

let add_local_name_str (name_str : string) (t : t) : t * Name.t =
  let name_index = get_new_name_index () in
  let name = `Local name_index in
  ({ t with names = String_map.add name_str name t.names }, name)

let add_local_name_strs (l : string list) (t : t) : t * Name.t list =
  CCList.fold_map
    (fun t x ->
       let t, x = add_local_name_str x t in
       (t, x))
    t l

let fresh_local_name () : string * Name.t =
  let name_index = get_new_name_index () in
  let name = `Local name_index in
  (Printf.sprintf "%s%d" Params.auto_gen_name_prefix name_index, name)

let add_submodul (name : string) ~(submodul : t) (t : t) : t =
  { t with submoduls = String_map.add name submodul t.submoduls }

let enter_sublevel (t : t) : t =
  {
    names_external_to_modul =
      String_map.union (fun _ _ x -> Some x) t.names_external_to_modul t.names;
    names = String_map.empty;
    external_moduls =
      String_map.union (fun _ _ x -> Some x) t.external_moduls t.submoduls;
    submoduls = String_map.empty;
  }

let open_modul ~(into : t) (t : t) : t =
  {
    into with
    names_external_to_modul =
      String_map.union
        (fun _ _ x -> Some x)
        into.names_external_to_modul (exposed_names t);
    external_moduls =
      String_map.union (fun _ _ x -> Some x) into.external_moduls t.submoduls;
  }

let insert_modul ~(into : t) (t : t) : t =
  {
    into with
    names = String_map.union (fun _ _ x -> Some x) into.names (exposed_names t);
    submoduls =
      String_map.union (fun _ _ x -> Some x) into.submoduls t.submoduls;
  }

type direction =
  [ `Global
  | `Inward
  ]

type modul_resolution_error =
  [ `Missing_top_level_modul of string
  | `Missing_middle_modul of string
  ]

type name_resolution_error =
  [ `Missing_top_level_modul of string
  | `Missing_middle_modul of string
  | `Missing_name of string
  ]

let resolve_modul ?(path_for_error_msg : Path.t option) (path : Path.t)
    (ctx : t) : (t, Error_msg.t * modul_resolution_error) result =
  let rec aux (direction : direction) path_for_error_msg path ctx =
    match path with
    | [] -> Ok ctx
    | x :: xs -> (
        let search_space =
          match direction with
          | `Global -> visible_moduls ctx
          | `Inward -> ctx.submoduls
        in
        match String_map.find_opt (Loc.content x) search_space with
        | None ->
          Error
            (Error_msg.make
               (Loc.tag x)
               (Fmt.str "unbound module %s in path %s"
                  (Loc.content x)
                  (Path.to_string path_for_error_msg)),
             match direction with
             | `Global -> `Missing_top_level_modul (Loc.content x)
             | `Inward -> `Missing_middle_modul (Loc.content x)
            )
        | Some ctx -> (
            match xs with
            | [] -> Ok ctx
            | _ -> aux `Inward path_for_error_msg xs ctx))
  in
  let path_for_error_msg = Option.value ~default:path path_for_error_msg in
  aux `Global path_for_error_msg path ctx

let resolve_name (path : Path.t) (ctx : t) :
  (Name.t, Error_msg.t * name_resolution_error) result =
  let modul_path, name =
    match List.rev path with
    | [] -> failwith "Unexpected case: empty path"
    | x :: xs -> (List.rev xs, x)
  in
  match resolve_modul ~path_for_error_msg:path modul_path ctx with
  | Error (msg, e) -> Error (msg, (e :> name_resolution_error))
  | Ok m -> (
      let search_space =
        match modul_path with [] -> visible_names m | _ -> exposed_names m
      in
      match String_map.find_opt (Loc.content name) search_space with
      | None ->
        Error
          (Error_msg.make (Loc.tag name)
             (Fmt.str "unbound value %s"
                (Path.to_string path)),
           `Missing_name (Loc.content name) )
      | Some name' -> Ok name')
