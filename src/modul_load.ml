open Result_syntax

let available_files_adjacent ~file : (string list String_map.t, Error_msg.t) result =
  let dir = Filename.dirname file in
  let+ (available_files : string list String_map.t) =
    try
      Ok
        (Sys.readdir dir
         |> Array.to_list
         |> List.fold_left
           (fun m s ->
              let key = String.lowercase_ascii s in
              match String_map.find_opt key m with
              | None -> String_map.add key [ s ] m
              | Some l -> String_map.add key (s :: l) m)
           String_map.empty)
    with Sys_error _ ->
      Error (Error_msg.make_msg_only (Printf.sprintf "Failed to read directory %s" dir))
  in
  available_files

let find_compatible_file ~required_by ~modul_name ~available_files =
  let file = modul_name ^ Params.file_extension
             |> String.lowercase_ascii
  in
  match
    String_map.find_opt (String.lowercase_ascii file) available_files
  with
  | None ->
    Error
      (Error_msg.make_msg_only
         (Printf.sprintf "File compatible with %s missing, required by module %s" file required_by)
      )
  | Some [ x ] -> Ok x
  | Some _ ->
    Error
      (Error_msg.make_msg_only
         (Printf.sprintf "Multiple files compatible with %s, required by module %s" file required_by)
      )

let read_file ~base_dir ~file_name : (string, Error_msg.t) result =
  try
    Ok
      CCIO.(
        with_in (Filename.concat base_dir file_name) (fun ic -> read_all ic))
  with
  | Sys_error _ ->
    Error (Error_msg.make_msg_only (Printf.sprintf "Failed to open file %s" file_name))

let construct_modul_req_graph ~base_dir ~available_files (target : string)
  : (string list String_map.t, Error_msg.t) result =
  let rec aux
      (seen : (string * string) list)
      (modul_name : string)
    : (string list String_map.t, Error_msg.t) result =
    let* actual_file_path =
      find_compatible_file ~required_by:target ~modul_name ~available_files
    in
    let actual_file_name = Filename.basename actual_file_path in
    let* content = read_file ~base_dir ~file_name:actual_file_name in
    let* m = Tg.parse_modul actual_file_name content in
    let seen = (modul_name, actual_file_name) :: seen in
    match Lexical_ctx_analysis.unsatisfied_modul_imports m with
    | [] -> Ok String_map.empty
    | reqs -> (
        let reqs = List.map Loc.content reqs in
        let g = String_map.(add modul_name reqs empty) in
        aux_list g seen reqs
      )
  and aux_list
      (g : string list String_map.t)
      seen
      (modul_names : string list)
    : (string list String_map.t, Error_msg.t) result =
    match modul_names with
    | [] -> Ok g
    | modul_name :: ms -> (
        match List.assoc_opt modul_name seen with
        | Some _ -> (
            Error
              (Error_msg.make_msg_only
                 (Fmt.str "Cannot compile due to dependency cycle:@,@[<v>   %a@]"
                    Fmt.(
                      list ~sep:(any "@,-> ")
                        (fun formatter (modul_name, file_name) ->
                           Fmt.pf formatter "module %s as file %s" modul_name file_name))
                    (List.rev seen))
              )
          )
        | None -> (
            let* g' = aux seen modul_name in
            let g = String_map.union (fun _ reqs0 reqs1 ->
                Some (List.sort_uniq String.compare (reqs0 @ reqs1))
              )
                g g'
            in
            aux_list g seen ms
          )
      )
  in
  aux [] target

let from_file (file : string) : (Tg_ast.modul, Error_msg.t) result =
  if not (Sys.file_exists file) then
    Error (Error_msg.make_msg_only (Fmt.str "File %s does not exist" file))
  else (
    let base_dir = Filename.dirname file in
    let* available_files = available_files_adjacent ~file in
    let modul_name =
      Filename.basename file
      |> CCString.chop_suffix ~suf:Params.file_extension
      |> Option.value ~default:file
      |> String.capitalize_ascii
    in
    let* req_graph = construct_modul_req_graph ~base_dir ~available_files modul_name in
    let* content = read_file ~base_dir ~file_name:(Filename.basename file) in
    let* m = Tg.parse_modul file content in
    Ok m
  )
