open Result_let

let file_buffers = ref String_map.empty

let from_file' (file : string) : (Tg_ast.modul, Error_msg.t) result =
  if not (Sys.file_exists file) then
    Error (Error_msg.make_msg_only (Fmt.str "File %s does not exist" file))
  else
    let dir = Filename.dirname file in
    let* (available_files : string list String_map.t) =
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
    let rec aux (seen : (string * string) list) (m : Tg_ast.modul) modul_name
        file =
      let* actual_file =
        match
          String_map.find_opt (String.lowercase_ascii file) available_files
        with
        | None ->
          Error
            (Error_msg.make_msg_only
               (Printf.sprintf
                  "File compatible with %s missing, required by module %s" file
                  (fst @@ List.hd seen))
            )
        | Some [ x ] -> Ok x
        | Some _ ->
          Error
            (Error_msg.make_msg_only
               (Printf.sprintf
                  "Multiple files compatible with %s, required by module %s" file
                  (fst @@ List.hd seen))
            )
      in
      let* s =
        try
          Ok
            CCIO.(
              with_in (Filename.concat dir actual_file) (fun ic -> read_all ic))
        with
        | Sys_error _ ->
          Error (Error_msg.make_msg_only (Printf.sprintf "Failed to open file %s" file))
      in
      file_buffers :=
        String_map.add actual_file (File_buffer.of_string s)
          !file_buffers;
      let* m' = Tg.parse_modul actual_file s in
      let m =
        match modul_name with
        | None -> m'
        | Some name -> D_modul (Loc.untagged name, m') :: m
      in
      match Lexical_ctx_analysis.missing_top_level_modul m with
      | None -> Ok m
      | Some missing -> (
          match List.assoc_opt missing seen with
          | Some _ ->
            Error
              (Error_msg.make_msg_only
                 (Fmt.str "Cannot compile due to dependency cycle:@,@[<v>   %a@]"
                    Fmt.(
                      list ~sep:(any "@,-> ")
                        (fun formatter (name, actual_file) ->
                           Fmt.pf formatter "module %s as file %s" name
                             actual_file))
                    (List.rev seen))
              )
          | None -> aux ((missing, actual_file) :: seen) m (Some missing) (missing ^ Params.file_extension))
    in
    let root_file =
      Filename.basename file
    in
    let root_modul_name =
      CCString.chop_suffix ~suf:Params.file_extension root_file
      |> Option.value ~default:file
      |> String.capitalize_ascii
    in
    aux [ (root_modul_name, root_file) ] [] None root_file

let from_file file =
  file_buffers := String_map.empty;
  (!file_buffers, from_file' file)
