open Result_syntax

type t = File_buffer.t String_map.t

let of_dir ~dir : (t, Error_msg.t) result =
  let available_files = Sys.readdir dir
                        |> Array.to_list
                        |> List.filter (fun file ->
                            not (Sys.is_directory (Filename.concat dir file))
                            &&
                            CCString.suffix ~suf:Params.file_extension file)
  in
  List.fold_left (fun m file_name ->
      let* m = m in
      let+ content = Modul_load.read_file ~base_dir:dir ~file_name in
      String_map.add file_name (File_buffer.of_string content) m
    )
    (Ok String_map.empty)
    available_files
