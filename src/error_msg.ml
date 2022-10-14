type typ = [
  | `Error
  | `Warning
]

type t =
  | With_loc of {
      loc : Loc.t option;
      typ : typ;
      msg : string;
    }
  | Msg_only of string

let make ?(typ = `Error) loc msg =
  With_loc { loc; typ; msg }

let make_msg_only msg =
  Msg_only msg

let print (file_buffers : File_buffer.t String_map.t) (t : t) =
  let empty_list_if_not_atty l =
    if Unix.isatty Unix.stderr then
      l
    else
      []
  in
  match t with
  | With_loc { loc; typ; msg } -> (
      let loc_str = Fmt.str "%a" Loc.pp_opt loc in
      let lnum_cnum_and_line =
        match loc with
        | None -> None
        | Some loc ->
          match String_map.find_opt Loc.(loc.file_name) file_buffers with
          | None -> None
          | Some buf ->
            try Some
                  (Loc.(loc.lnum), Loc.(loc.cnum), buf.lines.(loc.lnum - 1))
            with Invalid_argument _ -> None
      in
      ANSITerminal.(eprintf
                      (empty_list_if_not_atty [ Bold ]) "%s\n" loc_str);
      Option.iter (fun (lnum, cnum, line) ->
          let prefix = Printf.sprintf "%d | " lnum in
          let prefix_len = String.length prefix in
          Printf.eprintf "%s%s\n" prefix line;
          Printf.eprintf "%*s%s\n" (prefix_len + cnum) " " "^"
        ) lnum_cnum_and_line;
      (match typ with
       | `Error ->
         ANSITerminal.(eprintf
                         (empty_list_if_not_atty [ Bold; red ]) "Error: ")
       | `Warning ->
         ANSITerminal.(eprintf
                         (empty_list_if_not_atty [ Bold; magenta ]) "Warning: ")
      );
      Printf.eprintf "%s\n" msg
    )
  | Msg_only msg ->
    Printf.eprintf "%s\n" msg
