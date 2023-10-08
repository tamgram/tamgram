open Cmdliner
open Cli_utils

let input_file_arg =
  let doc = "Input dot file" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"DOT" ~doc)

let run
    (flags : bool list)
    (l : string list)
  : int =
    Fmt.pr "@[<v>%a@.@]" Fmt.(list bool) flags;
    Fmt.pr "@[<v>%a@.@]" Fmt.(list string) l;
  0

let cmd =
  Cmd.(v (info "rewrite-dot")
         Term.(const run
               $ Arg.(value & flag_all & info ["T"])
               $ Arg.(value & pos_all string [] & info [])
              ))
