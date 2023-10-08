open Cmdliner

let cmds = [ Debug_tg_cmd.cmd; Compile_tg_cmd.cmd; ]

let default =
  Term.(ret (const (`Help (`Pager, None))))

let () =
  let version = Version_string.s in
  Stdlib.exit @@ Cmd.(eval' (group ~default (info "tamgram" ~version) cmds))
