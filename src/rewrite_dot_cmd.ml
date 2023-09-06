let debug_arg = Arg.(value & flag & info [ "debug" ])

let run
    (debug : bool)
  : int =
  0

let cmd =
  Cmd.(v (info "rewrite-dot")
         Term.(const run
               $ debug_arg
              ))
