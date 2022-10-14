include CCSet.Make (struct
    type t = Builtin.t

    let compare = compare
  end)
