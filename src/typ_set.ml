include CCSet.Make (struct
    type t = Typ.term

    let compare = compare
  end)
