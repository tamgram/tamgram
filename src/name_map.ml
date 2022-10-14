include Map.Make (struct
    type t = Name.t

    let compare = compare
  end)
