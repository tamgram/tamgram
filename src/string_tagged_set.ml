include CCSet.Make (struct
    type t = string Loc.tagged

    let compare x y = String.compare (Loc.content x) (Loc.content y)
  end)
