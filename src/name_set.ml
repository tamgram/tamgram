include CCSet.Make (struct
    type t = Name.t

    let compare (x : Name.t) (y : Name.t) =
      match (x, y) with
      | `Local x, `Local y | `Global x, `Global y -> Int.compare x y
      | `Local _, `Global _ -> 1
      | `Global _, `Local _ -> -1
  end)
