include CCSet.Make (struct
    type t = int * int

    let compare ((x0, y0) : t) ((x1, y1) : t) =
      if x0 < x1 then -1
      else if x0 = x1 then Int.compare y0 y1
      else 1
  end)

