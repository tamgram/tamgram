type t = {
  lines : string array;
}

let of_string (s : string) : t =
  { lines = CCString.lines s |> Array.of_list }
