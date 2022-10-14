type t = string Loc.tagged list

let loc t = Loc.tag @@ List.hd t

let of_string (s : string) : t =
  String.split_on_char '.' s |> List.map Loc.untagged

let to_string (path : t) : string =
  String.concat "." (List.map Loc.content path)
