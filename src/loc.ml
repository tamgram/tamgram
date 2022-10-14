type t = {
  file_name : string;
  lnum : int;
  cnum : int;
}

type 'a tagged = {
  loc : t option;
  content : 'a;
}

let pp_opt (formatter : Format.formatter) (x : t option) : unit =
  match x with
  | None -> Fmt.pf formatter "Location N/A (system generated name)"
  | Some x -> Fmt.pf formatter "File \"%s\", line %d, character %d" x.file_name x.lnum x.cnum

let pp_opt_uncapitalized (formatter : Format.formatter) (x : t option) : unit =
  match x with
  | None -> Fmt.pf formatter "location N/A (system generated name)"
  | Some x -> Fmt.pf formatter "file \"%s\", line %d, character %d" x.file_name x.lnum x.cnum

let pp_loc_of_tagged (formatter : Format.formatter) (x : 'a tagged) : unit =
  pp_opt formatter x.loc

let pp_loc_of_tagged_uncapitalized (formatter : Format.formatter) (x : 'a tagged) : unit =
  pp_opt_uncapitalized formatter x.loc

let map (f : 'a -> 'b) (t : 'a tagged) : 'b tagged =
  { t with content = f t.content }

let content (t : 'a tagged) : 'a = t.content

let tag (t : 'a tagged) : t option = t.loc

let untagged (content : 'a) : 'a tagged = { loc = None; content }

let update_content (content : 'a) (x : 'b tagged) : 'a tagged =
  { x with content }

let update_tag (loc : t option) (x : 'a tagged) = { x with loc }

let update_tag_multi (loc : t option) (l : 'a tagged list) =
  List.map (update_tag loc) l

