type 'a t = {
  name_str : string Loc.tagged;
  name : Name.t;
  bound_to : 'a;
}

let make ?(name = `Local 0) name_str bound_to = { name_str; name; bound_to }

let make_untagged ?name name_str bound_to =
  make ?name (Loc.untagged name_str) bound_to

let map (f : 'a -> 'b) (x : 'a t) : 'b t = { x with bound_to = f x.bound_to }

let update (bound_to : 'a) (x : 'b t) : 'a t = { x with bound_to }

let update_name (name : Name.t) (x : 'a t) : 'a t = { x with name }

let update_name_str (name_str : string Loc.tagged) (x : 'a t) : 'a t =
  { x with name_str }

let update_name_str_untagged (name_str : string) (x : 'a t) : 'a t =
  update_name_str (Loc.untagged name_str) x

let update_loc (loc : Loc.t option) (x : 'a t) : 'a t =
  { x with name_str = Loc.update_tag loc x.name_str }

let get (x : 'a t) : 'a = x.bound_to

let name_str (x : 'a t) : string Loc.tagged = x.name_str

let name_str_untagged (x : 'a t) : string = Loc.content (name_str x)

let name (x : 'a t) : Name.t = x.name

let loc (x : 'a t) = Loc.tag x.name_str
