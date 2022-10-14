type 'a t

val make : ?name:Name.t -> string Loc.tagged -> 'a -> 'a t

val make_untagged : ?name:Name.t -> string -> 'a -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

val update : 'a -> 'b t -> 'a t

val update_loc : Loc.t option -> 'a t -> 'a t

val update_name : Name.t -> 'a t -> 'a t

val update_name_str : string Loc.tagged -> 'a t -> 'a t

val update_name_str_untagged : string -> 'a t -> 'a t

val get : 'a t -> 'a

val name_str : 'a t -> string Loc.tagged

val name_str_untagged : 'a t -> string

val name : 'a t -> Name.t

val loc : 'a t -> Loc.t option
