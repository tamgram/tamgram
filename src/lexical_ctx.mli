type t

val reset_name_indices_given_count : unit -> unit

val empty : t

val add_local_name_str : string -> t -> t * Name.t

val add_local_name_strs : string list -> t -> t * Name.t list

val fresh_local_name : unit -> string * Name.t

val add_submodul : string -> submodul:t -> t -> t

val enter_sublevel : t -> t

(* val open_modul : into:t -> t -> t

   val insert_modul : into:t -> t -> t *)

type modul_resolution_error = [
  | `Missing_top_level_modul of string
  | `Missing_middle_modul of string
]

type name_resolution_error = [
  | `Missing_top_level_modul of string
  | `Missing_middle_modul of string
  | `Missing_name of string
]

val resolve_modul : ?path_for_error_msg:Path.t -> Path.t -> t -> (t, Error_msg.t * modul_resolution_error) result

val resolve_name : Path.t -> t -> (Name.t, Error_msg.t * name_resolution_error) result

val add_decl : ?reuse_name_global:bool -> Tg_ast.decl -> t -> t * Tg_ast.decl
