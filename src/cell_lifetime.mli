module Usage : sig
  type t

  val empty : t

  val union : t -> t -> t

  val update : so_far:t -> t -> t

  val merge_parallel : t -> t -> t

  val merge_parallel_multi : t list -> t

  val add_require : string Loc.tagged -> t -> t
  val add_define : string Loc.tagged -> t -> t
  val add_undefine : string Loc.tagged -> t -> t

  val remove_require : string Loc.tagged -> t -> t
  val remove_define : string Loc.tagged -> t -> t
  val remove_undefine : string Loc.tagged -> t -> t

  val add_requires : String_tagged_set.t -> t -> t
  val add_defines : String_tagged_set.t -> t -> t
  val add_undefines : String_tagged_set.t -> t -> t

  val requires_cells : t -> String_tagged_set.t
  val defines_cells : t -> String_tagged_set.t
  val undefines_cells : t -> String_tagged_set.t
end

module Ctx : sig
  type t

  val empty :t 

  val update_from_usage : Usage.t -> t -> t

  val defined_cells : t -> String_tagged_set.t
end

val check_usage_is_satisfied : Ctx.t -> Usage.t -> (unit, string Loc.tagged) result
