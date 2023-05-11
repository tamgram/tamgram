type term = [
  | `Cell
  | `Temporal
  | `Bitstring
  | `Pub
  | `Fresh
  | `Fact
  | `Pfact
  | `Afact
  | `Pafact
  | `Formula
  | `Pat_match
  | `Statement
  | `Fun of (string * term) list * term list * term
  | `Process
  | `Subroutine of int * int
  | `Equation
  | `Lemma
  | `Restriction
  | `Rule
]

module Ctx : sig
  type t

  val empty : t

  val union : t -> t -> t

  val add : Name.t -> term -> t -> t

  val add_multi : (Name.t * term) list -> t -> t

  val find : Name.t -> t -> term option
end
