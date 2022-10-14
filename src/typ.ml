type term =
  [ `Cell
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
  | `Fun of term list * term
  | `Process
  | `Subroutine of int * int
  | `Equation
  | `Lemma
  | `Restriction
  | `Rule
  ]

module Ctx = struct
  type t = { assigns : term Name_map.t }

  let empty : t = { assigns = Name_map.empty }

  let union (t1 : t) (t2 : t) : t =
    {
      assigns =
        Name_map.union
          (fun _ _ _ -> failwith "Unexpected case")
          t1.assigns t2.assigns;
    }

  let add (name : Name.t) (typ : term) (t : t) : t =
    { assigns = Name_map.add name typ t.assigns }

  let add_multi (l : (Name.t * term) list) (t : t) : t =
    List.fold_left (fun t (name, typ) -> add name typ t) t l

  let find (name : Name.t) (t : t) : term option =
    Name_map.find_opt name t.assigns
end
