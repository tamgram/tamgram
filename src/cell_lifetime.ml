module Usage = struct
  type t = {
    requires_cells : String_tagged_set.t;
    defines_cells : String_tagged_set.t;
    undefines_cells : String_tagged_set.t;
  }

  let empty : t =
    {
      requires_cells = String_tagged_set.empty;
      defines_cells = String_tagged_set.empty;
      undefines_cells = String_tagged_set.empty;
    }

  let union (x : t) (y : t) : t =
    {
      requires_cells = String_tagged_set.union x.requires_cells y.requires_cells;
      defines_cells = String_tagged_set.union x.defines_cells y.defines_cells;
      undefines_cells =
        String_tagged_set.union x.undefines_cells y.undefines_cells;
    }

  let update ~(so_far : t) (x : t) : t =
    {
      requires_cells =
        String_tagged_set.union so_far.requires_cells
          (String_tagged_set.diff x.requires_cells so_far.defines_cells);
      defines_cells =
        String_tagged_set.(
          union (diff so_far.defines_cells x.undefines_cells) x.defines_cells);
      undefines_cells =
        String_tagged_set.(
          union (diff so_far.undefines_cells x.defines_cells) x.undefines_cells);
    }

  let merge_parallel (x1 : t) (x2 : t) : t =
    let undefines_cells =
      String_tagged_set.union x1.undefines_cells x2.undefines_cells
    in
    {
      requires_cells =
        String_tagged_set.union x1.requires_cells x2.requires_cells;
      defines_cells =
        (String_tagged_set.inter x1.defines_cells x2.defines_cells
         |> fun x -> String_tagged_set.diff x undefines_cells);
      undefines_cells;
    }

  let merge_parallel_multi (l : t list) : t =
    Option.value ~default:empty
    @@ List.fold_left
      (fun acc x ->
         match acc with
         | None -> Some x
         | Some acc -> Some (merge_parallel acc x))
      None l

  let add_require name (x : t) : t =
    { x with requires_cells = String_tagged_set.add name x.requires_cells }

  let add_define name (x : t) : t =
    { x with defines_cells = String_tagged_set.add name x.defines_cells }

  let add_undefine name (x : t) : t =
    { x with undefines_cells = String_tagged_set.add name x.undefines_cells }

  let add_requires names (x : t) : t =
    { x with requires_cells = String_tagged_set.union names x.requires_cells }

  let add_defines names (x : t) : t =
    { x with defines_cells = String_tagged_set.union names x.defines_cells }

  let add_undefines names (x : t) : t =
    { x with undefines_cells = String_tagged_set.union names x.undefines_cells }

  let requires_cells (x : t) = x.requires_cells

  let defines_cells (x : t) = x.defines_cells

  let undefines_cells (x : t) = x.undefines_cells

  let remove_require name (x : t) : t =
    { x with requires_cells = String_tagged_set.remove name x.requires_cells }

  let remove_define name (x : t) : t =
    { x with defines_cells = String_tagged_set.remove name x.defines_cells }

  let remove_undefine name (x : t) : t =
    { x with undefines_cells = String_tagged_set.remove name x.undefines_cells }
end

module Ctx = struct
  type t = { defined_cells : String_tagged_set.t }

  let empty = { defined_cells = String_tagged_set.empty }

  let update_from_usage (usage : Usage.t) (ctx : t) : t =
    let defined_cells =
      ctx.defined_cells
      |> (fun x ->
          String_tagged_set.union x usage.defines_cells
        )
      |> (fun x -> String_tagged_set.diff x usage.undefines_cells)
    in
    { defined_cells }

  let defined_cells t = t.defined_cells
end

let check_usage_is_satisfied (ctx : Ctx.t)
    (usage : Usage.t) : (unit, string Loc.tagged) result =
  let missing =
    String_tagged_set.diff usage.requires_cells ctx.defined_cells
  in
  match String_tagged_set.min_elt_opt missing with
  | None -> Ok ()
  | Some x -> Error x
