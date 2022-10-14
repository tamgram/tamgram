include CCSet.Make (struct
    type t = Tg_ast.cell_data_shape

    let compare = compare
  end)
