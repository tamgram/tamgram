type t = {
  builtins : Builtin.t Loc.tagged list;
  root : Tg_ast.modul;
  root_lexical_ctx_for_var : Lexical_ctx.t;
  root_lexical_ctx_for_func : Lexical_ctx.t;
  root_lexical_ctx_for_form : Lexical_ctx.t;
  root_typ_ctx : Typ.Ctx.t;
  proc_graphs : Tg_graph.t Name_map.t;
  well_defined_cells : String_tagged_set.t Int_map.t;
  cells_to_carry_over_before : String_tagged_set.t Int_map.t;
  cells_to_carry_over_after : String_tagged_set.t Int_map.t;
  cell_usages : Cell_lifetime.Usage.t Int_map.t;
  rule_tags : string Int_map.t;
  user_specified_cell_pat_matches : (string Loc.tagged * Tg_ast.term) list Int_map.t;
  cell_data_most_general_shape : Tg_ast.cell_data_shape String_map.t Int_map.t;
  cell_data_possible_shapes : Cell_data_shape_set.t String_map.t Int_map.t;
  warnings : Error_msg.t list;
}

let make (root : Tg_ast.modul) : t =
  {
    builtins = [];
    root;
    root_lexical_ctx_for_var = Lexical_ctx.empty;
    root_lexical_ctx_for_func = Lexical_ctx.empty;
    root_lexical_ctx_for_form = Lexical_ctx.empty;
    root_typ_ctx = Typ.Ctx.empty;
    proc_graphs = Name_map.empty;
    cells_to_carry_over_before = Int_map.empty;
    cells_to_carry_over_after = Int_map.empty;
    well_defined_cells = Int_map.empty;
    cell_usages = Int_map.empty;
    rule_tags = Int_map.empty;
    user_specified_cell_pat_matches = Int_map.empty;
    cell_data_most_general_shape = Int_map.empty;
    cell_data_possible_shapes = Int_map.empty;
    warnings = [];
  }

let print_warnings file_buffers (t : t) =
  List.iter (Error_msg.print file_buffers)
    t.warnings
