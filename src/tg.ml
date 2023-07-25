let pos_of_lexbuf lexbuf : int * int =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  (pos.pos_lnum, (pos.pos_cnum - pos.pos_bol))

let parse_modul file_name (input : string) : (Tg_ast.modul, Error_msg.t) result =
  let lexbuf = Lexing.from_string input in
  Lexing.set_filename lexbuf file_name;
  try Ok (Tg_parser.parse Tg_lexer.read lexbuf) with
  | Syntax_error_exn.Syntax_error msg ->
    let (lnum, cnum) = pos_of_lexbuf lexbuf in
    Error (Error_msg.make
             (Some Loc.{ file_name; lnum; cnum })
             msg
          )
  | Tg_parser.Error ->
    let (lnum, cnum) = pos_of_lexbuf lexbuf in
    Error (Error_msg.make
             (Some Loc.{ file_name; lnum; cnum })
             "Syntax error"
          )

let default_pipeline =
  [
    ("Add builtins", Add_builtins.map_spec);
    ("Missing builtin check", Missing_builtin_check.map_spec);
    (* ("Rewrite dots in named arguments", Rewrite_dots_in_named_args.map_spec); *)
    ("Name check", Name_check.map_spec);
    ("Cell usage check", Cell_usage_check.map_spec);
    ("Uninterpreted predicate check", Pred_check.map_spec);
    ("Duplicate uninterpreted function symbols check",
     Dup_uninterpreted_fun_symbols_check.map_spec );
    ("Rewrite uninterpreted function symbols with explicit arguments",
     Rewrite_uninterpreted_fun_symbols_exp_args.map_spec);
    ("Pattern matching syntax check", Pattern_matching_syntax_check.map_spec);
    ("Rewrite wildcard character", Rewrite_wildcard_char.map_spec);
    ("Rewrte term name as", Rewrite_term_name_as.map_spec);
    ("Lexical context anaylsis", Lexical_ctx_analysis.map_spec);
    ("Type checking", Typ_check.map_spec);
    ("Unused name check", Unused_name_check.map_spec);
    ("Reduce let bindings", Reduce_let_bindings.map_spec);
    ("Expand macro applications", Expand_macro_apps.map_spec);
    ("Fact usage check", Fact_usage_check.map_spec);
    ("Rewrite singleton processes into rules", Rewrite_singleton_processes_into_rules.map_spec);
    ("Add starting rules", Add_start_rules.map_spec);
    ("Construct process graphs", Construct_proc_graphs.map_spec);
    ("Propagate type annotations", Propagate_typ_annotations.map_spec);
    ("Cell usage check", Cell_usage_check.map_spec);
    ("Record cell usages", Record_cell_usages.map_spec);
    ("Cell lifetime check", Cell_lifetime_check.map_spec);
    ("Derive process contexts required", Derive_proc_ctxs_required.map_spec);
    ("Cell data shape analysis", Cell_data_shape_analysis.map_spec);
    ("Clean up user specified cell pattern matches",
     Clean_up_user_specified_cell_pattern_matches.map_spec);
    ("User specified cell pattern match analysis",
     User_specified_cell_pattern_match_analysis.map_spec);
    ("Translate to Tamarin rules", Translate.map_spec);
    ("Lexical context anaylsis", Lexical_ctx_analysis.map_spec);
  ]

let string_of_default_pipeline : string =
  String.concat "\n"
    (List.mapi
       (fun i (desc, _f) -> Printf.sprintf "Stage %d - %s." i desc)
       default_pipeline)

let run_pipeline ?(pipeline = default_pipeline)
    ?(stop_before_stage = List.length pipeline) (spec : Spec.t) :
  (Spec.t, Error_msg.t) result =
  let _, spec =
    List.fold_left
      (fun (stage, spec) (_desc, f) ->
         ( succ stage,
           if stage >= stop_before_stage then spec else Result.bind spec f ))
      (0, Ok spec) pipeline
  in
  spec
