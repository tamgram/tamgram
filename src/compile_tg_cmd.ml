open Cmdliner
open Cli_utils

let input_file_arg =
  let doc = "Input Tamgram file" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"TG_SRC" ~doc)

let output_file_arg =
  let doc = "Output Tamarin file" in
  Arg.(required & pos 1 (some string) None & info [] ~docv:"DEST" ~doc)

let pp_path formatter (path : string Loc.tagged list) : unit =
  let s = Loc.content (List.hd (List.rev path)) in
  Fmt.pf formatter "%s" s

let pp_quant formatter (quant : Typ.term Binding.t) =
  let prefix = Printers.prefix_of_typ (Binding.get quant) in
  Fmt.pf formatter "%s%a" prefix pp_path
    [Binding.name_str quant]

let pp_term (formatter : Format.formatter) (x : Tg_ast.term) : unit =
  let open Tg_ast in
  let rec aux formatter x =
    match x with
    | T_value x -> (
        match Loc.content x with
        | `Str s -> Fmt.pf formatter "'%s'" s
        | `T -> Fmt.pf formatter "T"
        | `F -> Fmt.pf formatter "F")
    | T_symbol (name, symbol_sort) ->
      Fmt.pf formatter "%s%s"
        (match symbol_sort with
         | `Pub -> "$"
         | `Cell ->
           failwith (Fmt.str "Unexpected case: sees cell '%s at %a\n "
                       (Loc.content name)
                       Loc.pp_loc_of_tagged name ))
        (Loc.content name)
    | T_name_as (_x, _name) ->
      failwith "Unexpected case"
    | T_var (path, _name, typ) -> (
        let prefix =
          match typ with
          | None -> ""
          | Some typ -> Printers.prefix_of_typ typ
        in
        Fmt.pf formatter "%s%a" prefix pp_path
          path
      )
    | T_app { path; named_args; args; anno } -> (
        let pp_arg formatter x =
          match x with
          | `Named (s, x) -> Fmt.pf formatter "%s:%a" s aux x
          | `Unnamed x -> Fmt.pf formatter "%a" aux x
        in
        if List.mem
            (Loc.content (List.hd path)) Params.builtin_constants
        then
          Fmt.pf formatter "%a" pp_path path
        else
          Fmt.pf formatter "%a(@[<h>%a@])%a" pp_path path
            Fmt.(list ~sep:comma pp_arg)
            (List.map (fun x -> `Named x) named_args
             @ List.map (fun x -> `Unnamed x) args)
            Printers.pp_fact_anno anno
      )
    | T_unary_op (op, x) ->
      Fmt.pf formatter "%s%a"
        (match op with `Persist -> "!" | `Not -> "not ")
        aux x
    | T_binary_op (op, x, y) ->
      Fmt.pf formatter "((%a) %s (%a))" aux x
        (match op with
         | `Exp -> "^"
         | `Eq -> "="
         | `Iff -> "<=>"
         | `Imp -> "==>"
         | `Or -> "|"
         | `And -> "&"
         | `Plus -> "+"
         | `Xor -> "XOR"
        )
        aux y
    | T_cell_pat_match _
    | T_cell_assign _
    | T_let _
    | T_let_macro _
      ->
      failwith "Unexpected case"
    | T_tuple (_, l) -> (
        match l with
        | [] -> Fmt.pf formatter "'empty_tuple'"
        | _ ->
          Fmt.pf formatter "@[<h><%a>@]" Fmt.(list ~sep:comma aux) l
      )
    | T_action { fact; temporal } ->
      Fmt.pf formatter "%a @@ %a" aux fact aux
        (T_var ([ fst temporal ], snd temporal, Some `Temporal))
    | T_temporal_a_lt_b { a; b } ->
      Fmt.pf formatter "%a < %a" aux
        (T_var ([ fst a ], snd a, Some `Temporal))
        aux
        (T_var ([ fst b ], snd b, Some `Temporal))
    | T_temporal_eq { a; b } ->
      Fmt.pf formatter "%a = %a" aux
        (T_var ([ fst a ], snd a, Some `Temporal))
        aux
        (T_var ([ fst b ], snd b, Some `Temporal))
    | T_quantified { quantifier; quant; formula; _ } ->
      Fmt.pf formatter "@[<v>%s @[<h>%a .@]@,  @[%a@]@]"
        (match quantifier with `Ex -> "Ex" | `All -> "All")
        Fmt.(list ~sep:(any " ") pp_quant)
        quant aux formula
  in
  aux formatter x

let pp_rule (formatter : Format.formatter) (rule : Tg_ast.rule) : unit =
  let open Tg_ast in
  let { l; a; r; _ } = rule in
  let l_count = List.length l in
  let a_count = List.length a in
  let r_count = List.length r in
  if l_count <= 1 && a_count <= 1 && r_count <= 1 then
    Fmt.pf formatter "[%a]--[%a]->[%a]"
      Fmt.(list ~sep:comma pp_term)
      l
      Fmt.(list ~sep:comma pp_term)
      a
      Fmt.(list ~sep:comma pp_term)
      r
  else
    Fmt.pf formatter
      "@[<v>  @[<v>[ %a@ ]@]@,--@[<v>[ %a@ ]->@]@,  @[<v>[ %a@ ]@]@]"
      Fmt.(list ~sep:(any "@,, ") pp_term)
      l
      Fmt.(list ~sep:(any "@,, ") pp_term)
      a
      Fmt.(list ~sep:(any "@,, ") pp_term)
      r

let pp_equation formatter (term : Tg_ast.term) : unit =
  let formula =
    match term with
    | T_quantified { formula; _ } -> formula
    | x -> x
  in
  match formula with
  | T_binary_op (`Eq, x, y) -> Fmt.pf formatter "%a = %a" pp_term x pp_term y
  | _ -> failwith "Unexpected case"

let pp_spec formatter ((theory_name, spec) : string * Spec.t) : unit =
  let rec aux (decls : Tg_ast.decl list) : unit =
    match decls with
    | [] -> ()
    | d :: ds ->
      (match d with
       | D_process _ | D_process_macro _ | D_builtins _ ->
         failwith "Unexpected case"
       | D_fun binding ->
         let name_str = Binding.name_str_untagged binding in
         if List.mem name_str Params.builtin_functions
         || List.mem name_str Params.builtin_constants
         then
           ()
         else
           Fmt.pf formatter "functions: %s/%d@,@,"
             name_str
             (Binding.get binding)
       | D_pred _ | D_ppred _
       | D_apred _ | D_papred _ -> ()
       | D_let _
       | D_macro _  -> failwith "Unexpected case"
       | D_equation { binding } ->
         Fmt.pf formatter "equations: %a@,@," pp_equation
           (Binding.get binding)
       | D_lemma { binding } ->
         let lemma =
           Binding.get binding
         in
         Fmt.pf formatter "lemma %s [%a]:@,  @[<v>%s@,\"%a\"@]@,@,"
           (Binding.name_str_untagged binding)
           Fmt.(list ~sep:comma Printers.pp_lemma_attr) (List.map Loc.content lemma.attrs)
           (match lemma.trace_quantifier with
            | `All_traces -> "all-traces"
            | `Exists_trace -> "exists-trace")
           pp_term lemma.formula
       | D_restriction { binding } ->
         Fmt.pf formatter "restriction %s:@,  \"@[<v>%a@]\"@,@,"
           (Binding.name_str_untagged binding)
           pp_term
           (Binding.get binding)
       | D_rule { binding } ->
         Fmt.pf formatter "rule %s:@,  %a@,@,"
           (Binding.name_str_untagged binding)
           pp_rule
           (Binding.get binding)
       | D_modul (_, decls) ->
         aux decls
       | D_import _ -> ()
      );
      aux ds
  in
  Fmt.pf formatter "@[<v>theory %s@," theory_name;
  Fmt.pf formatter "begin@,@,";
  (
    match spec.builtins with
    | [] -> ()
    | _ ->
      Fmt.pf formatter "builtins: @[<h>%a@]@,@,"
        Fmt.(list ~sep:comma Builtin.pp)
        (List.map Loc.content spec.builtins)
  );
  aux spec.root;
  Fmt.pf formatter "end@,@]@."

let run
    (force_write : bool)
    (skip_possible_cell_data_shape_analysis : bool)
    (use_most_general_cell_data_shape : bool)
    (skip_merge_branches : bool)
    (style : Translate_style.t)
    (input_file : string)
    (output_file : string)
  : int =
  Params.analyze_possible_cell_data_shapes := not skip_possible_cell_data_shape_analysis;
  Params.use_most_general_cell_data_shape := use_most_general_cell_data_shape;
  Params.merge_branches := not skip_merge_branches;
  Params.translate_style := style;
  let base_name = base_name_of_input_file input_file in
  let theory_name =
    base_name
    |> CCString.map (fun c ->
        match c with
        | '.'
        | '-'
          ->
          '_'
        | _ -> c
      )
  in
  let output_file =
    process_output_file ~base_name ~output_file ~suffix:".spthy"
  in
  let output_spec (spec : Spec.t) : unit =
    let f_out formatter =
      Fmt.pf formatter "%a" pp_spec (theory_name, spec)
    in
    match output_file with
    | None -> (
        f_out Fmt.stdout
      )
    | Some output_file -> (
        CCIO.(with_out ~flags:[Open_binary; Open_creat; Open_trunc]
                output_file (fun oc ->
                    f_out (Format.formatter_of_out_channel oc)
                  ))
      )
  in
  if cannot_write ~force_write ~output_file
  then (
    Printf.printf "Output file already exists: %s\n" (Option.get output_file);
    1
  ) else
    let res = Modul_load.from_file input_file in
    let file_buffers = File_buffer_store.of_dir ~dir:(Filename.dirname input_file) in
    match file_buffers with
    | Error msg -> Error_msg.print String_map.empty msg; 1
    | Ok file_buffers -> (
        match res with
        | Error msg -> (
            Error_msg.print file_buffers msg;
            1
          )
        | Ok root -> (
            let spec = Spec.make root in
            Tg.run_pipeline spec
            |> (fun x ->
                match x with
                | Error msg -> (
                    Error_msg.print file_buffers msg;
                    1
                  )
                | Ok spec -> (
                    Spec.print_warnings file_buffers spec;
                    output_spec spec;
                    0
                  )
              )
          )
      )

let cmd =
  Cmd.(v (info "compile")
         Term.(
           const run
           $ force_arg
           $ skip_possible_cell_data_shape_analysis
           $ use_most_general_cell_data_shape
           $ skip_merge_branches
           $ style_arg
           $ input_file_arg
           $ output_file_arg))
