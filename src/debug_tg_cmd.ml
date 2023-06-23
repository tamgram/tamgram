open Cmdliner
open Cli_utils

let show_root_arg = Arg.(value & flag & info [ "show-root" ])

let show_graph_arg = Arg.(value & flag & info [ "show-graph" ])

let debug_name_arg = Arg.(value & flag & info [ "name" ])

let debug_node_arg = Arg.(value & flag & info [ "node" ])

(* let list_stages_arg = Arg.(value & flag & info [ "list-stages" ]) *)

let stop_before_stage_arg =
  let doc =
    {|Stop before stage $(docv) of processing.
|}
    ^ Tg.string_of_default_pipeline
  in
  let open Arg in
  value
  & opt int (List.length Tg.default_pipeline)
  & info [ "stop-before-stage" ] ~docv:"N" ~doc

let input_file_arg =
  let doc = "Input Tamgram file" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"TG_SRC" ~doc)

let output_file_arg =
  let doc = "Output debug purpose Tamgram IR file" in
  Arg.(required & pos 1 (some string) None & info [] ~docv:"DEST" ~doc)

let run
    (force_write : bool)
    (skip_possible_cell_data_shape_analysis : bool)
    (use_most_general_cell_data_shape : bool)
    (skip_merge_branches : bool)
    (style : Translate_style.t)
    (show_root : bool)
    (show_graph : bool)
    (debug_name : bool)
    (debug_node : bool)
    (stop_before_stage : int)
    (input_file : string)
    (output_file : string)
  : int =
  Params.analyze_possible_cell_data_shapes := not skip_possible_cell_data_shape_analysis;
  Params.use_most_general_cell_data_shape := use_most_general_cell_data_shape;
  Params.merge_branches := not skip_merge_branches;
  Params.translate_style := style;
  Params.debug_name := debug_name;
  Params.debug_node := debug_node;
  let show_root, show_graph =
    if not show_root && not show_graph then
      true, true
    else
      show_root, show_graph
  in
  let base_name = base_name_of_input_file input_file in
  let output_file =
    process_output_file ~base_name ~output_file ~suffix:".debug"
  in
  let output_spec (spec : Spec.t) : unit =
    let f_out formatter =
      Fmt.pf formatter "%a" (Printers.pp_spec ~show_root ~show_graph) spec
    in
    match output_file with
    | None -> (
        f_out Fmt.stdout
      )
    | Some output_file -> (
        CCIO.(with_out ~flags:[Open_binary; Open_creat; Open_trunc]
                output_file
                (fun oc ->
                   f_out (Format.formatter_of_out_channel oc)
                ))
      )
  in
  if cannot_write ~force_write ~output_file
  then (
    Printf.printf "Output file already exists: %s\n" (Option.get output_file);
    1
  ) else (
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
            Tg.run_pipeline ~stop_before_stage spec
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
  )

let cmd =
  Cmd.(v (info "debug-tg")
         Term.(const run
               $ force_arg
               $ skip_possible_cell_data_shape_analysis
               $ use_most_general_cell_data_shape
               $ skip_merge_branches
               $ style_arg
               $ show_root_arg
               $ show_graph_arg
               $ debug_name_arg
               $ debug_node_arg
               $ stop_before_stage_arg
               $ input_file_arg
               $ output_file_arg))
