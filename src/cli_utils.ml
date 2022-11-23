open Cmdliner

let force_arg = Arg.(value & flag & info [ "force"; "f" ])

let skip_possible_cell_data_shape_analysis =
  Arg.(value & flag & info [ "skip-possible-cell-data-shape-analysis" ])

let use_most_general_cell_data_shape =
  Arg.(value & flag & info [ "use-most-general-cell-data-shape" ])

let skip_merge_branches =
  Arg.(value & flag & info [ "skip-merge-branches" ])

let style_arg : Translate_style.t Term.t =
  Arg.(value &
       opt
         (enum
            [
              ("cell-by-cell", `Cell_by_cell);
              ("frame", `Frame);
              ("frame-minimal0", `Frame_minimal0);
              ("frame-minimal1", `Frame_minimal1);
              ("persistent0", `Persistent0);
              ("frame-minimal-backward0", `Frame_minimal_backward0);
              ("frame-minimal-hybrid0", `Frame_minimal_hybrid0);
            ])
         Params.default_translate_style
       & info [ "style" ])

let base_name_of_input_file input_file =
  input_file
  |> Filename.basename
  |> (fun s ->
      Option.value ~default:s
        (CCString.chop_suffix ~suf:Params.file_extension s)
    )

let process_output_file ~base_name ~output_file ~suffix =
  if output_file = "-" then
    None
  else
  if Sys.file_exists output_file
  && Sys.is_directory output_file then (
    Some (
      Filename.concat output_file
        (Printf.sprintf "%s%s%s" base_name Params.file_extension
           suffix
        ))
  ) else (
    Some output_file
  )

let cannot_write ~force_write ~output_file =
  match output_file with
  | None -> false
  | Some output_file ->
    (not force_write)
    && Sys.file_exists output_file
