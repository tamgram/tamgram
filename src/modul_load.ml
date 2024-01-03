open Result_syntax

let find_compatible_file ~required_by ~modul_name ~(available_files : string String_map.t) =
  let file = modul_name ^ Params.file_extension
             |> String.lowercase_ascii
  in
  match
    String_map.find_opt (String.lowercase_ascii file) available_files
  with
  | None ->
    Error
      (Error_msg.make_msg_only
         (Printf.sprintf "File compatible with %s missing, required by module %s" file required_by)
      )
  | Some x -> Ok x

let construct_modul_req_graph ~available_files (target : string)
  : (string list String_map.t, Error_msg.t) result =
  let rec aux
      (seen : (string * string) list)
      (modul_name : string)
    : (string list String_map.t, Error_msg.t) result =
    let* actual_file_path =
      find_compatible_file ~required_by:target ~modul_name ~available_files
    in
    let actual_file_name = Filename.basename actual_file_path in
    let* content = Misc_utils.read_file ~path:actual_file_path in
    let* m = Tg.parse_modul actual_file_name content in
    let seen = (modul_name, actual_file_name) :: seen in
    let reqs = Lexical_ctx_analysis.unsatisfied_modul_imports m
               |> List.map Loc.content
    in
    let g = String_map.(add modul_name reqs empty) in
    aux_list g seen reqs
  and aux_list
      (g : string list String_map.t)
      seen
      (modul_names : string list)
    : (string list String_map.t, Error_msg.t) result =
    match modul_names with
    | [] -> Ok g
    | modul_name :: ms -> (
        match List.assoc_opt modul_name seen with
        | Some file_name -> (
            Error
              (Error_msg.make_msg_only
                 (Fmt.str "Cannot compile due to dependency cycle:@,@[<v>   %a@]"
                    Fmt.(
                      list ~sep:(any "@,-> ")
                        (fun formatter (modul_name, file_name) ->
                           Fmt.pf formatter "module %s as file %s" modul_name file_name))
                    (List.rev ((modul_name, file_name) :: seen))
                 )
              )
          )
        | None -> (
            let* g' = aux seen modul_name in
            let g = String_map.union (fun _ reqs0 reqs1 ->
                Some (List.sort_uniq String.compare (reqs0 @ reqs1))
              )
                g g'
            in
            aux_list g seen ms
          )
      )
  in
  aux [] target

let total_order_of_moduls (g : string list String_map.t) ~root : string list =
  let ranking : int String_map.t ref = ref String_map.empty in
  let rec aux cur_rank root : unit =
    let rank =
      match String_map.find_opt root !ranking with
      | None -> cur_rank
      | Some x -> max x cur_rank
    in
    ranking := String_map.add root rank !ranking;
    let reqs = String_map.find root g in
    List.iter (fun x ->
        aux (rank+1) x
      ) reqs
  in
  aux 0 root;
  let flipped : string list Int_map.t =
    !ranking
    |> String_map.to_seq
    |> Seq.fold_left (fun (m : string list Int_map.t) (modul, ranking) ->
        let l = Option.value ~default:[] (Int_map.find_opt ranking m) in
        Int_map.add ranking (modul :: l) m
      )
      Int_map.empty
  in
  Int_map.to_seq flipped
  |> Seq.flat_map (fun (_, l) -> List.to_seq l)
  |> List.of_seq

let from_file (file : string) : (Tg_ast.modul, Error_msg.t) result =
  if not (Sys.file_exists file) then
    Error (Error_msg.make_msg_only (Fmt.str "File %s does not exist" file))
  else (
    let* available_files = Misc_utils.available_files_in_dir ~dir:(Filename.dirname file) in
    let root_modul_name =
      Filename.basename file
      |> CCString.chop_suffix ~suf:Params.file_extension
      |> Option.value ~default:file
      |> String.capitalize_ascii
    in
    let* req_graph = construct_modul_req_graph ~available_files root_modul_name in
    let import_list =
      match total_order_of_moduls req_graph ~root:root_modul_name with
      | [] -> failwith "Unexpected case"
      | x :: xs -> (
          assert (x = root_modul_name);
          List.rev xs
        )
    in
    let* content = Misc_utils.read_file ~path:file in
    let* m = Tg.parse_modul file content in
    let* imported_modul_decls = List.fold_left (fun l modul_name ->
        let open Tg_ast in
        let* l = l in
        let* file = find_compatible_file ~required_by:root_modul_name ~modul_name ~available_files in
        let* content = Misc_utils.read_file ~path:file in
        let+ m = Tg.parse_modul file content in
        (D_modul (Loc.untagged modul_name, m) :: l)
      ) (Ok []) import_list
    in
    let imported_modul_decls = List.rev imported_modul_decls in
    Ok (imported_modul_decls @ m)
  )
