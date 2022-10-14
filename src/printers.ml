let pp_name (formatter : Format.formatter) (x : Name.t) : unit =
  match x with
  | `Global x -> Fmt.pf formatter "bound at global %d" x
  | `Local x -> Fmt.pf formatter "bound at local %d" x

let pp_path (formatter : Format.formatter) (p : Path.t) : unit =
  Fmt.pf formatter "%a"
    Fmt.(list ~sep:(any ".") string)
    (List.map Loc.content p)

let pp_name_if_debug formatter name =
  if !Params.debug_name then Fmt.pf formatter "[%a]" pp_name name

let pp_name_index_if_debug formatter index =
  if !Params.debug_name then Fmt.pf formatter "[index:%d]" index

let pp_typ (formatter : Format.formatter) (typ : Typ.term) : unit =
  let rec aux formatter term =
    match term with
    | `Cell -> Fmt.pf formatter "cell"
    | `Temporal -> Fmt.pf formatter "temporal"
    | `Bitstring -> Fmt.pf formatter "bitstring"
    | `Pub -> Fmt.pf formatter "pub"
    | `Fresh -> Fmt.pf formatter "fresh"
    | `Fact -> Fmt.pf formatter "fact"
    | `Pfact -> Fmt.pf formatter "pfact"
    | `Afact -> Fmt.pf formatter "afact"
    | `Pafact -> Fmt.pf formatter "pafact"
    | `Formula -> Fmt.pf formatter "form"
    | `Pat_match -> Fmt.pf formatter "patmatch"
    | `Statement -> Fmt.pf formatter "stmt"
    | `Fun (args, ret) -> (
        match args with
        | [] ->
          Fmt.pf formatter "() -> %a" aux ret
        | _ ->
          Fmt.pf formatter "%a -> %a" Fmt.(list ~sep:(any " * ") aux) args aux ret
      )
    | `Process -> Fmt.pf formatter "process"
    | `Subroutine (arg_count, ret_cell_count) -> (
        let arg_typs =
          CCList.(0 --^ arg_count) |> List.map (fun _ -> `Bitstring)
        in
        let ret_typ =
          CCList.(0 --^ ret_cell_count) |> List.map (fun _ -> `Bitstring)
        in
        match ret_typ with
        | [] ->
          Fmt.pf formatter "subroutine %a -> ()"
            Fmt.(list ~sep:(any " * ") aux)
            arg_typs
        | ret_typ ->
          Fmt.pf formatter "subroutine %a -> %a"
            Fmt.(list ~sep:(any " * ") aux)
            arg_typs
            Fmt.(list ~sep:(any " * ") aux)
            ret_typ)
    | `Equation -> Fmt.pf formatter "equation"
    | `Lemma -> Fmt.pf formatter "lemma"
    | `Restriction -> Fmt.pf formatter "restriction"
    | `Rule -> Fmt.pf formatter "rule"
  in
  aux formatter typ

let prefix_of_typ (typ : Typ.term) : string =
  match typ with
  | `Cell -> "'"
  | `Temporal -> "#"
  | `Pub -> "$"
  | `Fresh -> "~"
  | _ -> ""

let pp_name_and_typ ?(only_prefix = false) (formatter : Format.formatter)
    (binding : Typ.term Binding.t) : unit =
  let prefix = prefix_of_typ (Binding.get binding) in
  if only_prefix then
    Fmt.pf formatter "%s%s%a" prefix
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding)
  else
    Fmt.pf formatter "%s%s%a : %a" prefix
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) pp_typ (Binding.get binding)

let pp_fact_anno formatter (x : Tg_ast.fact_anno option) : unit =
  match x with
  | None -> ()
  | Some `Plus -> Fmt.pf formatter "[+]"
  | Some `Minus -> Fmt.pf formatter "[-]"

let pp_binary_op formatter (x : Tg_ast.binary_op) : unit =
  match x with
  | `Exp -> Fmt.pf formatter "^"
  | `Eq -> Fmt.pf formatter "="
  | `Iff -> Fmt.pf formatter "<=>"
  | `Imp -> Fmt.pf formatter "==>"
  | `Or -> Fmt.pf formatter "|"
  | `And -> Fmt.pf formatter "&"
  | `Plus -> Fmt.pf formatter "+"
  | `Xor -> Fmt.pf formatter "XOR"

let pp_term (formatter : Format.formatter) (x : Tg_ast.term) : unit =
  let open Tg_ast in
  let rec aux formatter x =
    match x with
    | T_value x -> (
        match Loc.content x with
        | `Str s -> Fmt.pf formatter "\"%s\"" s
        | `T -> Fmt.pf formatter "T"
        | `F -> Fmt.pf formatter "F")
    | T_symbol (name, symbol_sort) ->
      Fmt.pf formatter "%s%s"
        (match symbol_sort with `Cell -> "'" | `Pub -> "$")
        (Loc.content name)
    | T_name_as (x, name) ->
      Fmt.pf formatter "(%a as %s)" aux x (Loc.content name)
    | T_var (path, name, typ) -> (
        match typ with
        | Some typ -> (
            match typ with
            | `Pub | `Fresh | `Temporal -> (
                match path with
                | [] -> failwith "Unexpected case"
                | [ _ ] ->
                  Fmt.pf formatter "%s%a%a" (prefix_of_typ typ) pp_path path
                    pp_name_if_debug name
                | _ ->
                  Fmt.pf formatter "%a%a : %a" pp_path path pp_name_if_debug
                    name pp_typ typ)
            | _ ->
              Fmt.pf formatter "%a%a : %a" pp_path path pp_name_if_debug name
                pp_typ typ)
        | None -> Fmt.pf formatter "%a%a" pp_path path pp_name_if_debug name)
    | T_app (path, name, args, anno) ->
      Fmt.pf formatter "%a%a(@[<h>%a@])%a" pp_path path pp_name_if_debug name
        Fmt.(list ~sep:comma aux)
        args
        pp_fact_anno
        anno
    | T_unary_op (op, x) ->
      Fmt.pf formatter "%s%a"
        (match op with `Persist -> "!" | `Not -> "not")
        aux x
    | T_binary_op (op, x, y) ->
      Fmt.pf formatter "((%a) %a (%a))" aux x
        pp_binary_op op
        aux y
    | T_cell_pat_match (x, y) ->
      Fmt.pf formatter "('%s cas %a)" (Loc.content x) aux y
    | T_cell_assign (x, y) ->
      Fmt.pf formatter "('%s := %a)" (Loc.content x) aux y
    | T_tuple (_loc, l) -> Fmt.pf formatter "@[<h><%a>@]" Fmt.(list ~sep:comma aux) l
    | T_let { binding; next } ->
      Fmt.pf formatter "let %s%a = %a in@,%a"
        (Binding.name_str_untagged binding)
        pp_name_if_debug (Binding.name binding) aux (Binding.get binding) aux
        next
    | T_let_macro { binding; next } ->
      let { arg_and_typs; ret_typ; body } = Binding.get binding in
      Fmt.pf formatter "let %s%a(@[<h>%a@]) : %a =@,  @[<v>%a@]@,in@,%a"
        (Binding.name_str_untagged binding)
        pp_name_if_debug (Binding.name binding)
        Fmt.(list ~sep:comma pp_name_and_typ)
        arg_and_typs pp_typ ret_typ aux body aux next
    | T_action { fact; temporal } ->
      Fmt.pf formatter "%a @@ %a%a" aux fact aux
        (T_var ([ fst temporal ], snd temporal, Some `Temporal))
        pp_name_if_debug (snd temporal)
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
        Fmt.(list ~sep:(any " ") (pp_name_and_typ ~only_prefix:true))
        quant aux formula
  in
  aux formatter x

let pp_fact (formatter : Format.formatter) (fact : Tg_ast.fact) : unit =
  let open Tg_ast in
  Fmt.pf formatter "%s%s(%a)"
    (match fact.sort with `Linear -> "" | `Persist -> "!")
    (Loc.content fact.name)
    Fmt.(list ~sep:comma pp_term)
    fact.args

let pp_binding pp (formatter : Format.formatter) (binding : 'a Binding.t) : unit
  =
  Fmt.pf formatter "let %s%a = %a in"
    (Binding.name_str_untagged binding)
    pp_name_if_debug (Binding.name binding) pp (Binding.get binding)

let pp_rule_binding formatter (binding : Tg_ast.rule_binding) =
  let open Tg_ast in
  match binding with
  | R_let binding -> pp_binding pp_term formatter binding
  | R_let_macro { binding; _ } ->
    let { arg_and_typs; ret_typ; body } = Binding.get binding in
    Fmt.pf formatter "let %s%a(@[<h>%a@]) : %a =@,  @[<v>%a@]@,in@,"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding)
      Fmt.(list ~sep:comma pp_name_and_typ)
      arg_and_typs pp_typ ret_typ pp_term body

let pp_rule_bindings formatter bindings =
  match bindings with
  | [] -> ()
  | l ->
    Fmt.pf formatter "@,  @[<v>%a@]@,"
      Fmt.(list ~sep:(any "@,") pp_rule_binding)
      l

let pp_rule (formatter : Format.formatter) (rule : Tg_ast.rule) : unit =
  let open Tg_ast in
  let { l; bindings_before_a; a; bindings_before_r; r } = rule in
  let l_count = List.length l in
  let a_count = List.length a in
  let r_count = List.length r in
  if l_count <= 1 && a_count <= 1 && r_count <= 1 then
    Fmt.pf formatter "[%a]--%a[%a]->%a[%a]"
      Fmt.(list ~sep:comma pp_term)
      l pp_rule_bindings bindings_before_a
      Fmt.(list ~sep:comma pp_term)
      a pp_rule_bindings bindings_before_r
      Fmt.(list ~sep:comma pp_term)
      r
  else
    Fmt.pf formatter
      "@[<v>  @[<v>[ %a@ ]@]@,--%a@[<v>[ %a@ ]->@]%a@,  @[<v>[ %a@ ]@]@]"
      Fmt.(list ~sep:(any "@,, ") pp_term)
      l pp_rule_bindings bindings_before_a
      Fmt.(list ~sep:(any "@,, ") pp_term)
      a pp_rule_bindings bindings_before_r
      Fmt.(list ~sep:(any "@,, ") pp_term)
      r

let pp_proc (formatter : Format.formatter) (p : Tg_ast.proc) : unit =
  let open Tg_ast in
  let rec aux formatter p =
    match p with
    | P_null -> Fmt.pf formatter "0"
    | P_let { binding; next } ->
      Fmt.pf formatter "@[<hov>let %s%a =@ %a@ in@]@,%a"
        (Binding.name_str_untagged binding)
        pp_name_if_debug (Binding.name binding) pp_term (Binding.get binding)
        aux next
    | P_let_macro { binding; next } ->
      let { arg_and_typs; ret_typ; body } = Binding.get binding in
      Fmt.pf formatter "let %s%a(@[<h>%a@]) : %a =@,  @[<v>%a@]@,in@,%a"
        (Binding.name_str_untagged binding)
        pp_name_if_debug (Binding.name binding)
        Fmt.(list ~sep:comma pp_name_and_typ)
        arg_and_typs pp_typ ret_typ pp_term body aux next
    | P_app (path, name, args, next) ->
      Fmt.pf formatter "%a%a(@[<h>%a@]);@,%a" pp_path path pp_name_if_debug name
        Fmt.(list ~sep:comma pp_term)
        args
        aux next
    | P_line { tag; rule; next } ->
      (match tag with
       | None -> ()
       | Some s ->
         Fmt.pf formatter "%s:@,"
           (Loc.content s)
      );
      Fmt.pf formatter "%a;@,%a"
        pp_rule rule
        aux next
    | P_branch (_loc, branches, next) ->
      Fmt.pf formatter "choice {@,  @[<v>%a@]@,};@,%a"
        Fmt.(list ~sep:semi aux_in_block)
        branches aux next
    | P_scoped (proc, next) ->
      Fmt.pf formatter "%a;@,%a" aux_in_block
        proc aux next
    | P_entry_point { name; next } ->
      Fmt.pf formatter "entry_point \"%s\";@,%a"
        (Loc.content name) aux next
    | P_goto { dest } ->
      Fmt.pf formatter "goto \"%s\""
        (Loc.content dest)
  and aux_in_block formatter p = Fmt.pf formatter "{@,  @[<v>%a@]@,}" aux p in
  aux formatter p

let pp_lemma_attr (formatter : Format.formatter) (attr : Tg_ast.lemma_attr) : unit =
  match attr with
  | `Sources -> Fmt.pf formatter "sources"
  | `Reuse -> Fmt.pf formatter "reuse"
  | `Use_induction -> Fmt.pf formatter "use_induction"
  | `Hide_lemma s -> Fmt.pf formatter "hide_lemma=%s" s
  | `Heuristic s -> Fmt.pf formatter "heuristic=%s" s

let rec pp_decl (formatter : Format.formatter) (decl : Tg_ast.decl) : unit =
  let open Tg_ast in
  match decl with
  | D_builtins l ->
    Fmt.pf formatter "builtins := %a"
      Fmt.(list ~sep:comma string) (List.map Loc.content l)
  | D_process { binding; _ } ->
    Fmt.pf formatter "process %s%a =@,  @[<v>%a@]"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) pp_proc (Binding.get binding)
  | D_process_macro binding ->
    let macro = Binding.get binding in
    Fmt.pf formatter "process %s%a(@[<h>%a@]) =@,  @[<v>%a@]"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding)
      Fmt.(list ~sep:comma pp_name_and_typ)
      macro.arg_and_typs
      pp_proc macro.body
  | D_let { binding } ->
    Fmt.pf formatter "let %s%a = %a"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) pp_term (Binding.get binding)
  | D_fun binding ->
    Fmt.pf formatter "fun %s%a/%d"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) (Binding.get binding)
  | D_pred binding ->
    let { arity; options = _ } = Binding.get binding in
    Fmt.pf formatter "pred %s%a/%d"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) arity
  | D_ppred binding ->
    let { arity; options = _ } = Binding.get binding in
    Fmt.pf formatter "!pred %s%a/%d"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) arity
  | D_apred binding ->
    Fmt.pf formatter "apred %s%a/%d"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) (Binding.get binding)
  | D_papred binding ->
    Fmt.pf formatter "!apred %s%a/%d"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) (Binding.get binding)
  | D_macro { binding } ->
    let { arg_and_typs; ret_typ; body } = Binding.get binding in
    Fmt.pf formatter "fun %s%a(@[<h>%a@]) : %a =@,  @[<v>%a@]"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding)
      Fmt.(list ~sep:comma pp_name_and_typ)
      arg_and_typs pp_typ ret_typ pp_term body
  | D_lemma { binding } ->
    let lemma = Binding.get binding in
    Fmt.pf formatter "lemma %s%a [%a] =@,  @[<v>%s@,%a@]"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding)
      Fmt.(list ~sep:comma pp_lemma_attr) (List.map Loc.content lemma.attrs)
      (match lemma.trace_quantifier with
       | `All_traces -> "all-traces"
       | `Exists_trace -> "exists-trace")
      pp_term lemma.formula
  | D_equation { binding } ->
    let formula = Binding.get binding in
    Fmt.pf formatter "equation %s%a =@,  @[<v>%a@]"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) pp_term formula
  | D_restriction { binding } ->
    let formula = Binding.get binding in
    Fmt.pf formatter "restriction %s%a =@,  @[<v>%a@]"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) pp_term formula
  | D_rule { binding } ->
    Fmt.pf formatter "rule %s%a =@,  @[%a@]"
      (Binding.name_str_untagged binding)
      pp_name_if_debug (Binding.name binding) pp_rule (Binding.get binding)
  | D_modul (name, decls) ->
    Fmt.pf formatter "module %s = {@,  %a@,}" (Loc.content name) pp_modul decls
  | D_open path -> Fmt.pf formatter "open %a" pp_path path
  | D_insert path -> Fmt.pf formatter "insert %a" pp_path path

and pp_modul (formatter : Format.formatter) (modul : Tg_ast.modul) : unit =
  Fmt.pf formatter "@[<v>%a@]" Fmt.(list ~sep:(any "@,@,") pp_decl) modul

let pp_spec_root formatter (spec : Spec.t) =
  Fmt.pf formatter "%a@." pp_modul spec.root

let pp_spec_proc_graphs formatter (spec : Spec.t) =
  Seq.iter (fun (_proc_name, g) ->
      Seq.iter (fun (k, ru) ->
          Fmt.pf formatter "@[<v>k: %d@," k;
          Fmt.pf formatter "  @[<v>";
          Fmt.pf formatter "pred: [@[<h>%a@]]@," Fmt.(seq ~sep:comma int)
            (Int_set.to_seq (Graph.pred k g));
          Fmt.pf formatter "succ: [@[<h>%a@]]@," Fmt.(seq ~sep:comma int)
            (Int_set.to_seq (Graph.succ k g));
          Fmt.pf formatter "rule:@,";
          Fmt.pf formatter "  @[%a@]" pp_rule ru;
          Fmt.pf formatter "@]@,@,@]";
        )
        (Graph.vertex_seq g)
    )
    (Name_map.to_seq spec.proc_graphs)

let pp_spec ~show_root ~show_graph formatter (spec : Spec.t) =
  if show_root then (
    Fmt.pf formatter "%a" pp_spec_root spec
  );
  if show_root && show_graph then (
    Fmt.pf formatter "@[<v>@,===@,@]"
  );
  if show_graph then (
    Fmt.pf formatter "%a" pp_spec_proc_graphs spec
  )
