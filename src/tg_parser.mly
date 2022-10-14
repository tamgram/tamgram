%{
  open Tg_ast
  open Syntax_error_exn

  let macro (arg_and_typs : Typ.term Binding.t list) ret_typ body : Tg_ast.macro =
    {
      arg_and_typs;
      ret_typ;
      body;
    }

  let bind name_str (bound_to : 'a) : 'a Binding.t =
    Binding.make name_str bound_to

  let one_of_typ_strs (l : (string * Typ.term) list) s : Typ.term =
    match List.assoc_opt s l with
    | None ->
        raise (Syntax_error ("unrecognized type: " ^ s))
    | Some typ ->
        typ

  let macro_ret_typ_strs = [
    ("bitstring", `Bitstring);
    ("fact", `Fact);
    ("afact", `Afact);
    ("formula", `Formula);
    ("pub", `Pub);
  ]

  let let_typ_strs = [
    ("fresh", `Fresh);
    ("cell", `Cell);
    ("temporal", `Temporal);
  ]
  @ macro_ret_typ_strs

  let parse_lemma_attr (s0 : string Loc.tagged) (s1 : string Loc.tagged option) : lemma_attr Loc.tagged =
    let s0' = Loc.content s0 in
    Loc.update_content
      (match s0' with
      | "sources" -> `Sources
      | "reuse" -> `Reuse
      | "use_induction" -> `Use_induction
      | _ ->
        match s1 with
        | None ->
          raise (Syntax_error (Printf.sprintf "unrecognized lemma attribute: %s" s0'))
        | Some s1' ->
          let s1' = Loc.content s1' in
          match s0' with
          | "hide_lemma" ->
            `Hide_lemma s1'
          | "heuristic" ->
            `Heuristic s1'
          | _ ->
            raise (Syntax_error (Printf.sprintf "unrecognized lemma attribute: %s=%s" s0' s1'))
      )
      s0
%}

(* Keywords *)
%token PROCESS
%token LET
%token IN
%token <Loc.t> CHOICE
%token PRED
%token APRED
%token FUN
%token MODULE
%token LEMMA
%token ALL_TRACES
%token EXISTS_TRACE
%token <Loc.t> ALL
%token <Loc.t> EX
%token RESTRICTION
(* %token RULE *)
%token NOT
%token AS
%token CAS
(* %token LOCAL
%token GLOBAL *)
%token OPEN
%token INSERT
%token ENTRY_POINT
%token GOTO
%token EQUATION
%token <string Loc.tagged> BUILTIN
%token BUILTINS

%token NULL_PROC

%token ASSIGN
%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token LEFT_SQR_BRACK
%token RIGHT_SQR_BRACK
%token LEFT_CUR_BRACK
%token RIGHT_CUR_BRACK
%token <Loc.t> LEFT_ANGLE
%token RIGHT_ANGLE
%token COLON
%token SEMICOLON
%token DOT
%token DOLLAR_SIGN
%token TILDE
%token SLASH
%token MINUS
%token SINGLE_QUOTE
%token HASH
%token AT
%token ASTERISK
%token PLUS

%token EXCLAIM

%nonassoc A

%token IFF
%token IMP
%token AND
%token OR

%left IFF
%left IMP
%left OR
%left AND

%token EQ
%token EXP
%token XOR

%nonassoc AS
%left EQ
%left PLUS
%left EXP
%left XOR

%nonassoc NOT

%token <int> NAT
%token <string Loc.tagged> NAME
%token <string Loc.tagged> STRING

%token EOF

%start <Tg_ast.modul> parse

%%

parse:
  | root = modul; EOF
    { root }

(* From gallium.inria.fr/blog/lr-lists
   "Left-recursive versus right-recursive lists in LR parsers"
   written by Francois Pottier, 2015 Jan 21
 *)

reverse_separated_nonempty_llist(sep, X):
  | x = X
    { [ x ] }
  | xs = reverse_separated_nonempty_llist(sep, X); sep; x = X
    { x :: xs }

%inline reverse_separated_llist(sep, X):
  | { [] }
  | xs = reverse_separated_nonempty_llist(sep, X)
    { xs }

%inline separated_llist(sep, X):
  | xs = reverse_separated_llist(sep, X)
    { List.rev xs }

%inline flexible_list(sep, X):
  | xs = separated_llist(sep, X); sep?
    { xs }

modul:
  | decls = list(decl)
    { decls }

path:
  | path = separated_nonempty_list(DOT, NAME) { path }

macro_ret_typ:
  | s = NAME
  {
    one_of_typ_strs macro_ret_typ_strs (Loc.content s)
  }

let_typ:
  | s = NAME
  {
    one_of_typ_strs let_typ_strs (Loc.content s)
  }

name_and_typ:
  | name = NAME; COLON; typ = let_typ
    { bind name typ }
  | name = NAME
    { bind name `Bitstring }

cell_or_name_and_typ:
  | SINGLE_QUOTE; name = NAME
    { bind name `Cell }
  | name = NAME; COLON; typ = let_typ
    { bind name typ }
  | name = NAME
    { bind name `Bitstring }

lvar:
  | name = NAME
    { (name, `Bitstring) }
  | HASH; name = NAME
    { (name, `Temporal) }

lvars:
  | l = nonempty_list(lvar)
    { List.map (fun (name, x) -> bind name x) l
    }

cell:
  | SINGLE_QUOTE; name = NAME
    { name }

linear_app:
  | f = path; LEFT_PAREN; args = flexible_list(COMMA, term); RIGHT_PAREN;
    LEFT_SQR_BRACK; PLUS; RIGHT_SQR_BRACK;
    { T_app (f, `Local 0, args, Some `Plus) }
  | f = path; LEFT_PAREN; args = flexible_list(COMMA, term); RIGHT_PAREN;
    LEFT_SQR_BRACK; MINUS; RIGHT_SQR_BRACK;
    { T_app (f, `Local 0, args, Some `Minus) }
  | f = path; LEFT_PAREN; args = flexible_list(COMMA, term); RIGHT_PAREN;
    { T_app (f, `Local 0, args, None) }

fact_common:
  | EXCLAIM; x = linear_app;
    { T_unary_op (`Persist, x) }
  | x = linear_app;
    { x }

lfact:
  | x = fact_common
    { x }
  | x = cell; CAS; y = term;
    { T_cell_pat_match (x, y) }

rfact:
  | x = fact_common
    { x }
  | x = cell; ASSIGN; y = term
    { T_cell_assign (x, y) }

term:
  | name = STRING { T_value (Loc.map (fun s -> `Str s) name) }
  | DOLLAR_SIGN; name = NAME { T_symbol (name, `Pub) }
  | name = cell { T_symbol (name, `Cell) }
  | TILDE; name = NAME { T_var ([name], `Local 0, Some `Fresh) }
  | name = NAME; COLON; typ = let_typ
    { match typ with
      | `Pub -> T_symbol (name, `Pub)
      | `Cell -> T_symbol (name, `Cell)
      | _ -> T_var ([name], `Local 0, Some typ)
    }
  | path = path {
    match path with
    | [] -> failwith "Unexpected case"
    | [x] -> (
      match Loc.content x with
      | "T" -> T_value (Loc.update_content `T x)
      | "F" -> T_value (Loc.update_content `F x)
      | _ ->
        T_var (path, `Local 0, None)
    )
    | _ ->
      T_var (path, `Local 0, None)
  }
  | LEFT_PAREN; term = term; RIGHT_PAREN
    { term }
  | loc = LEFT_ANGLE; terms = flexible_list(COMMA, term); RIGHT_ANGLE
    { T_tuple (Some loc, terms) }
  | x = linear_app
    { x }
  | NOT; x = term;
    { T_unary_op (`Not, x) }
  | x = term; AS; y = NAME;
    { T_name_as (x, y) }
  | x = term; EQ; y = term
    { T_binary_op (`Eq, x, y) }
  | x = term; EXP; y = term
    { T_binary_op (`Exp, x, y) }
  | x = term; PLUS; y = term
    { T_binary_op (`Plus, x, y) }
  | LET; name = NAME; EQ; bound_to = term; IN; next = term %prec A
    { T_let {binding = bind name bound_to; next} }
  | LET; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; EQ; body = term; IN; next = term %prec A
    { T_let_macro {binding = bind name (macro arg_and_typs `Bitstring body); next} }
  | LET; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; COLON; ret_typ = macro_ret_typ; EQ; body = term; IN; next = term %prec A
    { T_let_macro {binding = bind name (macro arg_and_typs ret_typ body); next} }
  | fact = fact_common; AT; option(HASH); t = NAME
    { T_action { fact; temporal = (t, `Local 0)} }
  | f1 = term; IFF; f2 = term
    { T_binary_op (`Iff, f1, f2) }
  | f1 = term; IMP; f2 = term
    { T_binary_op (`Imp, f1, f2) }
  | f1 = term; OR; f2 = term
    { T_binary_op (`Or, f1, f2) }
  | f1 = term; AND; f2 = term
    { T_binary_op (`And, f1, f2) }
  | f1 = term; XOR; f2 = term
    { T_binary_op (`Xor, f1, f2) }
  | a = NAME; LEFT_ANGLE; b = NAME
    { T_temporal_a_lt_b { a = (a, `Local 0); b = (b, `Local 0) } }
  | HASH; a = NAME; LEFT_ANGLE; HASH; b = NAME
    { T_temporal_a_lt_b { a = (a, `Local 0); b = (b, `Local 0) } }
  | HASH; a = NAME; EQ; HASH; b = NAME
    { T_temporal_eq { a = (a, `Local 0); b = (b, `Local 0) } }
  | loc = ALL; quant = lvars; DOT; formula = term %prec A
    { T_quantified {
        loc = Some loc;
        quantifier = `All;
        quant;
        formula;
      }
    }
  | loc = EX; quant = lvars; DOT; formula = term %prec A
    { T_quantified {
        loc = Some loc;
        quantifier = `Ex;
        quant;
        formula;
      }
    }

lemma_attr:
  | s = NAME
    { parse_lemma_attr s None }
  | s0 = NAME; EQ; s1 = NAME
    { parse_lemma_attr s0 (Some s1) }

lemma_attrs:
  | l = flexible_list(COMMA, lemma_attr)
    { l }

builtin:
  | x = NAME
    { x }
  | x = BUILTIN
    { x }

decl:
  | BUILTINS; ASSIGN; l = separated_nonempty_list(COMMA, builtin)
    { D_builtins l }
  | FUN; name = NAME; SLASH; arity = NAT
    { D_fun (bind name arity) }
  | FUN; name = NAME; SLASH; NULL_PROC
    { D_fun (bind name 0) }
  | PRED; name = NAME; SLASH; arity = NAT
    { D_pred (bind name { arity; options = [] }) }
  | PRED; name = NAME; SLASH; NULL_PROC
    { D_pred (bind name { arity = 0; options = [] }) }
  | PRED; EXCLAIM; name = NAME; SLASH; arity = NAT
    { D_ppred (bind name { arity; options = [] }) }
  | PRED; EXCLAIM; name = NAME; SLASH; NULL_PROC
    { D_ppred (bind name { arity = 0; options = [] }) }
  (* | PRED; name = NAME; SLASH; arity = NAT; LEFT_SQR_BRACK;
    options = flexible_list(COMMA, pred_option);
    RIGHT_SQR_BRACK
    { D_pred (bind name { arity; options }) } *)
  | APRED; name = NAME; SLASH; arity = NAT
    { D_apred (bind name arity) }
  | APRED; name = NAME; SLASH; NULL_PROC
    { D_apred (bind name 0) }
  | APRED; EXCLAIM; name = NAME; SLASH; arity = NAT
    { D_papred (bind name arity) }
  | APRED; EXCLAIM; name = NAME; SLASH; NULL_PROC
    { D_papred (bind name 0) }
  | LET; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; COLON; ret_typ = macro_ret_typ; EQ; body = term
    { D_macro { binding = bind name (macro arg_and_typs ret_typ body)} }
  | FUN; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; EQ; body = term
    { D_macro { binding = bind name (macro arg_and_typs `Bitstring body)} }
  | PRED; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; EQ; body = term
    { D_macro { binding = bind name (macro arg_and_typs `Fact body) } }
  | APRED; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; EQ; body = term
    { D_macro { binding = bind name (macro arg_and_typs `Afact body) } }
  | LET; name = NAME; EQ; bound_to = term
    { D_let { binding = bind name bound_to } }
  | PROCESS; name = NAME; EQ; body = proc
    { D_process { binding = bind name body } }
  | PROCESS; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, cell_or_name_and_typ); RIGHT_PAREN; EQ; body = proc
    { D_process_macro (bind name { arg_and_typs; body }) }
  | MODULE; name = NAME; EQ; LEFT_CUR_BRACK; m = modul; RIGHT_CUR_BRACK
    { D_modul (name, m) }
  | OPEN; path = path
    { D_open path }
  | INSERT; path = path
    { D_insert path }
  | EQUATION; name = NAME; EQ; formula = term
    { D_equation { binding = bind name formula } }
  | LEMMA; name = NAME; EQ; formula = term
    { D_lemma { binding = bind name { trace_quantifier = `All_traces; formula; attrs = [] } } }
  | LEMMA; name = NAME; EQ; ALL_TRACES; formula = term
    { D_lemma { binding = bind name { trace_quantifier = `All_traces; formula; attrs = [] } } }
  | LEMMA; name = NAME; EQ; EXISTS_TRACE; formula = term
    { D_lemma { binding = bind name { trace_quantifier = `Exists_trace; formula; attrs = [] } } }
  | LEMMA; name = NAME; LEFT_SQR_BRACK; attrs = lemma_attrs; RIGHT_SQR_BRACK;
    EQ; formula = term;
    { D_lemma { binding = bind name { trace_quantifier = `All_traces; formula; attrs } } }
  | LEMMA; name = NAME; LEFT_SQR_BRACK; attrs = lemma_attrs; RIGHT_SQR_BRACK;
    EQ; ALL_TRACES; formula = term;
    { D_lemma { binding = bind name { trace_quantifier = `All_traces; formula; attrs } } }
  | LEMMA; name = NAME; LEFT_SQR_BRACK; attrs = lemma_attrs; RIGHT_SQR_BRACK;
    EQ; EXISTS_TRACE; formula = term;
    { D_lemma { binding = bind name { trace_quantifier = `Exists_trace; formula; attrs } } }
  | RESTRICTION; name = NAME; EQ; formula = term
    { D_restriction { binding = bind name formula } }
  (* | RULE; name = NAME; EQ; rule = rule
    { D_rule { binding = bind name rule } } *)

rule_let_binding:
  | LET; name = NAME; EQ; bound_to = term; IN
    { R_let (bind name bound_to) }
  | LET; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; EQ; body = term; IN
    { R_let_macro { binding = bind name (macro arg_and_typs `Bitstring body)} }
  | LET; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; COLON; ret_typ = macro_ret_typ; EQ; body = term; IN
    { R_let_macro { binding = bind name (macro arg_and_typs ret_typ body)} }

double_minus:
  | MINUS; MINUS { () }

rule:
  | LEFT_SQR_BRACK; l = flexible_list(COMMA, lfact); RIGHT_SQR_BRACK;
    double_minus;
    bindings_before_a = list(rule_let_binding);
    LEFT_SQR_BRACK; a = flexible_list(COMMA, fact_common); RIGHT_SQR_BRACK;
    MINUS; option(MINUS); RIGHT_ANGLE;
    bindings_before_r = list(rule_let_binding);
    LEFT_SQR_BRACK; r = flexible_list(COMMA, rfact); RIGHT_SQR_BRACK;
    {
      {l; vars_in_l = []; bindings_before_a; a; bindings_before_r; r}
    }
  | LEFT_SQR_BRACK; l = flexible_list(COMMA, lfact); RIGHT_SQR_BRACK;
    MINUS; option(MINUS); RIGHT_ANGLE;
    bindings_before_r = list(rule_let_binding);
    LEFT_SQR_BRACK; r = flexible_list(COMMA, rfact); RIGHT_SQR_BRACK;
    {
      {l; vars_in_l = []; bindings_before_a = []; a = []; bindings_before_r; r}
    }

proc:
  | NULL_PROC                                     { P_null }
  | LET; name = NAME; EQ; bound_to = term; IN; next = proc
    { P_let { binding = bind name bound_to; next} }
  | LET; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; EQ; body = term; IN; next = proc
    { P_let_macro { binding = bind name (macro arg_and_typs `Bitstring body); next} }
  | LET; name = NAME; LEFT_PAREN; arg_and_typs = flexible_list(COMMA, name_and_typ); RIGHT_PAREN; COLON; ret_typ = macro_ret_typ; EQ; body = term; IN; next = proc
    { P_let_macro { binding = bind name (macro arg_and_typs ret_typ body); next} }
  | f = path; LEFT_PAREN; args = flexible_list(COMMA, term); RIGHT_PAREN; SEMICOLON; next = proc
    { P_app (f, `Local 0, args, next) }
  | f = path; LEFT_PAREN; args = flexible_list(COMMA, term); RIGHT_PAREN
    { P_app (f, `Local 0, args, P_null) }
  | tag = STRING; COLON; rule = rule; SEMICOLON; next = proc
    { P_line { tag = Some tag; rule; next } }
  | rule = rule; SEMICOLON; next = proc
    { P_line { tag = None; rule; next } }
  | tag = STRING; COLON; rule = rule
    { P_line { tag = Some tag; rule; next = P_null } }
  | rule = rule
    { P_line { tag = None; rule; next = P_null } }
  | loc = CHOICE; LEFT_CUR_BRACK; branches = flexible_list(SEMICOLON, proc_in_block); RIGHT_CUR_BRACK; SEMICOLON; next = proc
    { P_branch (Some loc, branches, next) }
  | loc = CHOICE; LEFT_CUR_BRACK; branches = flexible_list(SEMICOLON, proc_in_block); RIGHT_CUR_BRACK
    { P_branch (Some loc, branches, P_null) }
  | proc = proc_in_block; SEMICOLON; next = proc
    { P_scoped (proc, next) }
  | proc = proc_in_block
    { P_scoped (proc, P_null) }
  | ENTRY_POINT; name = STRING; SEMICOLON; next = proc
    { P_entry_point { name; next } }
  | ENTRY_POINT; name = STRING;
    { P_entry_point { name; next = P_null } }
  | GOTO; dest = STRING;
    { P_goto { dest; } }

proc_in_block:
  | LEFT_CUR_BRACK; proc = proc; RIGHT_CUR_BRACK
    { proc }

