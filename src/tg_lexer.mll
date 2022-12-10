{
  open Lexing
  open Tg_parser
  open Syntax_error_exn

  let new_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with
        pos_bol = lexbuf.lex_curr_pos;
        pos_lnum = pos.pos_lnum + 1;
      }

  let get = Lexing.lexeme

  let loc lexbuf : Loc.t =
    let file_name = lexbuf.lex_start_p.pos_fname in
    let lnum = lexbuf.lex_start_p.pos_lnum in
    let cnum = lexbuf.lex_start_p.pos_cnum - lexbuf.lex_start_p.pos_bol in
    {file_name; lnum; cnum}

  let strip_front_end front_count end_count s =
    let last_index = String.length s - 1 in
    String.sub s front_count (last_index - end_count)
}

(* Characters *)
let white                = [' ' '\t']+
let newline              = '\r' | '\n' | "\r\n"

let not_star_paren       = ([^'*']*['*']['*']*[^ '*' ')'])*[^'*']*

let not_star         = [^'*']

let printable_char   = ['\032'-'\126']

let upper_alpha        = ['A'-'Z']
let lower_alpha        = ['a'-'z']
let numeric            = ['0'-'9']
let alpha              = (lower_alpha | upper_alpha)
let alpha_numeric_misc = (lower_alpha | upper_alpha | numeric | ['_'])
let other_name_symbol  = ['\'']
let nat                = numeric+

let name = alpha_numeric_misc (alpha_numeric_misc | other_name_symbol)*
let builtin = alpha_numeric_misc (alpha_numeric_misc | ['-'])*

rule read =
  parse
  (* Ignore spaces *)
  | white      { read lexbuf }
  | newline    { new_line lexbuf; read lexbuf }

  (* Keywords *)
  | '0'              { NULL_PROC }
  | "process"        { PROCESS }
  | "let"            { LET }
  | "in"             { IN }
  | "choice"         { CHOICE (loc lexbuf) }
  | "while"          { WHILE }
  | "break"          { BREAK (loc lexbuf) }
  | "continue"       { CONTINUE (loc lexbuf) }
  | "loop"           { LOOP }
  | "apred"          { APRED }
  | "pred"           { PRED }
  | "fun"            { FUN }
  | "module"         { MODULE }
  | "lemma"          { LEMMA }
  | "all-traces"     { ALL_TRACES }
  | "exists-trace"   { EXISTS_TRACE }
  | "All"            { ALL (loc lexbuf) }
  | "Ex"             { EX (loc lexbuf) }
  | "restriction"    { RESTRICTION }
  (* | "rule"           { RULE } *)
  | "not"            { NOT }
  | "as"             { AS }
  | "cas"            { CAS }
  (* | "global"         { GLOBAL }
  | "local"          { LOCAL } *)
  | "open"           { OPEN }
  | "insert"         { INSERT }
  (* | "entry_point"    { ENTRY_POINT } *)
  (* | "goto"           { GOTO } *)
  | "equation"       { EQUATION }
  | "builtins"       { BUILTINS }

  (* Typs *)
  (* | "cell"           { CELL }
  | "bitstring"      { BITSTRING }
  | "pub"            { PUB }
  | "prop"           { PROP }
  | "aprop"          { APROP }
  | "form"           { FORMULA }
  | "stmt"           { STATEMENT }
  | "temp"           { TEMPORAL }
  | "fresh"          { FRESH }
  | "thread_id"      { THREAD_ID }
  *)

  (* Symbols *)
  | ":="       { ASSIGN }
  | '('        { LEFT_PAREN }
  | ')'        { RIGHT_PAREN }
  | ','        { COMMA }
  | '['        { LEFT_SQR_BRACK }
  | ']'        { RIGHT_SQR_BRACK }
  | '{'        { LEFT_CUR_BRACK }
  | '}'        { RIGHT_CUR_BRACK }
  | '<'        { LEFT_ANGLE (loc lexbuf) }
  | '>'        { RIGHT_ANGLE }
  | ':'        { COLON }
  | ';'        { SEMICOLON }
  | '~'        { TILDE }
  | '/'        { SLASH }
  | '-'        { MINUS }
  | '\''       { SINGLE_QUOTE }
  | '.'        { DOT }
  | '#'        { HASH }
  | '@'        { AT }
  | '&'        { AND }
  | '|'        { OR }
  | "XOR"      { XOR }
  | '*'        { ASTERISK }
  | '+'        { PLUS }
  | '$'        { DOLLAR_SIGN }

  (* Operators *)
  | '!'        { EXCLAIM }
  | '^'        { EXP }
  | '='        { EQ }
  | "==>"      { IMP }

  | nat
    {
      NAT (int_of_string (get lexbuf))
    }

  | name
    {
      NAME { loc = Some (loc lexbuf); content = (get lexbuf) }
    }

  | builtin
    {
      BUILTIN { loc = Some (loc lexbuf); content = (get lexbuf) }
    }

  (* string literal *)
  | '"'        {
    read_string (loc lexbuf) (Buffer.create 17) lexbuf
    }

  | "/*"       { block_comment lexbuf }
  | "//"       { line_comment lexbuf }


  | _                    { raise (Syntax_error ("unexpected char: " ^ get lexbuf)) }
  | eof { EOF }

and block_comment =
  parse
  | newline        { new_line lexbuf; block_comment lexbuf }
  | "/*"           { block_comment lexbuf }
  | "*/"           { read lexbuf }
  | _              { block_comment lexbuf }
  | eof            { raise (Syntax_error ("unterminated comment")) }

and line_comment =
  parse
  | newline        { new_line lexbuf; read lexbuf }
  | _              { line_comment lexbuf }
  | eof            { read lexbuf }

and read_string loc buf =
  parse
  | '"'       {
    STRING {loc = Some loc; content = Buffer.contents buf} }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string loc buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string loc buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string loc buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string loc buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string loc buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string loc buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string loc buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string loc buf lexbuf
    }
  | _ { raise (Syntax_error ("illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (Syntax_error ("string is not terminated")) }
