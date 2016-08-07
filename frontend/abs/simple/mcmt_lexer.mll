{
  open Mcmt_parser
    let keyword_table = Hashtbl.create 35
  let keyword k = try Hashtbl.find keyword_table k with Not_found -> (IDENT k)
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      [
	"and", AND;
        "assert", ASSERT;
        "Int", INT_DECL;
        "Real", REAL_DECL;
        "Bool", BOOL_DECL;
        "let", LET;
        "ite", ITE;
        "not", NOT;
        "or", OR;
        "query", QUERY;
        "xor", XOR;
        "true", TRUE;
        "false", FALSE;
      ]
}

let alpha = ['_' 'a'-'z' 'A'-'Z']
let alphanum = ['0'-'9' '_' '?' '!' '.' 'a'-'z' 'A'-'Z' '\'']
let digit = ['0'-'9']
let plusminus = ['-' '+']

rule token =
   parse eof                       { EOF }
     | [ '\000' ' ' '\t' '\r'] +   { token lexbuf }
     | '\n'                        { Lexing.new_line lexbuf ; token lexbuf }
     | ";;" [^'\n''\r']*            { token lexbuf }
     | alpha alphanum*             { keyword (Lexing.lexeme lexbuf) }
     | digit+ '.' digit+ (['e' 'E'] plusminus? digit+)? { REAL (float_of_string (Lexing.lexeme lexbuf)) }
     | digit+                      { INT (int_of_string (Lexing.lexeme lexbuf)) }
     | '+'                         { PLUS }
     | '-'                         { MINUS }
     | '*'                         { MUL }
     | '/'                         { DIV }
     | '='                         { EQ }
     | "/="                        { NEQ }
     | ">="                        { GE }
     | '>'                         { GT }
     | "<="                        { LE }
     | '<'                         { LT }
     | "=>"                        { IMPLIES }
     | '('                         { OPEN_PAREN }
     | ')'                         { CLOSE_PAREN }
     | "define-state-type"         { DEFINE_STATE_TYPE }
     | "define-states"             { DEFINE_STATES }
     | "define-transition"         { DEFINE_TRANSITION }
     | "define-transition-system"  { DEFINE_TRANSITION_SYSTEM }
     | "define-constant"           { DEFINE_CONSTANT }
     | _                           { LEX_ERROR }

{
  let parse ch = 
    let lexbuf = Lexing.from_channel ch in
    let ctx =
      try ctx token lexbuf
      with Parsing.Parse_error ->
	let p = Lexing.lexeme_start_p lexbuf in
	  Printf.eprintf "Parse error at line %d character %d, near %s\n"
	    p.Lexing.pos_lnum
	    (p.Lexing.pos_cnum - p.Lexing.pos_bol)
	    (Lexing.lexeme lexbuf);
	  failwith "Syntax error" in
      ctx
}
