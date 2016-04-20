(*
 * This file is part of sally.
 * Copyright (C) 2016 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 *)

{
  open Sal_parser
  let keyword_table = Hashtbl.create 53
  let keyword k = try Hashtbl.find keyword_table k with Not_found -> IDENT(k)
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      [
	"CONTEXT", CONTEXT;
	"BEGIN", BEGIN;
	"END", END;
	"MODULE", MODULE;
	"INPUT", INPUT;
	"OUTPUT", OUTPUT;
	"GLOBAL", GLOBAL;
	"LOCAL", LOCAL;
	"INVARIANT", INVARIANT;
	"INITIALIZATION", INITIALIZATION;
	"DEFINITION", DEFINITION;
	"TRANSITION", TRANSITION;
	"ARRAY", ARRAY;
	"TYPE", TYPE;
	"OF", OF;
	"LEMMA", LEMMA;
	"THEOREM", THEOREM;
	"LET", LET;
	"IN", IN;
	"FORALL", FORALL;
	"EXISTS", EXISTS;
	"IF", IF;
	"THEN", THEN;
	"ELSE", ELSE;
	"ELSIF", ELSIF;
	"ENDIF", ENDIF;
	"XOR", XOR;
	"OR", OR;
	"AND", AND;
	"NOT", NOT;
	"PROCESS_TYPE", PROCESS_TYPE;
      ]
}

let alpha = ['_' 'a'-'z' 'A'-'Z']
let alphanum = ['0'-'9' '_' '?' 'a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let plusminus = ['-' '+']

rule token =
   parse eof                       { EOF }
     | [ '\000' ' ' '\t' '\r'] +   { token lexbuf }
     | '\n'                        { Lexing.new_line lexbuf ; token lexbuf }
     | '%' [^'\n''\r']*            { token lexbuf }
     | alpha alphanum*             { keyword (Lexing.lexeme lexbuf) }
     | digit+ '.' digit+ (['e' 'E'] plusminus? digit+)? { FLOAT (Lexing.lexeme lexbuf) }
     | digit+                      { DECIMAL (Lexing.lexeme lexbuf) }
     | '+'                         { PLUS }
     | '-'                         { MINUS }
     | '*'                         { TIMES }
     | '/'                         { DIV }
     | '='                         { EQUAL }
     | "/="                        { DISEQUAL }
     | '<'                         { LT }
     | '>'                         { GT }
     | "<="                        { LE }
     | ">="                        { GE }
     | "<=>"                       { IFF }
     | "=>"                        { IMPLIES }
     | '('                         { OPEN_PAR }
     | ')'                         { CLOSE_PAR }
     | '['                         { OPEN_BRACKET }
     | ']'                         { CLOSE_BRACKET }
     | '{'                         { OPEN_BRACE }
     | '}'                         { CLOSE_BRACE }
     | ':'                         { COLUMN }
     | ';'                         { SEMI_COLUMN }
     | ','                         { COMMA }
     | ".."                        { ELLIPSIS }
     | '|'                         { BAR }
     | "|-"                        { SATISFIES }
     | '\''                        { NEXT }
     | "[]"                        { BOX }
     | "-->"                       { ARROW }
     | _                           { LEX_ERROR }

{
  let parse ch = 
    let lexbuf = Lexing.from_channel ch in
    let ctx =
      try context token lexbuf
      with Parsing.Parse_error ->
	let p = Lexing.lexeme_start_p lexbuf in
	  Printf.eprintf "Parse error at line %d character %d, near %s\n"
	    p.Lexing.pos_lnum
	    (p.Lexing.pos_cnum - p.Lexing.pos_bol)
	    (Lexing.lexeme lexbuf);
	  failwith "Syntax error" in
      ctx
}
