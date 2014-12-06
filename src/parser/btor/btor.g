grammar btor;

options {
  // C output for antlr
  language = 'C';  
}
 
@parser::includes {
  #include <string>
  #include "parser/command.h"
  #include "parser/btor/btor_state.h"
  using namespace sal2;
}

@parser::postinclude {
  #define STATE (ctx->pState)
}


@parser::context
{
  /** The sal2 part of the parser state */
  parser::btor_state* pState;
}

/** Parses the file and produces the commands */
command returns [parser::command* cmd = 0] 
  : definition* EOF { 
  	  $cmd = 0; 
    } 
  ;
  
/** Parses a single BTOR definition */
definition 
@declarations {
  std::string name;
  expr::term_ref term;
  expr::term_ref type;
  expr::bitvector bv;
}
  : // Variables 
    id=integer 'var' size=integer (name=symbol[name])?                  
    { STATE->add_variable(id, size, name); }
    // Constants 
  | id=integer 'constd' size=integer bv_constant[bv, size]                 
    { STATE->add_constant(id, size, bv); }
    // Simple binary operations 
  | id=integer op = bv_binary_op size=integer t1=subterm t2=subterm
    { STATE->add_term(id, op, size, t1, t2); }
  | // Root nodes 
    id=integer 'root' size=integer t1=subterm 
    { STATE->add_root(id, size, t1); }
  ;

/** Parse a binary operator type */
bv_binary_op returns [expr::term_op op]
  : 'xor' { $op = expr::TERM_BV_XOR;  }
  | 'sra' { $op = expr::TERM_BV_ASHR; }
  ;

/** A subterm */
subterm returns [expr::term_ref subterm]
  : id=integer { $subterm = STATE->get_term(id); }
  ;
  
/** Parses an machine size integer */  
integer returns [int value = -1; ]
  :     NUMERAL { value = STATE->token_as_int($NUMERAL); }
  | '-' NUMERAL { value = -STATE->token_as_int($NUMERAL); }
  ;

/** Parses an ubounded integer */
bv_constant[expr::bitvector& bv, size_t size]
@declarations {
	expr::integer bv_int;
}
  : NUMERAL { 
  	  bv_int = STATE->token_as_integer($NUMERAL, 10);
  	  bv = expr::bitvector(size, bv_int); 
  	}
  ;
  
/** Parse a symbol (name) */
symbol[std::string& id] 
  : SYMBOL { id = STATE->token_text($SYMBOL); }
  ;  
  
/** Comments (skip) */
COMMENT
  : ';' (~('\n' | '\r'))* { SKIP(); }
  ; 
  
/** Whitespace (skip) */
WHITESPACE
  : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP(); }
  ;
  
/** Matches a symbol. */
SYMBOL
  : ALPHA (ALPHA | DIGIT | '_' | '@' | '.')*
  ;

/** Matches a letter. */
fragment
ALPHA : 'a'..'z' | 'A'..'Z';

/** Matches a numeral (sequence of digits) */
NUMERAL: DIGIT+;

/** Matches a digit */
fragment 
DIGIT : '0'..'9';  
 