grammar btor;

options {
  // C output for antlr
  language = 'C';  
}
 
@parser::includes {
  #include <string>
  #include "parser/command.h"
  #include "parser/parser_state.h"
  using namespace sal2;
}

@parser::postinclude {
  #define STATE (ctx->pState)
}


@parser::context
{
  /** The sal2 part of the parser state */
  parser::parser_state* pState;
}

/** Parses the file and produces the commands */
command returns [parser::command* cmd = 0] 
@declarations{
	// Map from indices to terms
	std::vector<expr::term_ref> terms;
    // List of variables 
    std::vector<size_t> variables;
	// Map from variables to their next versions
	std::vector<size_t> next;
}
  : definition[terms, variables, next]* EOF { 
  	  $cmd = 0; 
    } 
  ;
  
/** Parses a single BTOR definition */
definition [std::vector<expr::term_ref>& terms, std::vector<size_t>& vars, std::vector<size_t> next]
@declarations {
  std::string name;
  expr::term_ref term;
  expr::term_ref type;
  expr::bitvector bv;
}
  : // Variable declaration
    id=integer 'var' size=integer (name=symbol[name])? {
      type = STATE->tm().bitvectorType(size);
      if (name.size() > 0) { term = STATE->tm().mk_variable(name, type); }
      else { term = STATE->tm().mk_variable(type); }
      terms[id] = term;
    }
    // Constants 
  | id=integer 'constd' size=integer bv_constant[bv, size] {
      term = STATE->tm().mk_bitvector_constant(bv);
    }
    // Bit-vector operations 
  | id=integer 'xor' size=integer op1=subterm[terms] op2=subterm[terms] { 
      term = STATE->tm().mk_term(expr::TERM_BV_XOR, op1, op2);
    }
  | id=integer 'sra' size=integer op1=subterm[terms] op2=subterm[terms] {
      term = STATE->tm().mk_term(expr::TERM_BV_ASHR, op1, op2);
    }     
  ;

/** A subterm */
subterm[std::vector<expr::term_ref>& terms] returns [expr::term_ref subterm]
  : id=integer {
  	  if (id < 0) {
  	  	$subterm = STATE->tm().mk_term(expr::TERM_BV_NOT, terms[id]); 
  	  } else {
  	    $subterm = terms[id];
  	  }
    }
  ;
  
/** Parses an machine size integer */  
integer returns [int value = -1; ]
  : NUMERAL { value = STATE->token_as_int($NUMERAL); }
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
 