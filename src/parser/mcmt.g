grammar mcmt;

options {
  // C output for antlr
  language = 'C';  
}
 
@parser::includes {
#include <string>
#include "parser/command.h"
#include "parser/parser_state.h"
}

@parser::postinclude {
#define STATE (ctx->pState)
}


@parser::context
{
  /** The sal2 part of the parser state */
  sal2::parser::parser_state* pState;
}

/** Parses a command */
command returns [sal2::parser::command* cmd = 0] 
  : c = declare_state_type       { $cmd = c; }
  | c = define_states            { $cmd = c + 1; }
  | c = define_transition        { $cmd = c + 1; }
  | c = define_transition_system { $cmd = c + 1; }
  | c = query                    { $cmd = c + 1; }
  | EOF { $cmd = 0; } 
  ;
  
/** Declaration of a state type */
declare_state_type returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
  std::vector<std::string> vars;  
  std::vector<sal2::expr::term_ref> types;
}
  : '(' 'declare-state-type' symbol[id] variable_list[vars, types] ')'
  ; 

/** Definition of a state set  */
define_states returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
}
  : '(' 'define-states'
      symbol[id]
      symbol[type_id]
      state_formula
    ')'
  ; 

/** Definition of a transition  */
define_transition returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
}
  : '(' 'define-transition'
      symbol[id]
      symbol[type_id]
      state_transition_formula
    ')'
  ; 

/** Definition of a transition system  */
define_transition_system returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
  std::string initial_id;  
}
  : '(' 'define-transition-system'
      symbol[id]
      symbol[type_id]
      symbol[initial_id]
      transition_list
    ')'
  ; 

/** A list of transitions */
transition_list
@declarations {
  std::string id;
} 
  : '(' symbol[id]+ ')'
  ;
  
/** Query  */
query returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
}
  : '(' 'query'
      symbol[id]
      state_formula
    ')'
  ; 

/** A state formula */
state_formula 
  : term
  ;

/** A state transition formula */
state_transition_formula 
  : term
  ;

/** SMT2 term */
term returns [sal2::expr::term_ref t = sal2::expr::term_ref()]
@declarations{
  std::string id;
  std::vector<sal2::expr::term_ref> children;
} 
  : structured_symbol                 
  | constant
  | '(' 
        op = term_op 
        term_list[children] 
     ')'   
     { STATE->mk_term(op, children); }
  ; 
  
/** A symbol */
symbol[std::string& id]
  : SYMBOL { id = STATE->token_text($SYMBOL); }
  ;
  
/** Structured symbol (i.e a.b.c) */
structured_symbol
@declarations {
  std::string id;
}
  : (symbol[id] '.')* symbol[id]
  ;
  
term_list[std::vector<sal2::expr::term_ref>& out]
  : ( t = term { out.push_back(t); } )+
  ;
  
constant 
  : bool_constant
  | decimal_constant
  ; 

bool_constant
  : 'true'
  | 'false'
  ;
  
decimal_constant
  : NUMERAL
  ; 

term_op returns [sal2::expr::term_op op = sal2::expr::OP_LAST]
  : 'and'            { op = sal2::expr::TERM_AND; } 
  | 'or'             { op = sal2::expr::TERM_OR; }
  | 'not'            { op = sal2::expr::TERM_NOT; }
  | 'implies'        { op = sal2::expr::TERM_IMPLIES; } 
  | 'xor'            { op = sal2::expr::TERM_XOR; }
  | 'ite'            { op = sal2::expr::TERM_ITE; }
  | '='              { op = sal2::expr::TERM_EQ;  }
  | '+'              { op = sal2::expr::TERM_ADD; }
  | '-'              { op = sal2::expr::TERM_SUB; }
  | '*'              { op = sal2::expr::TERM_MUL; }
  | '/'              { op = sal2::expr::TERM_DIV; }
  | '>'              { op = sal2::expr::TERM_GT; }
  | '>='             { op = sal2::expr::TERM_GEQ; }
  | '<'              { op = sal2::expr::TERM_LT; }
  | '<='             { op = sal2::expr::TERM_LEQ; }
  ;

/** Parse a list of variables with types */
variable_list[std::vector<std::string>& out_vars, std::vector<sal2::expr::term_ref>& out_types]
@declarations {
	std::string var_id;
	std::string type_id;
} 
  : '('
      ( '(' 
        symbol[var_id]   { out_vars.push_back(var_id); } 
        symbol[type_id]  
        ')'       
      )+ 
    ')'
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
  : ALPHA (ALPHA | DIGIT | '_' | '@')*
  ;

/** Matches a letter. */
fragment
ALPHA : 'a'..'z' | 'A'..'Z';

/** Matches a numeral (sequence of digits) */
NUMERAL: DIGIT+;

/** Matches a digit */
fragment 
DIGIT : '0'..'9';  
 