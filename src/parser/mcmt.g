grammar mcmt;

options {
  // C output for antlr
  language = 'C';  
}
 
@parser::includes {
#include <string>
#include "parser/command.h"
#include "parser/mcmtParser_state.h"
}

@parser::context
{
  /** The sal2 part of the parser state */
  sal2::parser::mcmt_parser_state* sal2_state;
}

/** Parses a command */
command returns [sal2::parser::command* cmd = 0] 
  : c = declare_state_type_commmand { $cmd = c; }
  | EOF { $cmd = 0; } 
  ;
  
/** Declaration of a state type */
declare_state_type_commmand returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
}
  : '(' 'declare-state-type'
      simple_symbol[id]
      variable_list { $cmd = 0; }
    ')'
  ; 

/** Declaration of state set  */
declare_states returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
}
  : '(' 'declare-states'
      simple_symbol[id]
      simple_symbol[type_id]
      term
    ')'
  ; 

/** Declaration of a transition  */
define_transition returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
}
  : '(' 'define-transition'
      simple_symbol[id]
      simple_symbol[type_id]
      term
    ')'
  ; 

/** Declaration of a transition  */
define_transition_system returns [sal2::parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
  std::string initial_id;  
}
  : '(' 'define-transition-system'
      simple_symbol[id]
      simple_symbol[type_id]
      simple_symbol[initial_id]
      term
    ')'
  ; 

/** SMT2 formula */
term 
@declarations{
  std::string id;
} 
  : term_symbol
  | constant
  | '(' term_op term_list ')'
  ; 
  
term_list
  : term+
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

term_op
  : '='
  | '+'
  | '-'
  | '*'
  | '/'
  ;

/** Parse a list of variables with types */
variable_list
@declarations {
	std::string var_id;
	std::string type_id;
} 
  : '('
      ( '(' simple_symbol[var_id] simple_symbol[type_id] ')' )+ 
    ')'
  ; 

/** Match a simple simple_symbol. */
simple_symbol[std::string& id]
  : SIMPLE_SYMBOL
  ;
    
/** Match a full term simple_symbol */
term_symbol
  : TERM_SYMBOL
  ;
    
/** Comments (skip) */
COMMENT
  : ';' (~('\n' | '\r'))* { SKIP(); }
  ; 
  
/** Whitespace (skip) */
WHITESPACE
  : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP(); }
  ;
  
/** Matches a simple_symbol. */
SIMPLE_SYMBOL
  : ALPHA (ALPHA | DIGIT | '_' | '@')+
  ;

/** Matches a simple_symbol. */
TERM_SYMBOL
  : ALPHA (ALPHA | DIGIT | '_' | '@' | '.')+
  ;

/** Matches a letter. */
fragment
ALPHA : 'a'..'z' | 'A'..'Z';

/** Matches a numeral (sequence of digits) */
NUMERAL: DIGIT+;

/** Matches a digit */
fragment 
DIGIT : '0'..'9';  
 