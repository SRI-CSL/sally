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

@parser::context
{
  /** The sal2 part of the parser state */
  sal2::parser::mcmt_parser_state* pState;
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
  std::vector<std::vector> vars;  
  std::vector<expr::term_ref_strong> types;
}
  : '(' 'declare-state-type' symbol[id] variable_list[vars] ')'
    { STATE->declare_state_type(id, vars, types); $cmd = 0; }  
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
term 
@declarations{
  std::string id;
} 
  : structured_symbol
  | constant
  | '(' term_op term_list ')'
  ; 
  
/** A symbol */
symbol[std::string& id]
  : SYMBOL
  ;
  
/** Structured symbol (i.e a.b.c) */
structured_symbol
@declarations {
  std::string id;
}
  : symbol[id] ( '.' symbol[id])*
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
  : 'and'
  | 'or'
  | 'not'
  | 'implies'
  | 'xor'
  | 'ite'
  | '='
  | '+'
  | '-'
  | '*'
  | '/'
  | '>'
  | '>='
  | '<'
  | '<='
  ;

/** Parse a list of variables with types */
variable_list
@declarations {
	std::string var_id;
	std::string type_id;
} 
  : '('
      ( '(' symbol[var_id] symbol[type_id] ')' )+ 
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
 