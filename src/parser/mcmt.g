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
  ;
  
/** Declaration of a state type */
declare_state_type_commmand returns [sal2::parser::command* cmd = 0]
  : '(' 'declare-state-type'
    { $cmd = 0; }
    ')'
  ; 

/** Match a symbol. */
symbol[std::string& id]
  : SYMBOL 
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
  : ALPHA (ALPHA | DIGIT | SYMBOL_NONALPHA)+
  ;

/** Matches a letter. */
fragment
ALPHA
  : 'a'..'z' 
  | 'A'..'Z'
  ;
  
/** Matches a digit */
fragment 
DIGIT 
  : '0'..'9'
  ;  
 
/** Matches other characters allowed in symbols. */
fragment 
SYMBOL_NONALPHA
  : '_' 
  | '@'
  ;