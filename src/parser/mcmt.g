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

using namespace sal2;

}


@parser::context
{
  /** The sal2 part of the parser state */
  parser::parser_state* pState;
}

/** Parses a command */
command returns [parser::command* cmd = 0] 
  : c = declare_state_type       { $cmd = c; }
  | c = define_states            { $cmd = c; }
  | c = define_transition        { $cmd = c; }
  | c = define_transition_system { $cmd = c; }
  | c = query                    { $cmd = c + 1; }
  | EOF { $cmd = 0; } 
  ;
  
/** Declaration of a state type */
declare_state_type returns [parser::command* cmd = 0]
@declarations {
  std::string id;
  std::vector<std::string> vars;  
  std::vector<expr::term_ref> types;
}
  : '(' 'declare-state-type' symbol[id] variable_list[vars, types] ')' 
    {
      expr::state_type state_type = STATE->new_state_type(id, vars, types); 
      $cmd = new parser::declare_state_type_command(state_type);
    }
  ; 

/** Definition of a state set  */
define_states returns [parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;
}
  : '(' 'define-states'
      symbol[id]       
      symbol[type_id]     { STATE->push_scope(); 
                            STATE->use_state_type(type_id, expr::state_type::CURRENT); 
                          }
      f = state_formula  { expr::state_formula sf = STATE->new_state_formula(id, type_id, f);
                           $cmd = new parser::define_states_command(sf); 
                           STATE->pop_scope(); 
                          }
    ')'
  ; 

/** Definition of a transition  */
define_transition returns [parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
}
  : '(' 'define-transition'
      symbol[id]
      symbol[type_id]                { STATE->push_scope();
                                       STATE->use_state_type(type_id, expr::state_type::CURRENT); 
                                       STATE->use_state_type(type_id, expr::state_type::NEXT); 
                                     }
      f = state_transition_formula   { expr::state_transition_formula stf = STATE->new_state_transition_formula(id, type_id, f);
                                       $cmd = new parser::define_transition_command(stf); 
                                       STATE->pop_scope(); 
                                     }
    ')'
  ; 

/** Definition of a transition system  */
define_transition_system returns [parser::command* cmd = 0]
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
query returns [parser::command* cmd = 0]
@declarations {
  std::string id;
}
  : '(' 'query'
      symbol[id]
      state_formula
    ')'
  ; 

/** A state formula */
state_formula returns [expr::term_ref sf = expr::term_ref()]
  : t = term { $sf = t; }
  ;

/** A state transition formula */
state_transition_formula returns [expr::term_ref stf = expr::term_ref()]
  : t = term { $stf = t; }
  ;

/** SMT2 term */
term returns [expr::term_ref t = expr::term_ref()]
@declarations{
  std::string id;
  std::vector<expr::term_ref> children;
} 
  : symbol[id] { t = STATE->get_variable(id); }                
  | c = constant { t = c; } 
  | '(' 
        op = term_op 
        term_list[children] 
     ')'   
     { t = STATE->tm().mk_term(op, children); }
  ; 
  
/** A symbol */
symbol[std::string& id] 
  : SYMBOL { id = STATE->token_text($SYMBOL); }
  ;
    
term_list[std::vector<expr::term_ref>& out]
  : ( t = term { out.push_back(t); } )+
  ;
  
constant returns [expr::term_ref t = expr::term_ref()] 
  : bc = bool_constant     { t = bc; } 
  | dc = decimal_constant  { t = dc; } 
  ; 

bool_constant returns [expr::term_ref t = expr::term_ref()]
  : 'true'   { t = STATE->tm().mk_boolean_constant(true); }
  | 'false'  { t = STATE->tm().mk_boolean_constant(false); }
  ;
  
decimal_constant returns [expr::term_ref t = expr::term_ref()]
  : NUMERAL { 
     expr::rational value(STATE->token_text($NUMERAL));
     t = STATE->tm().mk_rational_constant(value);
    }
  ; 

term_op returns [expr::term_op op = expr::OP_LAST]
  : 'and'            { op = expr::TERM_AND; } 
  | 'or'             { op = expr::TERM_OR; }
  | 'not'            { op = expr::TERM_NOT; }
  | 'implies'        { op = expr::TERM_IMPLIES; } 
  | 'xor'            { op = expr::TERM_XOR; }
  | 'ite'            { op = expr::TERM_ITE; }
  | '='              { op = expr::TERM_EQ;  }
  | '+'              { op = expr::TERM_ADD; }
  | '-'              { op = expr::TERM_SUB; }
  | '*'              { op = expr::TERM_MUL; }
  | '/'              { op = expr::TERM_DIV; }
  | '>'              { op = expr::TERM_GT; }
  | '>='             { op = expr::TERM_GEQ; }
  | '<'              { op = expr::TERM_LT; }
  | '<='             { op = expr::TERM_LEQ; }
  ;

/** Parse a list of variables with types */
variable_list[std::vector<std::string>& out_vars, std::vector<expr::term_ref>& out_types]
@declarations {
	std::string var_id;
	std::string type_id;
} 
  : '('
      ( '(' 
        symbol[var_id]   { out_vars.push_back(var_id); } 
        symbol[type_id]  { out_types.push_back(STATE->get_type(type_id)); }
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
 