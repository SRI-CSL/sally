grammar mcmt;

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

/** Parses a command */
command returns [parser::command* cmd = 0] 
  : c = declare_state_type       { $cmd = c; }
  | c = define_states            { $cmd = c; }
  | c = define_transition        { $cmd = c; }
  | c = define_transition_system { $cmd = c; }
  | c = query                    { $cmd = c; }
  | EOF { $cmd = 0; } 
  ;
  
/** Declaration of a state type */
declare_state_type returns [parser::command* cmd = 0]
@declarations {
  std::string id;
  std::vector<std::string> vars;  
  std::vector<expr::term_ref> types;
}
  : '(' 'declare-state-type' 
        symbol[id, parser::PARSER_STATE_TYPE, false]  
        variable_list[vars, types] 
    ')' 
    {
      $cmd = new parser::declare_state_type_command(id, STATE->mk_state_type(id, vars, types));
    }
  ; 

/** Definition of a state set  */
define_states returns [parser::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;
}
  : '(' 'define-states'
        symbol[id, parser::PARSER_STATE_FORMULA, false]       
        symbol[type_id, parser::PARSER_STATE_TYPE, true] { 
            STATE->push_scope(); 
            STATE->use_state_type(type_id, system::state_type::STATE_CURRENT, true); 
        }
        f = state_formula { 
        	$cmd = new parser::define_states_command(id, STATE->mk_state_formula(id, type_id, f)); 
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
      symbol[id, parser::PARSER_TRANSITION_FORMULA, false]
      symbol[type_id, parser::PARSER_STATE_TYPE, true] { 
      	  STATE->push_scope();
          STATE->use_state_type(type_id, system::state_type::STATE_CURRENT, false); 
          STATE->use_state_type(type_id, system::state_type::STATE_NEXT, false); 
      }
      f = state_transition_formula   { 
          $cmd = new parser::define_transition_command(id, STATE->mk_transition_formula(id, type_id, f)); 
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
  std::vector<std::string> transitions;  
}
  : '(' 'define-transition-system'
      symbol[id, parser::PARSER_TRANSITION_SYSTEM, false]                    
      symbol[type_id, parser::PARSER_STATE_TYPE, true]
      symbol[initial_id, parser::PARSER_STATE_FORMULA, true]            
      transition_list[transitions]  {  
        $cmd = new parser::define_transition_system_command(id, STATE->mk_transition_system(id, type_id, initial_id, transitions));
      } 
    ')'
  ; 

/** A list of transitions */
transition_list[std::vector<std::string>& transitions] 
@declarations {
  std::string id;
} 
  : '(' (
    symbol[id, parser::PARSER_TRANSITION_FORMULA, true] { 
        transitions.push_back(id); 
    }
  	)+ ')'
  ;
  
/** Query  */
query returns [parser::command* cmd = 0]
@declarations {
  std::string id;
  const system::state_type* state_type;
}
  : '(' 'query'
    symbol[id, parser::PARSER_TRANSITION_SYSTEM, true] { 
        STATE->push_scope();
        state_type = STATE->ctx().get_transition_system(id)->get_state_type();
        STATE->use_state_type(state_type, system::state_type::STATE_CURRENT, true); 
    }
    f = state_formula { 
    	$cmd = new parser::query_command(STATE->ctx(), id, new system::state_formula(STATE->tm(), state_type, f));
        STATE->pop_scope(); 
    }
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
  : symbol[id, parser::PARSER_VARIABLE, true] { t = STATE->get_variable(id); }                
  | c = constant { t = c; } 
  | '(' 
        op = term_op 
        term_list[children] 
     ')'   
     { t = STATE->tm().mk_term(op, children); }
  ; 
  
/** 
 * A symbol. Returns it in the id string. If obj_type is not PARSER_OBJECT_LAST
 * we check whether it has been declared = true/false.
 */
symbol[std::string& id, parser::parser_object obj_type, bool declared] 
  : SYMBOL { 
  	    id = STATE->token_text($SYMBOL);
        STATE->ensure_declared(id, obj_type, declared);
    }
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
     expr::integer value(STATE->token_text($NUMERAL));
     t = STATE->tm().mk_integer_constant(value);
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
        symbol[var_id, parser::PARSER_OBJECT_LAST, false] { 
        	out_vars.push_back(var_id); 
        } 
        symbol[type_id, parser::PARSER_TYPE, true] { 
        	out_types.push_back(STATE->get_type(type_id)); 
        }
    ')' )+ 
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
 