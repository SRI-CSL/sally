/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
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
 */
grammar mcmt;

options {
  // C output for antlr
  language = 'C';  
}
 
@parser::includes {
  #include <string>
  #include "command/command.h"
  #include "command/assume.h"
  #include "command/declare_state_type.h"
  #include "command/define_states.h"
  #include "command/define_transition.h"
  #include "command/define_transition_system.h"
  #include "command/query.h"
  #include "command/sequence.h" 
  #include "parser/mcmt/mcmt_state.h"
  using namespace sally;
}

@parser::postinclude {
  #define STATE (ctx->pState)
}


@parser::context
{
  /** The sally part of the parser state */
  parser::mcmt_state* pState;
}

/** Parses a command */
command returns [cmd::command* cmd = 0] 
  : (internal_command*) c = system_command { $cmd = c; }
  ;

/** Parser an internal command */
internal_command
  : define_constant
  ; 

/** Parses a system definition command */  
system_command returns [cmd::command* cmd = 0] 
  : c = declare_state_type       { $cmd = c; }
  | c = define_states            { $cmd = c; }
  | c = define_transition        { $cmd = c; }
  | c = define_transition_system { $cmd = c; }
  | c = assume                   { $cmd = c; }                    
  | c = query                    { $cmd = c; }
  | EOF { $cmd = 0; }
  ;
  
/** Declaration of a state type */
declare_state_type returns [cmd::command* cmd = 0]
@declarations {
  std::string id;
  std::vector<std::string> state_vars;  
  std::vector<expr::term_ref> state_types;
  std::vector<std::string> input_vars;  
  std::vector<expr::term_ref> input_types;
}
  : '(' 'define-state-type' 
        // Name of the type
        symbol[id, parser::MCMT_STATE_TYPE, false]
        // State variables  
        variable_list[state_vars, state_types]
        // Input variables
        variable_list[input_vars, input_types]? 
    ')' 
    {
      $cmd = new cmd::declare_state_type(id, STATE->mk_state_type(id, state_vars, state_types, input_vars, input_types));
    }
  ; 

/** Definition of a state set  */
define_states returns [cmd::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;
  const system::state_type* state_type;
}
  : '(' 'define-states'
        symbol[id, parser::MCMT_STATE_FORMULA, false]       
        symbol[type_id, parser::MCMT_STATE_TYPE, true] {
        	state_type = STATE->ctx().get_state_type(type_id); 
        }
        sf = state_formula[state_type] { 
        	$cmd = new cmd::define_states(id, sf); 
        }
    ')'
  ; 

/** Definition of a transition  */
define_transition returns [cmd::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
  const system::state_type* state_type;
}
  : '(' 'define-transition'
      symbol[id, parser::MCMT_TRANSITION_FORMULA, false]
      symbol[type_id, parser::MCMT_STATE_TYPE, true] { 
          state_type = STATE->ctx().get_state_type(type_id); 
      }
      f = state_transition_formula[state_type] {
          $cmd = new cmd::define_transition(id, f); 
      }
    ')'
  ; 

/** Definition of a transition system  */
define_transition_system returns [cmd::command* cmd = 0]
@declarations {
  std::string id;
  std::string type_id;  
  std::string initial_id;
  std::vector<std::string> transitions;
  const system::state_type* state_type;
}
  : '(' 'define-transition-system'
      symbol[id, parser::MCMT_TRANSITION_SYSTEM, false]                    
      symbol[type_id, parser::MCMT_STATE_TYPE, true] { state_type = STATE->ctx().get_state_type(type_id); }
      initial_states = state_formula[state_type]
      transition_relation = state_transition_formula[state_type]    
      {  
      	system::transition_system* T = new system::transition_system(state_type, initial_states, transition_relation); 
        $cmd = new cmd::define_transition_system(id, T);
      } 
    ')'
  ; 

/** Assumptions  */
assume returns [cmd::command* cmd = 0]
@declarations {
  std::string id;
  const system::state_type* state_type;
}
  : '(' 'assume'
    symbol[id, parser::MCMT_TRANSITION_SYSTEM, true] { 
        state_type = STATE->ctx().get_transition_system(id)->get_state_type();
    }
    f = state_formula[state_type] { 
    	$cmd = new cmd::assume(STATE->ctx(), id, f);
    }
    ')'
  ; 
  
/** Query  */
query returns [cmd::command* cmd = 0]
@declarations {
  std::string id;
  const system::state_type* state_type;
}
  : '(' 'query'
    symbol[id, parser::MCMT_TRANSITION_SYSTEM, true] { 
        state_type = STATE->ctx().get_transition_system(id)->get_state_type();
    }
    f = state_formula[state_type] { 
    	$cmd = new cmd::query(STATE->ctx(), id, f);
    }
    ')'
  ; 

/** Parse a constant definition */
define_constant 
@declarations {
  std::string id;
}
  : '(' 'define-constant'
    symbol[id, parser::MCMT_VARIABLE, false] 
    c = term { STATE->set_variable(id, c); }
    ')'
  ; 

/** A state formula */
state_formula[const system::state_type* state_type] returns [system::state_formula* sf = 0]
@declarations {
  std::string sf_id;
}
  : // Declare state variables 
    { 
        STATE->push_scope(); 
        STATE->use_state_type(state_type, system::state_type::STATE_CURRENT, true); 
    }      
    // Parse the actual formula
    sf_term = term  
    // Undeclare the variables and return the formula
    { 
   		STATE->pop_scope(); 
   		$sf = new system::state_formula(STATE->tm(),  state_type, sf_term);
    }
  ;


/** A state transition formula */
state_transition_formula[const system::state_type* state_type] returns [system::transition_formula* tf = 0]
@declarations {
  std::string tf_id;
}
  : // Use the state type 
    { 
        STATE->push_scope();
        STATE->use_state_type_and_transitions(state_type);
    } 
    // Parse the term 
    tf_term = term 
    // Undeclare the variables and make the transition
    {
        STATE->pop_scope();
        $tf = new system::transition_formula(STATE->tm(), state_type, tf_term);
    }
  ;

/** SMT2 term */
term returns [expr::term_ref t = expr::term_ref()]
@declarations {
  std::string id;
  std::vector<expr::term_ref> children;
} 
  : symbol[id, parser::MCMT_VARIABLE, true] { t = STATE->get_variable(id); }                
  | c = constant { t = c; }
  | '(' 'let'
       { STATE->push_scope(); } 
       let_assignments 
       let_t = term { t = let_t; }
       { STATE->pop_scope(); }
    ')' 
  | '(' 
        op = term_op 
        term_list[children] 
     ')'   
     { t = STATE->tm().mk_term(op, children); }
  | '(' 
       '(_' 'extract' high = NUMERAL low = NUMERAL ')'
       s = term
    ')' 
    {
     expr::integer hi_value(STATE->token_text(high), 10);
     expr::integer lo_value(STATE->token_text(low), 10);
     expr::bitvector_extract extract(hi_value.get_unsigned(), lo_value.get_unsigned());
     t = STATE->tm().mk_bitvector_extract(s, extract);
    }
  | '(' 'cond' 
       ( '(' term_list[children] ')' )+
       '(' 'else' else_term = term ')'
       { 
       	 children.push_back(else_term);
       	 t = STATE->mk_cond(children);
       }
    ')'
  | '(' '/=' { STATE->lsal_extensions() }? term_list[children] 
    {
  	  t = STATE->tm().mk_term(expr::TERM_EQ, children);
  	  t = STATE->tm().mk_term(expr::TERM_NOT, t);
    }   
    ')'
  ; 
  
let_assignments 
  : '(' let_assignment+ ')'
  ; 
  
let_assignment 
@declarations {
  std::string id;
}
  : '(' symbol[id, parser::MCMT_VARIABLE, false] 
        t = term 
        { STATE->set_variable(id, t); }
    ')'
  ;  
  
/** 
 * A symbol. Returns it in the id string. If obj_type is not MCMT_OBJECT_LAST
 * we check whether it has been declared = true/false.
 */
symbol[std::string& id, parser::mcmt_object obj_type, bool declared] 
@declarations {
  bool is_next = false;
}
  : SYMBOL ('\'' { STATE->lsal_extensions() }? { is_next = true; })? { 
  	    id = STATE->token_text($SYMBOL);
        if (is_next) { id = "next." + id; }
        id.erase(std::remove(id.begin(), id.end(), '|'), id.end());
        STATE->ensure_declared(id, obj_type, declared);
    }
  ;
    
term_list[std::vector<expr::term_ref>& out]
  : ( t = term { out.push_back(t); } )+
  ;
  
constant returns [expr::term_ref t = expr::term_ref()] 
  : bc = bool_constant     { t = bc; } 
  | dc = integer_constant  { t = dc; }
  | fc = decimal_constant { t = fc; }
  | bvc = bitvector_constant { t = bvc; }
  ; 

bool_constant returns [expr::term_ref t = expr::term_ref()]
  : 'true'   { t = STATE->tm().mk_boolean_constant(true); }
  | 'false'  { t = STATE->tm().mk_boolean_constant(false); }
  ;
  
integer_constant returns [expr::term_ref t = expr::term_ref()]
  : NUMERAL { 
     expr::rational value(STATE->token_text($NUMERAL));
     t = STATE->tm().mk_rational_constant(value);
    }
  ; 

decimal_constant returns [expr::term_ref t = expr::term_ref()]
  : a = NUMERAL '.' b = NUMERAL {
    expr::rational value(STATE->token_text(a), STATE->token_text(b));
    t = STATE->tm().mk_rational_constant(value);
    }
  ;

bitvector_constant returns [expr::term_ref t = expr::term_ref()]
  : HEX_NUMERAL {
     std::string hex_number(STATE->token_text($HEX_NUMERAL));
     hex_number = hex_number.substr(2); 
     expr::integer int_value(hex_number, 16);
     expr::bitvector value(hex_number.size()*4, int_value);
     t = STATE->tm().mk_bitvector_constant(value);
    }
  | BIN_NUMERAL {
     std::string bin_number(STATE->token_text($BIN_NUMERAL));
     bin_number = bin_number.substr(2);
     expr::integer int_value(bin_number, 2);
     expr::bitvector value(bin_number.size(), int_value);
     t = STATE->tm().mk_bitvector_constant(value);
    }
  | '(_' v = BV_NUMERAL s = NUMERAL ')' {
     expr::integer int_value(STATE->token_text(v).substr(2), 10);
     expr::integer size_value(STATE->token_text(s), 10);
     expr::bitvector value(size_value.get_unsigned(), int_value);
     t = STATE->tm().mk_bitvector_constant(value);     
    }
  ;

term_op returns [expr::term_op op = expr::OP_LAST]
  : // Boolean
    'and'            { op = expr::TERM_AND; } 
  | 'or'             { op = expr::TERM_OR; }
  | 'not'            { op = expr::TERM_NOT; }
  | '=>'             { op = expr::TERM_IMPLIES; } 
  | 'xor'            { op = expr::TERM_XOR; }
  | 'ite'            { op = expr::TERM_ITE; }
    // Equality
  | '='              { op = expr::TERM_EQ;  }
    // Arithmetic
  | '+'              { op = expr::TERM_ADD; }
  | '-'              { op = expr::TERM_SUB; }
  | '*'              { op = expr::TERM_MUL; }
  | '/'              { op = expr::TERM_DIV; }
  | '>'              { op = expr::TERM_GT; }
  | '>='             { op = expr::TERM_GEQ; }
  | '<'              { op = expr::TERM_LT; }
  | '<='             { op = expr::TERM_LEQ; }
  | 'to_int'         { op = expr::TERM_TO_INT; }
  | 'to_real'        { op = expr::TERM_TO_REAL; }
  | 'is_int'         { op = expr::TERM_IS_INT; }
    // Bitvectors
  | 'bvadd' { op = expr::TERM_BV_ADD; }
  | 'bvsub' { op = expr::TERM_BV_SUB; }
  | 'bvmul' { op = expr::TERM_BV_MUL; }
  | 'bvudiv' { op = expr::TERM_BV_UDIV; }
  | 'bvsdiv' { op = expr::TERM_BV_SDIV; }
  | 'bvurem' { op = expr::TERM_BV_UREM; }
  | 'bvsrem' { op = expr::TERM_BV_SREM; }
  | 'bvsmod' { op = expr::TERM_BV_SMOD; }
  | 'bvxor' { op = expr::TERM_BV_XOR; }
  | 'bvshl' { op = expr::TERM_BV_SHL; }
  | 'bvlshr' { op = expr::TERM_BV_LSHR; }
  | 'bvashr' { op = expr::TERM_BV_ASHR; }
  | 'bvnot' { op = expr::TERM_BV_NOT; }
  | 'bvand' { op = expr::TERM_BV_AND; }
  | 'bvor' { op = expr::TERM_BV_OR; }
  | 'bvnand' { op = expr::TERM_BV_NAND; }
  | 'bvnor' { op = expr::TERM_BV_NOR; }
  | 'bvxnor' { op = expr::TERM_BV_XNOR; }
  | 'concat' { op = expr::TERM_BV_CONCAT; }
  | 'bvule' { op = expr::TERM_BV_ULEQ; }
  | 'bvsle' { op = expr::TERM_BV_SLEQ; }
  | 'bvult' { op = expr::TERM_BV_ULT; }
  | 'bvslt' { op = expr::TERM_BV_SLT; }
  | 'bvuge' { op = expr::TERM_BV_UGEQ; }
  | 'bvsge' { op = expr::TERM_BV_SGEQ; }
  | 'bvugt' { op = expr::TERM_BV_UGT; }
  | 'bvsgt' { op = expr::TERM_BV_SGT; }
  ;

/** Parse a list of variables with types */
variable_list[std::vector<std::string>& out_vars, std::vector<expr::term_ref>& out_types]
@declarations {
  std::string var_id;
} 
  : '(' 
    ( '(' 
        // Variable name
        symbol[var_id, parser::MCMT_OBJECT_LAST, false] { 
        	out_vars.push_back(var_id); 
        } 
        // Type: either basic or composite (TODO: bitvector) 
        t = type { out_types.push_back(t); } 
    ')' )*
    ')'
  ; 
        
type returns [expr::term_ref type]
@declarations {
  std::string type_id;
}
  : // Primitive types
    symbol[type_id, parser::MCMT_TYPE, true] { type = STATE->get_type(type_id); }  
  | // Bitvector types 
    '(_' 'BitVec' size = NUMERAL ')' { 
       expr::integer int_value(STATE->token_text(size), 10);
       type = STATE->get_bitvector_type(int_value.get_unsigned());       
    }
  ;

/** Comments (skip) */
COMMENT
  : ';' (~('\n' | '\r'))* { SKIP(); }
  ; 
  
/** Whitespace (skip) */
WHITESPACE
  : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP(); }
  ;

/** Bitvector numeral */
BV_NUMERAL: 'bv' DIGIT+;

/** Matches a symbol. */
SYMBOL
  : (ALPHA | ('|' (~'|')* '|')) (ALPHA | ('|' (~'|')* '|') | DIGIT | '_' | '@' | '.' | '!' | '%' )* 
  ;

/** Matches a letter. */
fragment
ALPHA : 'a'..'z' | 'A'..'Z';

/** Matches a numeral (sequence of digits) */
NUMERAL: DIGIT+;

/** Matches a binary numeral (sequence of digits) */
BIN_NUMERAL: '#b' ('0'|'1')+;

/** Matches a binary numeral (sequence of digits) */
HEX_NUMERAL: '#x' HEX_DIGIT+;

/** Matches a digit */
fragment 
DIGIT : '0'..'9';  

/** Matches a hexadecimal digit */
fragment 
HEX_DIGIT : DIGIT | 'a'..'f' | 'A'..'F';
 
