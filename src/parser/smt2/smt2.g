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
grammar smt2;

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
  #include "parser/smt2/smt2_state.h"
  using namespace sally;
}

@parser::postinclude {
  #define STATE (ctx->pState)
}


@parser::context
{
  /** The sally part of the parser state */
  parser::smt2_state* pState;
}

command returns [cmd::command* cmd = 0] 
  : smt2_command* { $cmd = STATE->mk_smt2_system(); }
  | EOF 
  ;

smt2_command
  : assert_command
  | check_sat_command
  | declare_const_command
  | declare_fun_command
  | define_fun_command
  | set_info_command
  | set_logic_command
  | exit_command
  ;
  
assert_command
  : '(' 'assert' t = term ')' { STATE->assert_command(t); }
  ;
  
check_sat_command
  : '(' 'check-sat' ')'
  ;
  
exit_command
  : '(' 'exit' ')'
  ;
  
declare_const_command 
@declarations {
  std::string id;
}
  : '(' 
        'declare-const' 
        symbol[id, parser::SMT2_VARIABLE, false] 
        t = type 
        { STATE->declare_variable(id, t); } 
    ')'
  ;

declare_fun_command 
@declarations {
  std::string id;
}
  : '(' 
        'declare-fun' 
        symbol[id, parser::SMT2_VARIABLE, false] 
        '(' ')' // No real functions
        t = type 
        { STATE->declare_variable(id, t); } 
    ')'
  ;

define_fun_command 
@declarations {
  std::string id;
}
  : '(' 
        'define-fun' 
        symbol[id, parser::SMT2_VARIABLE, false] 
        '(' ')' // No real functions
        t1 = type
        t2 = term 
        { STATE->set_variable(id, t2); } 
    ')'
  ;
  
set_info_command
  : '(' 'set-info' 
      ( ':smt-lib-version' DECIMAL_NUMERAL
      | ':status' ( 'sat' | 'unsat' | 'unknown' )
      | ATTRIBUTE (STRING | SYMBOL)
      )
    ')'
  ; 

set_logic_command
@declarations {
  std::string id;
}
  : '(' 'set-logic' ( 'QF_NRA' | 'QF_LRA' ) ')'
  ;
  
/** SMT2 term */
term returns [expr::term_ref t = expr::term_ref()]
@declarations {
  std::string id;
  std::vector<expr::term_ref> children;
} 
  : symbol[id, parser::SMT2_VARIABLE, true] { t = STATE->get_variable(id); }                
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
  ; 
  
let_assignments 
  : '(' let_assignment+ ')'
  ; 
  
let_assignment 
@declarations {
  std::string id;
}
  : '(' symbol[id, parser::SMT2_VARIABLE, false] 
        t = term 
        { STATE->set_variable(id, t); }
    ')'
  ;  
  
/** 
 * A symbol. Returns it in the id string. If obj_type is not SMT2_OBJECT_LAST
 * we check whether it has been declared = true/false.
 */
symbol[std::string& id, parser::smt2_object obj_type, bool declared] 
  : SYMBOL { 
  	    id = STATE->token_text($SYMBOL);
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
  : a = NUMERAL { 
       t = STATE->mk_rational_constant(STATE->token_text(a));
    }
  ; 

decimal_constant returns [expr::term_ref t = expr::term_ref()]
  : a = DECIMAL_NUMERAL {
       t = STATE->mk_rational_constant(STATE->token_text(a));
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
        
type returns [expr::term_ref type]
@declarations {
  std::string type_id;
}
  : // Primitive types
    symbol[type_id, parser::SMT2_TYPE, true] { type = STATE->get_type(type_id); }  
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
  : ALPHA (ALPHA | DIGIT | SYMBOL_EXTRA)* 
  | SYMBOL_EXTRA (ALPHA | DIGIT | SYMBOL_EXTRA)* 
  | ('|' (~'|')* '|')
  ;
  
ATTRIBUTE
  : ':' (ALPHA | '-')+
  ;

STRING : '\"' ( ~'"' | '""' )+ '"';

/** Matches a letter. */
fragment
ALPHA : 'a'..'z' | 'A'..'Z';

fragment 
SYMBOL_EXTRA : '_' | '@' | '.' | '!' | '%' | '~' | '?';

/** Matches a numeral (sequence of digits) */
NUMERAL: DIGIT+;

DECIMAL_NUMERAL: DIGIT+ '.' DIGIT+;

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

 
