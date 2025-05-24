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
grammar btor2;

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
  #include "parser/btor2/btor2_state.h"
  using namespace sally;
}

@parser::postinclude {
  #define STATE (ctx->pState)
}


@parser::context
{
  /** The sally part of the parser state */
  parser::btor2_state* pState;
}

/** Parses the file and produces the commands */
command returns [cmd::command* cmd = 0] 
  : definition* { 
  	  $cmd = STATE->finalize(); 
    } 
  | EOF
  ;
  
/** Parses a single btor2 definition */
definition 
@declarations {
  std::string name;
  expr::term_ref term;
  expr::term_ref type;
  expr::integer i;
}
  : // Bitvector Sorts
    id=pos_integer 'sort' 'bitvec' size=pos_integer              
    { STATE->add_bv_type(id, size); }
  | // Input Variables 
    id=pos_integer 'state' type_id=pos_integer (name=symbol[name])?                  
    { STATE->add_state_var(id, type_id, name); }
  | // State Variables 
    id=pos_integer 'input' type_id=pos_integer (name=symbol[name])?                  
    { STATE->add_input_var(id, type_id, name); }
  | // Init 
    id=pos_integer 'init' type_id=pos_integer var_id=pos_integer t=subterm
    { STATE->set_init(id, type_id, var_id, t); } 
  | // Next 
    id=pos_integer 'next' type_id=pos_integer var_id=pos_integer t=subterm
    { STATE->set_next(id, type_id, var_id, t); } 
  | // Constants 
    id=pos_integer 'zero' type_id=pos_integer               
    { STATE->add_constant_zero(id, type_id); }
  | // Constants 
    id=pos_integer 'one' type_id=pos_integer               
    { STATE->add_constant_one(id, type_id); }
  | // Constants 
    id=pos_integer 'ones' type_id=pos_integer               
    { STATE->add_constant_ones(id, type_id); }
  | // Constants 
    id=pos_integer 'constd' type_id=pos_integer int_literal[i, 10]
    { STATE->add_constant(id, type_id, i); }
  | id=pos_integer 'const' type_id=pos_integer int_literal[i, 2]
    { STATE->add_constant(id, type_id, i); }
  | id=pos_integer op=bv_unary_op type_id=pos_integer t=subterm
    { STATE->add_unary_term(id, op, type_id, t); }
  | // Simple binary operations 
    id=pos_integer op=bv_binary_op type_id=pos_integer t1=subterm t2=subterm
    { STATE->add_binary_term(id, op, type_id, t1, t2); }
  | // Extraction/Slicing
    id=pos_integer 'slice' type_id=pos_integer t=subterm high=pos_integer low=pos_integer
    { STATE->add_slice(id, type_id, t, high, low); }
  | // Unsigned Extension
    id=pos_integer 'uext' type_id=pos_integer t=subterm amt=pos_integer
    { STATE->add_uext(id, type_id, t, amt); }
  | // Signed Extension
    id=pos_integer 'sext' type_id=pos_integer t=subterm amt=pos_integer
    { STATE->add_sext(id, type_id, t, amt); }
  | // Conditional
    id=pos_integer 'ite' type_id=pos_integer t1=subterm t2=subterm t3=subterm
    { STATE->add_ite(id, type_id, t1, t2, t3); }
  | // Constraints 
    id=pos_integer 'constraint' t=subterm
    { STATE->add_constraint(id, t); } 
  | // Bad 
    id=pos_integer 'bad' t=subterm
    { STATE->add_bad(id, t); } 
  ;


/** Parse a binary operator type */
bv_unary_op returns [expr::term_op op = expr::OP_LAST]
  : 'not'      { op = expr::TERM_BV_NOT; }
  | 'inc'      { op = expr::TERM_BV_NOT; }
  | 'dec'      { op = expr::TERM_BV_NOT; }
  | 'neg'      { op = expr::TERM_BV_NEG; }
  | 'redand'   { op = expr::TERM_BV_REDAND; }
  | 'redor'    { op = expr::TERM_BV_REDOR; }
  | 'redxor'   { op = expr::TERM_BV_NOT; }
  ;

/** Parse a binary operator type */
bv_binary_op returns [expr::term_op op = expr::OP_LAST]
  : 'add'     { op = expr::TERM_BV_ADD; }
  | 'sub'     { op = expr::TERM_BV_SUB; }
  | 'mul'     { op = expr::TERM_BV_MUL; }
  | 'udiv'    { op = expr::TERM_BV_UDIV; }
  | 'sdiv'    { op = expr::TERM_BV_SDIV; }
  | 'urem'    { op = expr::TERM_BV_UREM; }
  | 'srem'    { op = expr::TERM_BV_SREM; }
  | 'smod'    { op = expr::TERM_BV_SMOD; }
  | 'xor'     { op = expr::TERM_BV_XOR;  }
  | 'sll'     { op = expr::TERM_BV_SHL; }
  | 'srl'     { op = expr::TERM_BV_LSHR; }
  | 'sra'     { op = expr::TERM_BV_ASHR; }
  // 'rol' rotate left
  // 'ror' rotate right
  | 'and'     { op = expr::TERM_BV_AND; }
  | 'or'      { op = expr::TERM_BV_OR; }
  | 'nand'    { op = expr::TERM_BV_NAND; }
  | 'nor'     { op = expr::TERM_BV_NOR; }
  | 'xnor'    { op = expr::TERM_BV_XNOR; }
  | 'concat'  { op = expr::TERM_BV_CONCAT; }
  | 'ule'     { op = expr::TERM_BV_ULEQ; }
  | 'sle'     { op = expr::TERM_BV_SLEQ; }
  | 'ult'     { op = expr::TERM_BV_ULT; }
  | 'slt'     { op = expr::TERM_BV_SLT; }
  | 'uge'     { op = expr::TERM_BV_UGEQ; }
  | 'sge'     { op = expr::TERM_BV_SGEQ; }
  | 'ugt'     { op = expr::TERM_BV_UGT; }
  | 'sgt'     { op = expr::TERM_BV_SGT; }
  | 'eq'      { op = expr::TERM_EQ; }
  | 'iff'     { op = expr::TERM_EQ; }
  | 'implies' { op = expr::TERM_IMPLIES; }
  ;

/** A subterm */
subterm returns [expr::term_ref subterm]
  : id=integer { subterm = STATE->get_term(id); }
  ;
  
/** Parses a machine size integer */
integer returns [int value = -1]
  :     p=pos_integer { value = p; }
  | '-' p=pos_integer { value = -p; }
  ;

pos_integer returns [size_t value = 0]
  : NUMERAL { value = STATE->token_as_int($NUMERAL); }
  ;

/** Parses an unbounded integer */
int_literal[expr::integer& i, size_t base]
  : NUMERAL { 
  	  i = STATE->token_as_integer($NUMERAL, base);
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
  
/** Matches a symbol. 
    First character cannot be '-' to avoid ambiguity with negated subterms */
SYMBOL
  : ~(' ' | '\t' | '\f' | '\r' | '\n' | '-' | DIGIT) ~(' ' | '\t' | '\f' | '\r' | '\n')*
  ;

/** Matches a numeral (sequence of digits) */
NUMERAL: DIGIT+;

/** Matches a digit */
fragment 
DIGIT : '0'..'9';  

/** Matches a letter. */
fragment
ALPHA : 'a'..'z' | 'A'..'Z';
