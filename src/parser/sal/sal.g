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
grammar sal;

options {
  // C output for antlr
  language = 'C'; 
}
 
@parser::includes {
  #include <string>
  #include "parser/command.h"
  #include "parser/sal/sal_state.h"
  using namespace sally;
}

@parser::postinclude {
  #define STATE (ctx->pState)
}


@parser::context
{
  /** The sally part of the parser state. */
  parser::sal_state* pState;
}

/** SAL context returned as a sequence command. */
command returns [parser::command* cmd = 0]
  : context
  | EOF
  ; 

/** SAL context, with parameters for parametrization. */
context 
  : identifier ('{' var_declaration_list '}')? ':' KW_CONTEXT '=' context_body   
  ;

/** Body of the context */
context_body 
  : KW_BEGIN declaration (';' declaration)* ';'? KW_END 
  ;

/** 
 * Individual declarations in the context. Usually, defined by defining a some 
 * constants (these are either instantiated to a value, or don't change during 
 * evolution), types, then the modules, and finally at least one property to 
 * check.  
 */
declaration 
  : constant_declaration
  | type_declaration     
  | module_declaration
  | assertion_declaration
  ;

/** Declaration of constants (including functions) */
constant_declaration 
  : identifier ('(' var_declaration_list ')')? ':' type ('=' term)?
  ;

/** Declations of types */
type_declaration 
  : identifier ':' KW_TYPE ('=' type)?
  ;

/** Assertions (lemmas, theorems, ...) */
assertion_declaration 
  : identifier ':' assertion_form assertion_term
  ;

/** Types of assertions (there is no semantics attached to these names) */
assertion_form 
  : (KW_OBLIGATION | KW_CLAIM | KW_LEMMA | KW_THEOREM)
  ;

/** The actual assertion, does 'term' hold in the 'module' */
assertion_term 
  : module '|-' term
  ;

/** Definition of a module */
module_declaration 
  : identifier ('[' var_declaration_list ']')? ':' 'MODULE' '=' module
  ;

/** Types */ 
type
  : type_name
  | scalar_type 
  | subrange_type
  | array_type
  | subtype
  | record_type
  ;

/** Subtype of a type */
subtype
  : '{' identifier ':' type '|' term '}'
  ;

/** Name of an existing type */
type_name 
  : identifier
  ;

/** List of scalars (an enum) */
scalar_type
  : '{' identifier (',' identifier)* '}'
  ;

/** Types that can be used for indexing */
index_type 
  : identifier 
  | subrange_type 
  ;

/** Bound is either a term or infinity */
bound: term | '_';

/** Range types */
subrange_type 
  : '[' bound '..' bound ']'
  ;

/** Array type, from indices to elements */
array_type 
  : KW_ARRAY index_type KW_OF type
  ;


/** Record types */
record_type
  : '[#' var_declaration_list '#]'
  ;

// Expressions: typical

term 
  : iff_term
  ;

iff_term 
  : implies_term (OP_IFF implies_term)?
  ;

implies_term 
  : or_term (OP_IMPLIES or_term)?
  ;

or_term 
  : and_term ((KW_OR | KW_XOR) and_term)*
  ;

and_term 
  : not_term (KW_AND not_term)*
  ;

not_term 
  : NOT not_term
  | eq_term 
  ;

eq_term 
  : rel_term ((OP_EQ | OP_NEQ) rel_term)?
  ;

rel_term 
  : additive_term ((OP_GT | OP_GEQ | OP_LT | OP_LEQ) additive_term)?
  ;

infix_application 
  : additive_term (IDENTIFIER additive_term)?
  ;

additive_term 
  : multiplicative_term  ((OP_ADD | OP_SUB) multiplicative_term)*
  ;

multiplicative_term 
  : unary_term ((OP_MUL | OP_DIV | KW_MOD | KW_DIV) unary_term)*
  ;

unary_term 
  : (OP_SUB unary_term)
  | simple_expression
  ;

simple_expression 
  : term_prefix (term_suffix)*
  ;

term_prefix 
  : identifier '\''?
  | numeral
  | lambda_term
  | quantified_term
  | let_term
  | array_literal 
  | record_literal 
  | tuple_literal 
  | set_term
  | conditional_term
  ;

term_suffix 
  : argument
  | access
  | update_suffix
  ;

lambda_term 
  : KW_LAMBDA '(' var_declaration_list ')' ':' term // TODO: recursion here
  ;

quantified_term 
  : KW_FORALL '(' var_declaration_list ')' ':' term // TODO: recursion here
  | KW_EXISTS '(' var_declaration_list ')' ':' term // TODO: recursion here
  ;

let_term 
  : KW_LET let_declarations KW_IN term
  ;

let_declarations 
  : let_declaration (',' let_declaration)*
  ;

let_declaration 
  : identifier ':' type '=' term
  ;

array_literal 
  : '[' '[' index_var_declaration ']' term ']'
  ;

record_literal
  : '(#' record_entry (',' record_entry)* '#)'
  ;

record_entry 
  : identifier ':=' term
  ;

tuple_literal 
  : '(' term_list ')' 
  ;

set_term 
  : '{' identifier ':' type '|' term '}'
  | '{' (term (',' term)*)? '}'
  ;

conditional_term 
  : KW_IF   term
    KW_THEN term
    ('ELSIF' term KW_THEN term)*   
    KW_ELSE term
    KW_ENDIF
  ;

argument
  : '(' term_list ')' 
  ;

term_list 
  : term (',' term )* 
  ;

update_suffix 
  : KW_WITH update
  ;

update 
  : update_position ':=' term 
  ;

update_position 
  : (argument | access)+
  ;

index_var_declaration 
  : identifier ':' index_type
  ;

identifier_list 
  : identifier (',' identifier)* 
  ;

pidentifier_list 
  : identifier_list;

var_declaration 
  : identifier_list ':' type 
  ;

var_declaration_list 
  : var_declaration (',' var_declaration)*
  ;

/* The Transition Language */

lvalue 
  : identifier '\''? access*
  ;

access 
  : '[' term ']' 
  | '.' identifier
  | '.' numeral
  ;

rhs_definition 
  : OP_EQ term 
  | KW_IN term 
  ;

simple_definition 
  : lvalue rhs_definition
  ;

forall_definition 
  : '(' KW_FORALL '(' var_declaration_list ')' ':' definitions ')' 
  ;

definition 
  : simple_definition 
  | forall_definition 
  ;

definitions :
  definition (';' definition)* ';'?;

guard 
  : term
  ;

assignments 
  : simple_definition (';' simple_definition)* ';'?
  ;

guarded_command 
  : guard '-->' assignments?
  | KW_ELSE '-->' assignments? 
  ;

/* The Module Language */

// TODO: What's the precedence here
module 
  : basic_module ((OP_ASYNC|OP_SYNC) basic_module)*
  ;

basic_module 
  : base_module
  | multi_synchronous
  | multi_asynchronous
  | hiding
  | new_output
  | renaming
  | with_module
  | module_name
  | observe_module
  | ('(' module ')') 
  ;

base_module
  : KW_BEGIN base_declaration_list KW_END
  ;

base_declaration_list 
  : base_declaration* 
  ;

base_declaration 
  : input_declaration 
  | output_declaration 
  | global_declaration 
  | local_declaration 
  | definition_declaration 
  | invariant_declaration
  | init_formula_declaration 
  | init_declaration 
  | transition_declaration
  ;

multi_synchronous 
  : '(' OP_SYNC '(' index_var_declaration ')' ':' module ')'
  ;

multi_asynchronous 
  : '(' OP_ASYNC '(' index_var_declaration ')' ':' module ')'
  ;

hiding
  : KW_LOCAL pidentifier_list KW_IN module
  ;

new_output 
  : KW_OUTPUT pidentifier_list KW_IN module
  ;

renaming 
  : KW_RENAME rename_list KW_IN module
  ;

rename_list 
  : rename (',' rename)*
  ;

rename 
  : lvalue KW_TO lvalue
  ;

with_module
  : KW_WITH new_var_declaration_list module
  ;

module_name 
  : identifier module_actuals
  ;

module_actuals 
  : ('[' term_list ']')?
  ;

observe_module 
  : KW_OBSERVE module KW_WITH module
  ;

/* Declarations within modules */

input_declaration 
  : KW_INPUT var_declaration_list
  ;

output_declaration 
  : KW_OUTPUT var_declaration_list
  ;

global_declaration 
  : KW_GLOBAL var_declaration_list
  ;

local_declaration
  : KW_LOCAL var_declaration_list
  ;

definition_declaration
  : KW_DEFINITION definitions
  ;

invariant_declaration
  : KW_INVARIANT term
  ;

init_formula_declaration 
  : KW_INITFORMULA term
  ;

init_declaration 
  : KW_INITIALIZATION definition_or_command (';' definition_or_command)* ';'?
  ;

transition_declaration 
  : KW_TRANSITION definition_or_command (';' definition_or_command)* ';'?
  ; 

multi_command 
  : '(' OP_ASYNC '(' var_declaration_list ')' ':' some_command ')' 
  ;

some_command 
  : (identifier ':') ? guarded_command 
  | (identifier ':') ? multi_command 
  ;

some_commands 
  : some_command (OP_ASYNC some_command)*
  ;

definition_or_command
  : definition
  | ('[' some_commands ']')
  ;

new_var_declaration 
  : input_declaration 
  | output_declaration 
  | global_declaration
  ;

new_var_declaration_list 
  : new_var_declaration (';' new_var_declaration)*
  ;

type_declarations 
  : identifier_list ':' KW_TYPE;

identifier 
  : IDENTIFIER
  ;

numeral 
  : NUMERAL
  ;

/** Numerals */
NUMERAL: DIGIT+;

/** Keywords */ 
KW_ARRAY: A R R A Y; 
KW_BEGIN: B E G I N;
KW_CONTEXT: C O N T E X T;
KW_CLAIM: C L A I M;
KW_DEFINITION: D E F I N I T I O N;
KW_DIV: D I V;
KW_ELSE: E L S E;
KW_ENDIF: E N D I F;
KW_END: E N D;
KW_EXISTS: E X I S T S;
KW_FORALL: F O R A L L;
KW_GLOBAL: G L O B A L;
KW_INITFORMULA: I N I T F O R M U L A;
KW_INITIALIZATION: I N I T I A L I Z A T I O N;
KW_INVARIANT: I N V A R I A N T;
KW_INPUT: I N P U T; // Had to rename because it clashes with antlr #define INPUT
KW_IF: I F;
KW_IN: I N;
KW_LAMBDA: L A M B D A;
KW_LET: L E T;
KW_LEMMA: L E M M A;
KW_LOCAL: L O C A L;
KW_MOD: M O D;
KW_OF: O F;
KW_OUTPUT: O U T P U T;
KW_OBLIGATION: O B L I G A T I O N;
KW_OBSERVE: O B S E R V E;
KW_RENAME: R E N A M E;
KW_THEN: T H E N;
KW_THEOREM: T H E O R E M;
KW_TRANSITION: T R A N S I T I O N;
KW_TYPE: T Y P E;
KW_TO: T O;
KW_WITH: W I T H;


/** Boolean opearators */
KW_AND: A N D;
KW_OR: O R;
KW_XOR: X O R;
NOT: N O T;
OP_IMPLIES: '=>';
OP_IFF: '<=>';

// Arithmetic Operators
OP_SUB: '-';
OP_ADD: '+';
OP_MUL: '*';
OP_DIV: '/';

// Relational Operators
OP_LEQ: '<=';
OP_LT: '<';
OP_GEQ: '>=';
OP_GT: '>';
OP_NEQ: '/=';
OP_EQ: '=';

// Combination operators
OP_SYNC: '||' ;
OP_ASYNC: '[]';

/** Letters */ 
fragment                                     
LETTER : 'a'..'z' | 'A'..'Z';

/** Digits */
fragment   
DIGIT : '0'..'9';

/** Whitespace characters */
fragment
WHITESPACE : ' ' | '\t' | '\n' | '\r' | '\f';

/** Comments (which we skip) */
SL_COMMENT
  : '%' (~('\n'|'\r'))* ('\n'|'\r'('\n')?) { SKIP(); }
  ;

/** Whitespace (skip) */
WHITESPACE_SKIP
  : WHITESPACE+ { SKIP(); }
  ;
   
/** Identifiers */
IDENTIFIER
  : LETTER (LETTER | DIGIT | '?' | '_' )*
  ;

/** Case insensitive matches */
fragment A:('a'|'A');
fragment B:('b'|'B');
fragment C:('c'|'C');
fragment D:('d'|'D');
fragment E:('e'|'E');
fragment F:('f'|'F');
fragment G:('g'|'G');
fragment H:('h'|'H');
fragment I:('i'|'I');
fragment J:('j'|'J');
fragment K:('k'|'K');
fragment L:('l'|'L');
fragment M:('m'|'M');
fragment N:('n'|'N');
fragment O:('o'|'O');
fragment P:('p'|'P');
fragment Q:('q'|'Q');
fragment R:('r'|'R');
fragment S:('s'|'S');
fragment T:('t'|'T');
fragment U:('u'|'U');
fragment V:('v'|'V');
fragment W:('w'|'W');
fragment X:('x'|'X');
fragment Y:('y'|'Y');
fragment Z:('z'|'Z');  
  