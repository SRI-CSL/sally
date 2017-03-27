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
  #include "command/command.h"
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
command returns [cmd::command* cmd = 0]
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
  : identifier
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
  : implies_term (OP_IFF implies_term)*
  ;

implies_term 
  : or_term (OP_IMPLIES or_term)*
  ;

or_term 
  : and_term (KW_OR and_term)*
  ; 
  
and_term 
  : xor_term (KW_AND xor_term)*
  ;

xor_term 
  : unary_bool_term (KW_XOR unary_bool_term)*
  ;

unary_bool_term 
  : NOT unary_bool_term
  | KW_FORALL '(' var_declaration_list ')' ':' unary_bool_term
  | KW_EXISTS '(' var_declaration_list ')' ':' unary_bool_term   
  | eq_term 
  ;

eq_term 
  : rel_term ((OP_EQ | OP_NEQ) rel_term)?
  ;

rel_term 
  : additive_term ((OP_GT | OP_GEQ | OP_LT | OP_LEQ) additive_term)?
  ;

/** Associative reading, evaluate from left to right. */
additive_term 
  : multiplicative_term ((OP_ADD | OP_SUB) multiplicative_term)*
  ;

/** Associative reading, evaluate from left to right. */
multiplicative_term 
  : unary_nonboolean_term ((OP_MUL | OP_DIV | KW_MOD | KW_DIV) unary_nonboolean_term)*
  ;

unary_nonboolean_term 
  : OP_SUB unary_nonboolean_term
  | update_term
  ;

update_term 
  : base_term (KW_WITH term_access+ ':=' base_term)*
  ;

/** 
 * Base term is a non-breakable unit with potential let declaration ahead of it.
 */
base_term 
  : KW_LET let_declarations KW_IN base_term
  | base_term_prefix base_term_suffix* 
  ;

base_term_prefix 
  : identifier '\''?
  | rational_constant
  | '[' '[' index_var_declaration ']' term ']'
  | '(#' record_entry (',' record_entry)* '#)' 
  | '(' term_list ')' 
  | conditional_term
  ;

conditional_term 
  : KW_IF   term
    KW_THEN term
    ('ELSIF' term KW_THEN term)*   
    KW_ELSE term
    KW_ENDIF
  ;

base_term_suffix 
  : term_argument
  | term_access
  ;

let_declarations 
  : let_declaration (',' let_declaration)*
  ;

let_declaration 
  : identifier (':' type)? '=' term
  ;

record_entry 
  : identifier ':=' term
  ;

set_term 
  : '{' identifier ':' type '|' term '}'
  | '{' (term (',' term)*)? '}'
  ;

term_argument
  : '(' term_list ')' 
  ;

term_list 
  : term (',' term )* 
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
  : identifier '\''? term_access*
  ;

term_access 
  : '[' term ']' 
  | '.' identifier
  ;

rhs_definition 
  : OP_EQ term 
  | KW_IN set_term 
  ;

simple_definition 
  : lvalue rhs_definition
  ;

forall_definition 
  : '(' KW_FORALL '(' var_declaration_list ')' ':' definition_list ')' 
  ;

/**
 * Definitions are the basic constructs used to build up the invariants, 
 * initializations, and transitions of a module. Definitions are used to specify 
 * the trajectory of variables in a computation by providing constraints on the 
 * controlled variables in a transition system. For variables ranging over 
 * aggregate data structures like records or arrays, it is possible to define 
 * each component separately. For example,
 *   
 *  x’ = x + 1
 * 
 * simply increments the state variable x, where x’ is the newstate of the 
 * variable,
 *  
 *  y’[i] = 3
 * 
 * sets the new state of the array y to be 3 at index i, and to remain unchanged
 * on all other indices, and
 *
 *  z.foo.1[0] = y
 * 
 * constrains state variable z, which is a record whose foo component is a 
 * tuple, whose first component in turn is an array of the same type as y.
 */
definition 
  : simple_definition 
  | forall_definition 
  ;

definition_list
  : definition (';' definition)* ';'?
  ;

assignments 
  : simple_definition (';' simple_definition)* ';'?
  ;

/** 
 * Each guarded command consists of a guard formula and an assignment part. The 
 * guard is a boolean expression in the current controlled (local, global, and 
 * output) variables and current and next state input variables. The assignment 
 * part is a list of equalities between a left-hand side next state variable and 
 * a right-hand side expression in current and next state variables.
 */
guarded_command 
  : term '-->' assignments?
  | KW_ELSE '-->' assignments? 
  ;

/* The Module Language */

/** 
 * A module is a self-contained specification of a transition system in SAL. 
 * Modules can be independently analyzed for properties and composed 
 * synchronously or asynchronously.
 */
module 
  : synchronous_module_composition 
  ;  

/**
 * The semantics of synchronous composition is that the module M1 || M2 
 * consists of:
 * - The initializations are the combination of initializations.
 * - The transitions are the combination of the individual transitions.
 * - The definitions are the union of the definition.
 * - The initializations are the pairwise combination of the initializations. 
 * - Two guarded initializations are combined by conjoining the guards and by 
 *   taking the union of the assignments. 
 */
synchronous_module_composition
  : asynchronous_module_composition (OP_SYNC asynchronous_module_composition)*
  ;  

/**
 * The semantics of asynchronous composition of two modules is given by the 
 * conjunction of the initializations, and the interleaving of the transitions 
 * of the two modules.
 */
asynchronous_module_composition
  : unary_module_modifier (OP_ASYNC unary_module_modifier)*
  ; 
  
/** Prefix module operations */
unary_module_modifier
  : OP_SYNC '(' index_var_declaration ')' ':' unary_module_modifier
  | OP_ASYNC '(' index_var_declaration ')' ':' unary_module_modifier
  | KW_LOCAL pidentifier_list KW_IN unary_module_modifier
  | KW_OUTPUT pidentifier_list KW_IN unary_module_modifier
  | KW_RENAME rename_list KW_IN unary_module_modifier
  | KW_WITH new_var_declaration_list unary_module_modifier
  | KW_OBSERVE module KW_WITH unary_module_modifier
  | module_base
  ;

/** The base of the module expressions */
module_base
  : module_name
  | base_module
  | ('(' module ')') 
  ;

/**
 * A BaseModule identifies the pairwise distinct sets of input, output, global, 
 * and local variables. This characterizes the state of the module. Base modules 
 * also may consist of several sections that can be given in any order. There 
 * may, for example, be 3 distinct TRANSITION sections. In every case, it is the 
 * same as if there was a prescribed order, with each class of variable and 
 * section being the union of the individual declarations.
 */
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
  | invariant_declaration // TODO: maybe remove
  | init_formula_declaration 
  | initialization_declaration 
  | transition_declaration
  ;

rename_list 
  : rename (',' rename)*
  ;

rename 
  : lvalue KW_TO lvalue
  ;

module_name 
  : identifier module_actuals
  ;

module_actuals 
  : ('[' term_list ']')?
  ;

/* Declarations within modules */

/**
 * From the SAL manual:
 * 
 * The state type is defined by four pairwise disjoint sets of input, output, 
 * global, and local variables. The input and global variables are the observed 
 * variables of a module and the output, global, and local variables are the 
 * controlled variables of the module.
 *
 * TODO: Can the module change global variables?
 */


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

/**
 * Definitions appearing in the DEFINITION section(s) are treated as invariants
 * for the system. When composed with other modules, the definitions remain true
 * even during the transitions of the other modules. This section is usually 
 * used to define controlled variables whose values ultimately depend on the 
 * inputs, for example, a boolean variable that becomes true when the 
 * temperature goes above a specified value.
 */
definition_declaration
  : KW_DEFINITION definition_list
  ;

/**
 * The INITIALIZATION section(s) constrain the possible initial values for the 
 * local, global, and output declarations. Input variables may not be 
 * initialized. The INITIALIZATION section(s) determine a state predicate that 
 * holds of the initial state of the base module. Definitions and guarded 
 * commands appearing in the INITIALIZATION section must not contain any 
 * NextVariable occurrences, i.e., both sides of the defining equation must be 
 * current expressions.
 * 
 * Guards may refer to any variables, this acts as a form of postcondition when
 * controlled variables are involved. This is like backtracking: operationally a 
 * guarded initialization is selected, the assignments made, and if the 
 * assignments violate the guard the assignments are undone and a new guarded 
 * initialization is selected. 
 */
initialization_declaration 
  : KW_INITIALIZATION definition_or_command (';' definition_or_command)* ';'?
  ;

/**
 * The TRANSITION section(s) constrain the possible next states for the local,
 * global, and output declarations. As this is generally defined relative to the
 * previous state of the module, the transition section(s) determine a state 
 * relation. Input variables may not appear on the Lhs of any assignments. 
 * Guards may refer to any variables, even NextVariables. As with guarded 
 * initial transitions, guards involving NextVariables have to be evaluated 
 * after the assignments have been made, and if they are false the assignments 
 * must be undone and a new guarded transition selected.
 */
transition_declaration 
  : KW_TRANSITION definition_or_command (';' definition_or_command)* ';'?
  ; 
 
invariant_declaration
  : KW_INVARIANT term
  ;

init_formula_declaration 
  : KW_INITFORMULA term
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

rational_constant
  : NUMERAL ('.' NUMERAL)?
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
  