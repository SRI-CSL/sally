grammar sal;

options {
  // C output for antlr
  language = 'C'; 
}
 
@parser::includes {
  #include <string>
  #include "parser/command.h"
  #include "parser/sal/sal_state.h"
  using namespace sal2;
}

@parser::postinclude {
  #define STATE (ctx->pState)
}


@parser::context
{
  /** The sal2 part of the parser state */
  parser::sal_state* pState;
}

command returns [parser::command* cmd = 0]
  : context
  | EOF
  ; 

context 
  : identifier ('{' parameters '}')? ':' 'CONTEXT' '=' contextbody   
  ;

parameters 
  : type_declarations? ';' var_declarations?
  ;

contextbody 
  : 'BEGIN' declarations 'END' 
  ;

declarations 
 : (declaration ';')+ 
 ;

declaration 
  : type_declaration 
  | assertion_declaration
  | context_declaration 
  | module_declaration
  | constant_declaration
  ;

constant_declaration 
  : identifier ('(' var_declarations ')')? ':' type ('=' expression)?
  ;

type_declaration 
  : identifier ':' 'TYPE' ('=' type_definition)?
  ;

assertion_declaration 
  : identifier ':' assertion_form assertion_expression
  ;

assertion_form 
  : ('OBLIGATION' | 'CLAIM' | 'LEMMA' | 'THEOREM')
  ;

assertion_expression 
  : module '|-' expression
  ;

assertion_proposition 
  : ((AND|OR|IMPLIES|IFF) '(' assertion_expression ',' assertion_expression ')')
  | (NOT '(' assertion_expression ')')
  ;

quantified_assertion 
  : ('FORALL' | 'EXISTS') '(' var_declarations ')' ':' assertion_expression
  ;

context_declaration 
  : identifier ':' 'CONTEXT' '=' context_name
  ;

context_name 
  : identifier ('{' actual_parameters '}')?
  ;

module_declaration 
  : identifier ('[' var_declarations ']')? ':' 'MODULE' '=' module
  ;

// Types

type_definition 
  : type 
  | scalar_type 
  | datatype 
  ;

type
  : type_name
  | basic_type
  | (subrange_type)     => subrange_type
  | array_type
  | (function_type) => function_type
  | tuple_type
  | record_type
  | subtype
  ;

subtype
  : '{' identifier ':' type '|' expression '}'
  ;

type_name 
  : name
  ;

scalar_type
  : '{' scalar_elements '}'
  ;

scalar_elements 
  : identifier (',' identifier)* 
  ;

datatype
  : 'DATATYPE' constructors 'END'
  ;

constructors 
  : constructor (',' constructor)* 
  ;

constructor
  : identifier ('(' accessors ')')?
  ;

accessors 
  : accessor (',' accessor)* 
  ;

accessor 
  : identifier ':' type 
  ;

index_type 
  : 'BOOLEAN'
  | 'NATURAL'
  | 'INTEGER'
  | name 
  | subrange_type 
  ;

name 
  : (qualified_name) => qualified_name
  | identifier
  ;

qualified_name
  : identifier ('{' actual_parameters '}' )? '!' identifier
  ;

basic_type 
  : 'BOOLEAN'
  | 'REAL' 
  | 'INTEGER' 
  | 'NZINTEGER' 
  | 'NATURAL'
  | 'NZREAL' 
  ;

bound 
  : expression 
  | '_'
  ;

subrange_type 
  : '[' bound '..' bound ']'
  ;

array_type 
  : 'ARRAY' index_type 'OF' type
  ;

tuple_type 
  : '[' type (',' type)+ ']'
  ;

function_type 
  : '[' type '->' type ']'
  ;

record_type
  : '[#' field_declaration (',' field_declaration)* '#]'
  ;

field_declaration 
  : identifier ':' type
  ;

// Expressions

expression 
  : iff_expression
  ;

iff_expression 
  : implies_expression (IFF implies_expression)?
  ;

implies_expression 
  : or_expression (IMPLIES or_expression)?
  ;

or_expression 
  : and_expression ((OR | XOR) and_expression)*
  ;

and_expression 
  : not_expression (AND not_expression)*
  ;

not_expression 
  : NOT not_expression
  | eq_expression 
  ;

eq_expression 
  : rel_expression (('=' | '/=') rel_expression)?
  ;

rel_expression 
  : infix_application (('>' | '>=' | '<' | '<=') infix_application)?
  ;

infix_application 
  : additive_expression (IDENTIFIER additive_expression)?
  ;

additive_expression 
  : multiplicative_expression  (('+' | '-') multiplicative_expression)*
  ;

multiplicative_expression 
  : unary_expression (('*' | '/') unary_expression)*
  ;

unary_expression 
  : ('-' unary_expression)
  | simpleExpression
  ;

simpleExpression 
  : expression_prefix (expression_suffix)*
  ;

name_expression 
  : name
  ;

expression_prefix 
  : next_variable
  | name_expression
  | numeral
  | lambda_expression
  | quantified_expression
  | let_expression
  | array_literal 
  | record_literal 
  | tuple_literal 
  | set_expression
  | conditional
  ;

expression_suffix 
  : argument
  | access
  | updatesuffix
  ;

next_variable 
  : identifier '\'' 
  ;

lambda_expression 
  : 'LAMBDA' '(' var_declarations ')' ':' expression // TODO: recursion here
  ;

quantified_expression 
  : 'FORALL' '(' var_declarations ')' ':' expression // TODO: recursion here
  | 'EXISTS' '(' var_declarations ')' ':' expression // TODO: recursion here
  ;

let_expression 
  : 'LET' let_declarations 'IN' expression
  ;

let_declarations 
  : let_declaration (',' let_declaration)*
  ;

let_declaration 
  : identifier ':' type '=' expression
  ;

array_literal 
  : '[' '[' index_var_declaration ']' expression ']'
  ;

record_literal
  : '(#' record_entry (',' record_entry)* '#)'
  ;

record_entry 
  : identifier ':=' expression
  ;

tuple_literal 
  : '(' expressions ')' 
  ;

set_expression 
  : set_predicate_expression
  | set_list_expression
  ;

set_predicate_expression
  : '{' identifier ':' type '|' expression '}'
  ;

set_list_expression 
  : '{' (expression (',' expression)*)? '}' 
  ;

conditional 
  : 'IF'   expression
    'THEN' expression
    (elsif)*   
    'ELSE' expression
    'ENDIF'
  ;

elsif 
  : 'ELSIF' expression 'THEN' expression 
  ;
  
argument
  : '(' expressions ')' 
  ;

expressions 
  : expression (',' expression )* 
  ;

updatesuffix 
  : 'WITH' update
  ;

update 
  : updateposition ':=' expression 
  ;

updateposition 
  : (argument | access)+
  ;

index_var_declaration 
  : identifier ':' index_type
  ;

identifiers 
  : identifier (',' identifier)* 
  ;

pidentifiers 
  : identifiers;

var_declaration 
  : identifiers ':' type 
  ;

var_declarations 
  : var_declaration (',' var_declaration)*
  ;

/* The Transition Language */

lhs 
  : identifier '\''? access*
  ;

access 
  : '[' expression ']' 
  | '.' identifier
  | '.' numeral
  ;

rhsexpression 
  : '=' expression
  ;

rhsselection 
  : 'IN' expression
  ;

rhsdefinition 
  : rhsexpression 
  | rhsselection 
  ;

simple_definition 
  : lhs rhsdefinition
  ;

foralldefinition 
  : '(' 'FORALL' '(' var_declarations ')' ':' definitions ')' 
  ;

definition 
  : simple_definition 
  | foralldefinition 
  ;

definitions :
  definition (';' definition)* ';'?;

guard 
  : expression
  ;

assignments 
  : simple_definition (';' simple_definition)* ';'?
  ;

guardedcommand 
  : guard '-->' assignments?
  | 'ELSE' '-->' assignments? 
  ;

/* The Module Language */

module 
  : basic_module ((ASYNC|SYNC) basic_module)*
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
  : 'BEGIN' base_declarations 'END'
  ;

base_declarations 
  : (base_declaration)* 
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
  : '(' SYNC '(' index_var_declaration ')' ':' module ')'
  ;

multi_asynchronous 
  : '(' ASYNC '(' index_var_declaration ')' ':' module ')'
  ;

hiding
  : 'LOCAL' pidentifiers 'IN' module
  ;

new_output 
  : 'OUTPUT' pidentifiers 'IN' module
  ;

renaming 
  : 'RENAME' renames 'IN' module
  ;

renames 
  : rename (',' rename)*
  ;

rename 
  : lhs 'TO' lhs
  ;

with_module
  : 'WITH' new_var_declarations module
  ;

module_name 
  : name module_actuals
  ;

module_actuals 
  : ('[' expressions ']')?
  ;

observe_module 
  : 'OBSERVE' module 'WITH' module
  ;

/* Declarations within modules */

input_declaration 
  : 'INPUT' var_declarations
  ;

output_declaration 
  : 'OUTPUT' var_declarations
  ;

global_declaration 
  : 'GLOBAL' var_declarations
  ;

local_declaration
  : 'LOCAL' var_declarations
  ;

definition_declaration
  : 'DEFINITION' definitions
  ;

invariant_declaration
  : 'INVARIANT' expression
  ;

init_formula_declaration 
  : 'INITFORMULA' expression
  ;

init_declaration 
  : 'INITIALIZATION' definition_or_command (';' definition_or_command)* ';'?
  ;

transition_declaration 
  : 'TRANSITION' definition_or_command (';' definition_or_command)*
  ; 

multicommand 
  : '(' ASYNC '(' var_declarations ')' ':' some_command ')' 
  ;

some_command 
  : (identifier ':') ? guardedcommand 
  | (identifier ':') ? multicommand 
  ;

some_commands 
  : some_command (ASYNC some_command)*
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

new_var_declarations 
  : new_var_declaration (';' new_var_declaration)*
  ;

type_declarations 
  : identifiers ':' 'TYPE';

actual_parameters 
  : actual_types? ';' actual_expressions?
  ;

actual_types 
  : type (',' type)*
  ;

actual_expressions 
  : expression (',' expression)*
  ;

identifier 
  : IDENTIFIER
  ;

numeral 
  : NUMERAL
  ;

/** Numerals */
NUMERAL: DIGIT+;
 
// Boolean operators
AND: 'AND';
OR: 'OR';
XOR: 'XOR';
NOT: 'NOT';
IMPLIES: '=>' ;
IFF : '<=>' ;

// Combination operators
SYNC: '||' ;
ASYNC: '[]';

/** Special symbols */
fragment
SPECIAL_SYMBOL : '(' | ')' | '[' | ']' | '{' | '}' | '%' | ',' | '.' | ';' | '\'' | '!' | '#' | '?' | '_';

/** Letters */ 
fragment                                     
LETTER : 'a'..'z' | 'A'..'Z';

/** Digits */
fragment   
DIGIT : '0'..'9';

/** Whitespace characters */
fragment
WHITESPACE : ' ' | '\t' | '\n' | '\r' | '\f';

/** Opchar: anything not a letter, digit, special symbol, or whitespace */
fragment
OPCHAR : ~(LETTER | DIGIT | SPECIAL_SYMBOL | WHITESPACE);

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
  | OPCHAR+
  ;
