%{
(*
 * This file is part of sally.
 * Copyright (C) 2016 SRI International.
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
 *)

  open Ast.Sal_ast
%}

/*
 * Parser for the simplified SAL language
 */

%token <string> FLOAT
%token <string> DECIMAL
%token <string> IDENT

%token CONTEXT
%token BEGIN
%token END
%token MODULE
%token INPUT
%token OUTPUT
%token GLOBAL
%token LOCAL
%token INVARIANT
%token INITIALIZATION
%token DEFINITION
%token TRANSITION
%token ARRAY
%token TYPE
%token OF
%token LEMMA
%token THEOREM

%token OPEN_PAR
%token CLOSE_PAR
%token OPEN_BRACKET
%token CLOSE_BRACKET
%token OPEN_BRACE
%token CLOSE_BRACE
%token COLUMN
%token SEMI_COLUMN
%token COMMA
%token ELLIPSIS
%token BAR
%token SATISFIES
%token NEXT
%token BOX
%token ARROW

%token LET IN
%token IF THEN ELSE ELSIF ENDIF
%token IFF XOR OR AND IMPLIES NOT
%token EQUAL DISEQUAL GT LT GE LE
%token FORALL EXISTS
%token PLUS MINUS TIMES DIV


%token EOF
%token LEX_ERROR

%start context

%type <Ast.Sal_ast.sal_context> context

%%

context:
| IDENT COLUMN CONTEXT EQUAL BEGIN declarations END
    { { ctx_name = $1; definitions = $6; } }
;

declarations:
| declaration SEMI_COLUMN declarations { $1::$3 }
|                                      { [] }
;

declaration:
| type_declaration       { $1 }
| constant_declaration   { $1 }
| function_declaration   { $1 }
| assertion              { $1 }
| module_declaration     { $1 }
;

type_declaration:
| IDENT COLUMN TYPE                 { Type_decl($1) }
| IDENT COLUMN TYPE EQUAL stype     { Type_def($1,$5) }
;

constant_declaration:
| IDENT COLUMN stype               { Constant_decl($1,$3) }
| IDENT COLUMN stype EQUAL expr    { Constant_def($1,$3,$5) }
;

function_declaration:
| IDENT OPEN_PAR var_declarations CLOSE_PAR COLUMN stype EQUAL expr 
   { Function_def($1,$3,$6,$8) }
;

assertion:
| IDENT COLUMN lemma module_name SATISFIES expr
    { Assertion($1,$3,$4,$6) }
;
lemma:
| LEMMA                              { Lemma }
| THEOREM                            { Theorem }
;
module_name:
| IDENT                              { $1 }
;

module_declaration:
| IDENT COLUMN MODULE EQUAL module_expression { Module_def($1,$5) }
;

/*
 * TYPES
 */
stype:
| simple_type                       { $1 }
| array_type                        { $1 }
| predicate_subtype                 { $1 }
;

simple_type:
| IDENT                                           { Base_type($1) }
| OPEN_BRACKET expr ELLIPSIS expr CLOSE_BRACKET   { Range($2,$4) }
| OPEN_BRACE enumlist CLOSE_BRACE                 { Enum($2) }
;

enumlist:
| IDENT enumlist_rest              { $1::$2 }
;

enumlist_rest:
| COMMA IDENT enumlist_rest         { $2::$3}
|                                   { [] }
;

array_type:
| ARRAY simple_type OF stype     { Array($2,$4) }
;

predicate_subtype:
| OPEN_BRACE IDENT COLUMN stype BAR expr CLOSE_BRACE     { Subtype($2,$4,$6) }
;


/*
 * VARIABLE DECLARATIONS
 */

/*
 * These are used in quantifiers, function definitions, and state variable declarations.
 * Example:  FORALL (x, y: int, z: bool) : expr
 */
var_declarations:
| var_decl var_decl_rest           { $1::$2 }
;
var_decl:
| identifiers COLUMN stype         { ($1,$3) }
;
identifiers:
| IDENT ident_list_rest            { $1::$2 }
;
ident_list_rest:
| COMMA IDENT ident_list_rest      { $2::$3 }
|                                  { [] }
;
var_decl_rest:
| COMMA var_decl var_decl_rest     { $2::$3 }
|                                  { [] }
;



/*
 * EXPRESSIONS
 */
/* 
 * The rules are derived from sal.g in sally/src/parsers/sal.
 * with fixes to avoid shift/reduce conflicts.
 *
 * We distinguish between right-most and other expressions.
 * 
 * SAL does not require parenthesese around quantified expressions
 * that occur in right-most position.
 * For example, both
 *
 *       A AND (B OR FORALL ...)
 *  and  A AND (B OR (FORALL ...))
 *
 * are allowed.
 *
 * In the grammar, r_expression means right-most.
 */
expr:
| let_expression    { $1 }
;

let_expression:
| LET let_declarations IN let_expression { Let($2,$4) }
| iff_r_expression     { $1 }
;

let_declarations:
| let_decl let_decl_rest     { $1::$2 }
;

let_decl:
| IDENT COLUMN stype EQUAL expr     { ($1,$3,$5) }
;

let_decl_rest:
| COMMA let_decl let_decl_rest     { $2::$3 }
|                                  { [] }
;


iff_r_expression:
| implies_expression IFF implies_r_expression   { Iff($1,$3) }
| implies_r_expression                          { $1 }
;


implies_r_expression:
| or_expression IMPLIES or_r_expression     { Implies($1,$3) }
| or_r_expression                           { $1 }
;

implies_expression:
| or_expression IMPLIES or_expression     { Implies($1,$3) }
| or_expression                           { $1 }
;

or_r_expression:
| or_expression OR and_r_expression       { Or($1,$3) }
| or_expression XOR and_r_expression      { Xor($1,$3) }
| and_r_expression                        { $1 }
;

or_expression:
| or_expression OR and_expression       { Or($1,$3) }
| or_expression XOR and_expression      { Xor($1,$3) }
| and_expression                        { $1 }
;

and_r_expression:
| and_expression AND not_r_expression     { And($1,$3) }
| not_r_expression                        { $1 }
;

and_expression:
| and_expression AND not_expression     { And($1,$3) }
| not_expression                        { $1 }
;

not_r_expression:
| NOT eq_r_expression     { Not($2) }
| eq_r_expression         { $1 }
;

not_expression:
| NOT eq_expression     { Not($2) }
| eq_expression         { $1 }
;

eq_r_expression:
| eq_expression         { $1 }
| q_expression          { $1 }
;

q_expression:
| EXISTS OPEN_PAR var_declarations CLOSE_PAR COLUMN iff_r_expression
    { Exists($3,$6) }
| FORALL OPEN_PAR var_declarations CLOSE_PAR COLUMN iff_r_expression
    { Forall($3,$6) }
;

eq_expression:
| rel_expression EQUAL rel_expression        { Eq($1,$3) }
| rel_expression DISEQUAL rel_expression     { Neq($1,$3) }
| rel_expression                             { $1 }
;

rel_expression:
| additive_expression GE additive_expression     { Ge($1,$3) }
| additive_expression LE additive_expression     { Le($1,$3) }
| additive_expression GT additive_expression     { Gt($1,$3) }
| additive_expression LT additive_expression     { Lt($1,$3) }
| additive_expression                            { $1 }
;

additive_expression:
| additive_expression PLUS multiplicative_expression      { Add($1,$3) }
| additive_expression MINUS multiplicative_expression     { Sub($1,$3) }
| multiplicative_expression                               { $1 }
;

multiplicative_expression:
| multiplicative_expression TIMES unary_expression    { Mul($1,$3) }
| multiplicative_expression DIV unary_expression      { Div($1,$3) }
| unary_expression                                    { $1 }
;

unary_expression:
| MINUS simple_expression     { Opp($2) }
| PLUS simple_expression      { $2 }
| simple_expression           { $1 }
;

simple_expression:
| number                      { $1 }
| function_call               { $1 }
| array_access                { $1 }
| if_then_else                { $1 }
| array_literal               { $1 }
| set_literal                 { $1 }
| OPEN_PAR expr CLOSE_PAR     { $2 }
;

number:
| FLOAT       { Float(float_of_string $1) }
| DECIMAL     { Decimal(int_of_string $1) }
;

var_or_next:
| IDENT       { Ident($1) }
| IDENT NEXT  { Ident($1 ^ "'") }
;

function_call:
| IDENT OPEN_PAR expr_list CLOSE_PAR     { Funcall($1,$3) }
;
expr_list:
| expr exprlist_rest           { $1::$2 }
;
exprlist_rest:
| COMMA expr exprlist_rest     { $2::$3 }
|                              { [] }
;

array_access:
| array_access OPEN_BRACKET expr CLOSE_BRACKET     { Array_access($1, $3) }
| var_or_next                                      { $1 }
;

if_then_else:
| IF expr THEN expr elsif ELSE expr ENDIF     { Cond(($2,$4)::$5,$7) }
;
elsif:
| ELSIF expr THEN expr elsif     { ($2,$4)::$5 }
|                                { [] }
;

array_literal:
| OPEN_BRACKET OPEN_BRACKET IDENT COLUMN simple_type CLOSE_BRACKET expr CLOSE_BRACKET  
   { Array_literal($3,$5,$7) }
;

set_literal:
| OPEN_BRACE IDENT COLUMN stype BAR expr CLOSE_BRACE
   { Set_literal($2,$4,$6) }
;


/*
 * MODULES
 */
module_expression:
| base_module     { $1 }
;

base_module:
| BEGIN state_var_declarations init_clause definition_clause 
     invariant_clause transition_clause END     
     { { state_vars = List.rev $2;
	 initialization = $3;
	 definition = $4;
	 invariant = $5;
	 transition = $6;
       }
     }
;

state_var_declarations:
| state_var_declarations module_var_declaration         { $2::$1 } 
| module_var_declaration                                { [$1] }
;

module_var_declaration:
| INPUT  var_declarations    { (Input,$2) }
| OUTPUT var_declarations    { (Output,$2) }
| LOCAL  var_declarations    { (Local,$2) }
| GLOBAL var_declarations    { (Global,$2) }
;

init_clause:
| INITIALIZATION assignments { $2 }
|                            { [] }
;

definition_clause:
| DEFINITION assignments     { $2 }
|                            { [] }
;

invariant_clause:
| INVARIANT expr             { Some($2) }
|                            { None }
;

transition_clause:
| TRANSITION assignments                                 { Assignments($2) }
| TRANSITION OPEN_BRACKET guarded_commands CLOSE_BRACKET { GuardedCommands(List.rev $3) }
|                                                        { NoTransition }
;

assignments:
| assignment SEMI_COLUMN             { [$1] }
| assignment SEMI_COLUMN assignments { $1::$3 }
;

assignment:
| array_access EQUAL expr         { Assign($1,$3) }
| var_or_next IN set_literal     { Member($1, $3) }
;

guarded_commands:
| guarded_command                       { [$1] }
| guarded_commands BOX guarded_command  { $3::$1 }
;

guarded_command:
| expr ARROW assignments           { Guarded($1,$3) }
| expr ARROW                       { Guarded($1,[]) }
| ELSE ARROW assignments           { Default($3) }
| ELSE ARROW                       { Default([]) }
;
