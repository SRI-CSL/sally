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
  : typedecls? ';' varDecls?
  ;

contextbody 
  : 'BEGIN' declarations 'END' 
  ;

declarations 
 : (declaration ';')+ 
 ;

declaration 
  : (identifier ':' 'TYPE')                       => typeDeclaration 
  | (identifier ':' assertionForm)                => assertionDeclaration
  | (identifier ':' 'CONTEXT')                    => contextDeclaration 
  | (identifier ('[' varDecls ']')? ':' 'MODULE') => moduleDeclaration
  | constantDeclaration
  ;

constantDeclaration 
  : identifier ('(' varDecls ')')? ':' type ('=' expression)?
  ;

typeDeclaration 
  : identifier ':' 'TYPE' ('=' typedefinition)?
  ;

assertionDeclaration 
  : identifier ':' assertionForm assertionExpression
  ;

assertionForm 
  : ('OBLIGATION' | 'CLAIM' | 'LEMMA' | 'THEOREM')
  ;

assertionExpression 
  : (AND | OR | IMPLIES | IFF | NOT) => assertionProposition
  | ('FORALL' | 'EXISTS')            => quantifiedAssertion
  | (module moduleModels)            => moduleAssertion
  | expression
  ;

assertionProposition 
  : ((AND|OR|IMPLIES|IFF) '(' assertionExpression ',' assertionExpression ')')
  | (NOT '(' assertionExpression ')')
  ;

quantifiedAssertion 
  : ('FORALL' | 'EXISTS') '(' varDecls ')' ':' assertionExpression
  ;

moduleAssertion 
  :  module moduleModels 
  ;

moduleModels 
  : '|-' expression 
  ;

contextDeclaration 
  : identifier ':' 'CONTEXT' '=' contextName
  ;

contextName 
  : identifier ('{' actualparameters '}')?
  ;

moduleDeclaration 
  : identifier ('[' varDecls ']')? ':' 'MODULE' '=' module
  ;

// Types

typedefinition 
  : type 
  | scalartype 
  | datatype 
  ;

type
  : basictype
  | typeName
  | (subrange)     => subrange
  | arraytype
  | (functiontype) => functiontype
  | tupletype
  | recordtype
  | subtype
  ;

subtype
  : '{' identifier ':' type '|' expression '}'
  ;

typeName 
  : name
  ;

scalartype
  : '{' scalarElements '}'
  ;

scalarElements 
  : scalarElement (',' scalarElement)* 
  ;

scalarElement 
  : identifier;

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

indextype 
  : BOOLEAN
  | NATURAL
  | INTEGER
  | name 
  | subrange 
  ;

name 
  : (fullname) => fullname
  | identifier
  ;

fullname
  : identifier ('{' actualparameters '}' )? '!' identifier
  ;

basictype 
  : REAL 
  | NZREAL 
  | INTEGER 
  | NZINTEGER 
  | NATURAL 
  | BOOLEAN
  ;

bound 
  : expression 
  ;

subrange 
  : '[' bound '..' bound ']'
  ;

arraytype 
  : 'ARRAY' indextype 'OF' type
  ;

tupletype 
  : '[' type (',' type)+ ']'
  ;

functiontype 
  : '[' type '->' type ']'
  ;

recordtype
  : '[#' fielddeclaration (',' fielddeclaration)* '#]'
  ;

fielddeclaration 
  : identifier ':' type
  ;

// Expressions

expression 
  : iffExpression
  ;

iffExpression 
  : impliesexpression (IFF impliesexpression)?
  ;

impliesexpression 
  : orexpression (IMPLIES orexpression)?
  ;

orexpression 
  : andexpression ((OR | XOR) andexpression)*
  ;

andexpression 
  : notexpression (AND notexpression)*
  ;

notexpression 
  : NOT notexpression
  | eqexpression 
  ;

eqexpression 
  : relexpression (('=' | '/=') relexpression)?
  ;

relexpression 
  : infixapplication (('>' | '>=' | '<' | '<=') infixapplication)?
  ;

infixapplication 
  : additiveexpression (IDENTIFIER additiveexpression)*
  ;

additiveexpression 
  : multiplicativeexpression  (('+' | '-') multiplicativeexpression)*
  ;

multiplicativeexpression 
  : unaryexpression (('*' | '/') unaryexpression)*
  ;

unaryexpression 
  : ('-' unaryexpression)
  | simpleExpression
  ;

simpleExpression 
  : expressionprefix (expressionSuffix)*
  ;

nameexpr 
  : name
  ;

expressionprefix 
  : (nextvariable) => nextvariable
  | nameexpr
  | numeral
  | lambdaabstraction
  | quantifiedexpression
  | letexpression
  | arrayliteral 
  | recordliteral 
  | tupleLiteral 
  | setexpression
  | conditional
  ;

expressionSuffix 
  : argument
  | access
  | updatesuffix
  ;

nextvariable 
  : identifier '\'' 
  ;

lambdaabstraction 
  : 'LAMBDA' '(' varDecls ')' ':' expression
  ;

quantifiedexpression 
  : 'FORALL' '(' varDecls ')' ':' expression
  | 'EXISTS' '(' varDecls ')' ':' expression 
  ;

letexpression 
  : 'LET' letdeclarations 'IN' expression
  ;

letdeclarations 
  : letDeclaration (',' letDeclaration)*
  ;

letDeclaration 
  : identifier ':' type '=' expression
  ;

arrayliteral 
  : '[' '[' indexVarDecl ']' expression ']'
  ;

recordliteral
  : '(#' recordentry (',' recordentry)* '#)'
  ;

recordentry 
  : identifier ':=' expression
  ;

tupleLiteral 
  : '(' expressions ')' 
  ;

setexpression 
  : (setpredexpression) => setpredexpression
  | setlistexpression
  ;

setpredexpression
  : '{' identifier ':' type '|' expression '}'
  ;

setlistexpression 
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

indexVarDecl 
  : identifier ':' indextype
  ;

identifiers 
  : identifier (',' identifier)* 
  ;

pidentifiers 
  : identifiers;

varDecl 
  : identifiers ':' type 
  ;

varDecls 
  : varDecl (',' varDecl)*
  ;

/* The Transition Language */

lhs 
  : identifier '\''? access*
  ;

access 
  : '[' expression ']' 
  | ( '.' identifier) => '.' identifier
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

simpleDefinition 
  : lhs rhsdefinition
  ;

foralldefinition 
  : '(' 'FORALL' '(' varDecls ')' ':' definitions ')' 
  ;

definition 
  : simpleDefinition 
  | foralldefinition 
  ;

definitions :
  definition (';' definition)* ;

guard 
  : expression
  ;

assignments 
  : simpleDefinition (';' simpleDefinition)* '?'?
  ;

guardedcommand 
  : guard '-->' assignments?
  | 'ELSE' '-->' assignments? 
  ;

/* The Module Language */

module 
  : basicmodule ((ASYNC|SYNC) basicmodule)*
  ;

basicmodule 
  : basemodule
  | ('(' SYNC)   => multisynchronous
  | ('(' ASYNC)  => multiasynchronous
  | hiding
  | newoutput
  | renaming
  | withModule
  | modulename
  | observeModule
  | ('(' module ')') 
  ;

basemodule
  : 'BEGIN' basedeclarations 'END'
  ;

basedeclarations 
  : (basedeclaration)* 
  ;

basedeclaration 
  : inputdecl 
  | outputdecl 
  | globaldecl 
  | localdecl 
  | defdecl 
  | invardecl
  | initfordecl 
  | initdecl 
  | transdecl
  ;

multisynchronous 
  : '(' SYNC '(' indexVarDecl ')' ':' module ')'
  ;

multiasynchronous 
  : '(' ASYNC '(' indexVarDecl ')' ':' module ')'
  ;

hiding
  : 'LOCAL' pidentifiers 'IN' module
  ;

newoutput 
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

withModule
  : 'WITH' newVarDecls module
  ;

modulename 
  : name moduleActuals
  ;

moduleActuals 
  : ('[' expressions ']')?
  ;

observeModule 
  : 'OBSERVE' module 'WITH' module
  ;

/* Declarations within modules */

inputdecl 
  : 'INPUT' varDecls
  ;

outputdecl 
  : 'OUTPUT' varDecls
  ;

globaldecl 
  : 'GLOBAL' varDecls
  ;

localdecl
  : 'LOCAL' varDecls
  ;

defdecl
  : 'DEFINITION' definitions
  ;

invardecl
  : 'INVARIANT' expression
  ;

initfordecl 
  : 'INITFORMULA' expression
  ;

initdecl 
  : 'INITIALIZATION' definitionorcommand (';' definitionorcommand)* ';'?
  ;

transdecl 
  : 'TRANSITION' definitionorcommand (';' definitionorcommand)*
  ; 

labeledcommand 
  : identifier ':' guardedcommand
  ;

namedcommand 
  : (identifier ':') => labeledcommand
  | guardedcommand 
  ;

multicommand 
  : '(' ASYNC '(' varDecls ')' ':' somecommand ')' 
  ;

somecommand 
  : (namedcommand) => namedcommand 
  | multicommand 
  ;

somecommands 
  : somecommand (ASYNC somecommand)*
  ;

definitionorcommand
  : definition
  | ('[' somecommands ']')
  ;

newVarDecl 
  : inputdecl 
  | outputdecl 
  | globaldecl
  ;

newVarDecls 
  : newVarDecl (';' newVarDecl)*
  ;

typedecls 
  : identifiers ':' 'TYPE';

actualparameters 
  : actualtypes? ';' actualexprs?
  ;

actualtypes 
  : type (',' type)*
  ;

actualexprs 
  : expression (',' expression)*
  ;

identifier 
  : IDENTIFIER
  ;

numeral 
  : NUMERAL
  ;

/** Whitespace (skip) */
WS : (' ' | '\t' | '\n' | '\r' | '\f')+ { SKIP(); }
   ;

/** Comments */
SL_COMMENT
  : '%' (~('\n'|'\r'))* ('\n'|'\r'('\n')?) { SKIP(); }
  ;

/** Numerals */
NUMERAL: ('0'..'9')+;
 
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

// Types
REAL      : 'REAL' | 'real';
NZREAL    : 'NZREAL' | 'nzreal';
INTEGER   : 'INTEGER' | 'integer';
NZINTEGER : 'NZINTEGER' | 'nzinteger';
NATURAL   : 'NATURAL' | 'natural';
BOOLEAN   : 'BOOLEAN' | 'boolean';

/** Identifiers */
IDENTIFIER: ALPHA (ALPHA|'0'..'9'|'?'|'_')*;

/** Letters */ 
fragment
ALPHA: 'a'..'z'|'A'..'Z';

