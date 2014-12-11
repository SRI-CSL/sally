grammar sal;

options {
  // C output for antlr
  language = 'C'; 
  // Lookahead 
  k = 2;
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
  ; 

context 
  : identifier (LC parameters RC)? CLN 'CONTEXT' EQ contextbody EOF  
  ;

parameters 
  : typedecls? SEMI varDecls?
  ;

contextbody 
  : 'BEGIN' declarations 'END' 
  ;

declarations 
 : (declaration SEMI)+ 
 ;

declaration 
  : (identifier CLN 'TYPE')                     => typeDeclaration 
  | (identifier CLN assertionForm)              => assertionDeclaration
  | (identifier CLN 'CONTEXT')                  => contextDeclaration 
  | (identifier (LB varDecls RB)? CLN 'MODULE') => moduleDeclaration
  | constantDeclaration
  ;

constantDeclaration 
  : identifier (LP varDecls RP)? CLN type (EQ expression)?
  ;

typeDeclaration 
  : identifier CLN 'TYPE' (EQ typedefinition)?
  ;

assertionDeclaration 
  : identifier CLN assertionForm assertionExpression
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
  : ((AND|OR|IMPLIES|IFF) LP assertionExpression COMMA assertionExpression RP)
  | (NOT LP assertionExpression RP)
  ;

quantifiedAssertion 
  : ('FORALL' | 'EXISTS') LP varDecls RP CLN assertionExpression
  ;

moduleAssertion 
  :  module moduleModels 
  ;

moduleModels 
  : '|-' expression 
  ;

contextDeclaration 
  : identifier CLN 'CONTEXT' EQ contextName
  ;

contextName 
  : identifier (LC actualparameters RC)?
  ;

moduleDeclaration 
  : identifier (LB varDecls RB)? CLN 'MODULE' EQ module
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
  ;

typeName 
  : name
  ;

scalartype
  : LC scalarElements RC
  ;

scalarElements 
  : scalarElement (COMMA scalarElement)* 
  ;

scalarElement 
  : identifier;

datatype
  : 'DATATYPE' constructors 'END'
  ;

constructors 
  : constructor (COMMA constructor)* 
  ;

constructor
  : identifier (LP accessors RP)?
  ;

accessors 
  : accessor (COMMA accessor)* 
   ;

accessor 
  : identifier CLN type 
  ;

indextype 
  : integertype
  | name 
  | subrange 
  ;

integertype
  : INTEGER
  ;

name 
  : (fullname) => fullname
  | identifier
  ;

fullname
  : identifier (LC actualparameters RC )? BANG identifier
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
  : LB bound DOTDOT bound RB
  ;

arraytype 
  : 'ARRAY' indextype 'OF' type
  ;

tupletype 
  : LB type (COMMA type)+ RB
  ;

functiontype 
  : LB type ARROW type RB
  ;

recordtype
  : RECS fielddeclaration (COMMA fielddeclaration)* RECE
  ;

fielddeclaration 
  : identifier CLN type
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
  : relexpression ((EQ | NEQ) relexpression)?
  ;

relexpression 
  : infixapplication ((GT | GE | LT | LE) infixapplication)?
  ;

infixapplication 
  : additiveexpression (IDENTIFIER additiveexpression)*
  ;

additiveexpression 
  : multiplicativeexpression ((PLUS | MINUS) multiplicativeexpression)*
  ;

multiplicativeexpression 
  : unaryexpression ((MULT | DIV) unaryexpression)*
  ;

unaryexpression 
  : (MINUS unaryexpression)
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
  : identifier QUOTE 
  ;

lambdaabstraction 
  : 'LAMBDA' LP varDecls RP CLN expression
  ;

quantifiedexpression 
  : 'FORALL' LP varDecls RP CLN expression
  | 'EXISTS' LP varDecls RP CLN expression 
  ;

letexpression 
  : 'LET' letdeclarations 'IN' expression
  ;

letdeclarations 
  : letDeclaration (COMMA letDeclaration)*
  ;

letDeclaration 
  : identifier CLN type EQ expression
  ;

arrayliteral 
  : LB LB indexVarDecl RB expression RB
  ;

recordliteral
  : RECEXS recordentry (COMMA recordentry)* RECEXE
  ;

recordentry 
  : identifier ASSIGN expression
  ;

tupleLiteral 
  : LP expressions RP 
  ;

setexpression 
  : (setpredexpression) => setpredexpression
  | setlistexpression
  ;

setpredexpression
  : LC identifier CLN type VBAR expression RC
  ;

setlistexpression 
  : LC (expression (COMMA expression)*)? RC 
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
  : LP expressions RP 
  ;

expressions 
  : expression (COMMA expression )* 
  ;

updatesuffix 
  : 'WITH' update
  ;

update 
  : updateposition ASSIGN expression 
  ;

updateposition 
  : (argument | access)+
  ;

indexVarDecl 
  : identifier CLN indextype
  ;

identifiers 
  : identifier (COMMA identifier)* 
  ;

pidentifiers 
  : identifiers;

varDecl 
  : identifiers CLN type 
  ;

varDecls 
  : varDecl (COMMA varDecl)*
  ;

/* The Transition Language */

lhs 
  : identifier QUOTE? access*
  ;

access 
  : LB expression RB 
  | ( DOT identifier) => DOT identifier
  | DOT numeral
  ;

rhsexpression 
  : EQ expression
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
  : LP 'FORALL' LP varDecls RP CLN definitions RP 
  ;

definition 
  : simpleDefinition 
  | foralldefinition 
  ;

definitions :
  definition (SEMI definition)* ;

guard 
  : expression
  ;

assignments 
  : simpleDefinition (SEMI simpleDefinition)*
  ;

guardedcommand 
  : guard LONGARROW assignments?
  ;

/* The Module Language */

module 
  : basicmodule ((ASYNC|SYNC) basicmodule)*
  ;

basicmodule 
  : basemodule
  | (LP SYNC)   => multisynchronous
  | (LP ASYNC)  => multiasynchronous
  | hiding
  | newoutput
  | renaming
  | withModule
  | modulename
  | observeModule
  | (LP module RP) 
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
  : LP SYNC LP indexVarDecl RP CLN module RP
  ;

multiasynchronous 
  : LP ASYNC LP indexVarDecl RP CLN module RP
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
  : rename (COMMA rename)*
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
  : (LB expressions RB)?
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
  : 'INITIALIZATION' definitionorcommand (SEMI definitionorcommand)*
  ;

transdecl 
  : 'TRANSITION' definitionorcommand (SEMI definitionorcommand)*
  ; 

labeledcommand 
  : identifier CLN guardedcommand
  ;

namedcommand 
  : (identifier CLN) => labeledcommand
  | guardedcommand 
  ;

multicommand 
  : LP ASYNC LP varDecls RP CLN somecommand RP 
  ;

somecommand 
  : (namedcommand) => namedcommand 
  | multicommand 
  ;

somecommands 
  : somecommand (ASYNC somecommand)
  ;

definitionorcommand
  : definition
  | (LB somecommands RB)
  ;

newVarDecl 
  : inputdecl 
  | outputdecl 
  | globaldecl
  ;

newVarDecls 
  : newVarDecl (SEMI newVarDecl)*
  ;

typedecls 
  : identifiers CLN 'TYPE';

actualparameters 
  : actualtypes? SEMI actualexprs?
  ;

actualtypes 
  : type (COMMA type)*
  ;

actualexprs 
  : expression (COMMA expression)*
  ;

identifier 
  : IDENTIFIER
  ;

numeral 
  : NUMERAL
  ;

// Letters 
ALPHA: ('a'..'z'|'A'..'Z');


// Whitespace
WS : (' ' | '\t' | '\n' | '\r' | '\f')+ { SKIP(); }
   ;

// Single-line comments
SL_COMMENT
  : '%' (~('\n'|'\r'))* ('\n'|'\r'('\n')?) { SKIP(); }
  ;

LP: '(';
RP: ')';
LB: '[';
RB: ']';
LC: '{';
RC: '}';
RECS: '[#';
RECE: '#]';
RECEXS: '(#';
RECEXE: '#)';
DOT: '.';
COMMA: ',';
CLN: ':';
SEMI: ';';
BANG: '!';
VBAR: '|';
PERCENT: '%';
HASH: '#';
QMARK: '?';
NUMERAL: ('0'..'9')+;
ALPHANUM: (ALPHA|'0'..'9'|'?'|'_');
AND: 'AND';
OR: 'OR';
XOR: 'XOR';
NOT: 'NOT';
ASSIGN: ':=' ;
DOTDOT: '..' ;
QUOTE: '\'' ;
IMPLIES: '=>' ;
EQ: '=' ;
DIV: '/' ;
NEQ: '/=' ;
SYNC: '||' ;
ASYNC: '[]';
PLUS: '+';
LONGARROW: '-->' ;
ARROW: '->' ;
MINUS: '-' ;
MULT : '*';

// Relational operators
IFF : '<=>' ;
LE : '<=' ;
LT : '<' ;
GE : '>=' ;
GT : '>' ;

REAL : 'REAL' | 'real';
NZREAL : 'NZREAL' | 'nzreal';
INTEGER : 'INTEGER' | 'integer';
NZINTEGER : 'NZINTEGER' | 'nzinteger';
NATURAL : 'NATURAL' | 'natural';
BOOLEAN : 'BOOLEAN' | 'boolean';

/* From the language description: an identifier is taken to be any string
of ASCII characters that is not a numeral and does not contain spaces,
parentheses, brackets, braces, the percent sign, equality, comma, period,
colon, semi-colon, and hash.  */

// IDENTIFIER
IDENTIFIER: (ALPHA (ALPHA|'0'..'9'|'?'|'_')*);

// The only purpose of the following line is to allow the user to use the double quote character inside comments.
DOUBLEQUOTE : '\"';

