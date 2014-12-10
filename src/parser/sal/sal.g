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

context
  : identifier (LC parameters RC)? CLN "CONTEXT" EQ contextbody EOF  
  ;

parameters 
  : (typedecls)? SEMI (pvarDecls)?
  ;

pvarDecls 
  : varDecls
  ;

contextbody 
  : "BEGIN" declarations "END" 
  ;

declarations 
 : (declaration SEMI)+ 
 ;

declaration 
  : (identifier CLN "TYPE")                     => typeDeclaration 
  | (identifier CLN assertionForm)              => assertionDeclaration
  | (identifier CLN "CONTEXT")                  => contextDeclaration 
  | (identifier (LB varDecls RB)? CLN "MODULE") => moduleDeclaration
  | constantDeclaration
  ;

constantDeclaration 
  : identifier (LP arDecls RP)? CLN type (EQ expression)?
  ;

typeDeclaration 
  : identifier CLN "TYPE" (EQ typedef)?
  ;

assertionDeclaration 
  : identifier CLN assertionForm assertionExpression
  ;

assertionForm 
  : ("OBLIGATION" | "CLAIM" | "LEMMA" | "THEOREM")
  ;

assertionExpression 
  : (AND | OR | IMPLIES | IFF | NOT)           => assertionProposition
  | ("FORALL" | "EXISTS")                      => quantifiedAssertion
  | (module (moduleModels | moduleImplements)) => moduleAssertion
  | expression
  ;

assertionProposition 
  : ((AND|OR|IMPLIES|IFF) LP assertionExpression COMMA assertionExpression RP)
  | (NOT LP assertionExpression RP)
  ;

quantifiedAssertion 
  : ("FORALL" | "EXISTS") LP pvarDecls RP CLN aexp : assertionExpression
  ;

moduleAssertion 
  :  module (moduleModels | moduleImplements)
  ;

moduleModels 
  : "|-" expression 
  ;

moduleImplements 
  : "IMPLEMENTS" module 
  ;

moduleRefines :
  "REFINES"! module ;

contextDeclaration 
  : identifier CLN "CONTEXT" EQ contextName
  ;

contextName 
  : identifier (LC actualparameters RC)?
  ;

moduleDeclaration 
  : identifier (LB varDecls RB)? CLN "MODULE" EQ module
  ;

// Types

typedef 
  : type 
  | scalartype 
  | datatype 
  ;

type
  : basictype
  | (module DOT)   => statetype
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
  : "DATATYPE" constructors "END"
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
  : identifier (LC actualparameters RC )? BANG id:identifier
  ;

basictype 
  : REAL 
  | NZREAL 
  | INTEGER 
  | NZINTEGER 
  | NATURAL 
  | BOOLEAN
  ;

unbounded 
  : UNBOUNDED
  ;

bound 
  : unbounded 
  | expression 
  ;

subrange 
  : LB bound DOTDOT bound RB
  ;

arraytype 
  : "ARRAY" indextype "OF" type
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

statetype 
  : module DOT "STATE" 
  ;

// Expressions

expression 
  : iffExpression
  ;

iffExpression 
  : impliesexpression
  (options {warnWhenFollowAmbig=false;}:
   op : IFF {setSimplePlaceAttribute(#op);} impliesexpression)*
  {#iffExpression = infix_to_prefix(#iffExpression);};

impliesexpression :
  orexpression
  (options {warnWhenFollowAmbig=false;}:
   op : IMPLIES {setSimplePlaceAttribute(#op);} orexpression)*
  {#impliesexpression = infix_to_prefix_right(#impliesexpression);};

orexpression :
  andexpression
  (options {warnWhenFollowAmbig=false;}:
   (  op1: OR {setSimplePlaceAttribute(#op1);} 
    | op2: XOR {setSimplePlaceAttribute(#op2);}) andexpression)*
  {#orexpression = infix_to_prefix(#orexpression);};

andexpression :
  notexpression
  (options {warnWhenFollowAmbig=false;}:
   op : AND {setSimplePlaceAttribute(#op);} notexpression)*
   {#andexpression = infix_to_prefix(#andexpression);};

notexpression :
  (op : NOT {setSimplePlaceAttribute(#op);} notexpression
  {#notexpression = #makeUnaryApplication(#notexpression);})
  | eqexpression ;

eqexpression :
  relexpression
  (options {warnWhenFollowAmbig=false;}:
   (  op1 : EQ {setSimplePlaceAttribute(#op1);} 
    | op2 : NEQ {setSimplePlaceAttribute(#op2);} ) relexpression)*
  {#eqexpression = infix_to_prefix(#eqexpression);};

relexpression :
  infixapplication
  (options {warnWhenFollowAmbig=false;}:
   (   op1 : GT {setSimplePlaceAttribute(#op1);}
     | op2 : GE {setSimplePlaceAttribute(#op2);}
     | op3 : LT {setSimplePlaceAttribute(#op3);}
     | op4 : LE {setSimplePlaceAttribute(#op4);}) infixapplication)*
  {#relexpression = infix_to_prefix(#relexpression);};

infixapplication :
  additiveexpression
  (options {warnWhenFollowAmbig=false;}:
   op : IDENTIFIER {setSimplePlaceAttribute(#op);} additiveexpression)*
  {#infixapplication = infix_to_prefix(#infixapplication);};

additiveexpression :
  multiplicativeexpression
  (options {warnWhenFollowAmbig=false;}:
   (  op1 : PLUS {setSimplePlaceAttribute(#op1);}
    | op2 : MINUS {setSimplePlaceAttribute(#op2);} ) multiplicativeexpression)*
  {#additiveexpression = infix_to_prefix(#additiveexpression);};

multiplicativeexpression :
  unaryexpression
  (options {warnWhenFollowAmbig=false;}:
   (  op1 : MULT {setSimplePlaceAttribute(#op1);}
    | op2 : DIV {setSimplePlaceAttribute(#op2);} ) unaryexpression)*
  {#multiplicativeexpression = infix_to_prefix(#multiplicativeexpression);};

unaryexpression :
  ( op: MINUS {setSimplePlaceAttribute(#op);} unaryexpression
   {#unaryexpression = #makeUnaryApplication(#unaryexpression);})
  | simpleExpression
  ;

simpleExpression :
  expressionprefix (options {warnWhenFollowAmbig=false;}:
        expressionSuffix)*
  {#simpleExpression = makeSimpleExpression(#simpleExpression);};

nameexpr :
  name
  {#nameexpr = #makeNameExpr((XmlAst)#nameexpr);};

expressionprefix 
  : (nextvariable)                => nextvariable
  | (module DOT ("INIT"|"TRANS")) => statepreds
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
  : "LAMBDA" LP pvarDecls RP CLN expression
  ;

quantifiedexpression 
  : ("FORALL" | "EXISTS") LP pvarDecls RP CLN expression
  ;

letexpression 
  : "LET" letdeclarations "IN" expression
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
  : "IF"   expression
    "THEN" expression
    (elsif)*   
    "ELSE" expression
    "ENDIF"
  ;

elsif 
  : "ELSIF" expression "THEN" expression 
  ;

statepreds 
  : module DOT ("INIT" |"TRANS")
  ;
  
argument
  : LP expressions RP 
  ;

expressions 
  : expression (COMMA expression )* 
  ;

updatesuffix 
  : "WITH" update
  ;

update 
  : updateposition ASSIGN! expression 
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
  : "IN" expression
  ;

rhsdefinition 
  : rhsexpression 
  | rhsselection 
  ;

simpleDefinition 
  : lhs rhsdefinition
  ;

foralldefinition 
  : LP! "FORALL" LP pvarDecls RP CLN definitions RP 
  ;

definition 
  : simpleDefinition 
  | foralldefinition 
  ;

definitions :
  definition (SEMI! definition)* ;

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
  : "BEGIN" basedeclarations "END"
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
  : "LOCAL" pidentifiers "IN" module
  ;

newoutput 
  : "OUTPUT" pidentifiers "IN" module
  ;

renaming 
  : "RENAME" renames "IN" module
  ;

renames 
  : rename (COMMA! rename)*
  ;

rename 
  : lhs "TO" lhs
  ;

withModule
  : "WITH" newVarDecls module
  ;

modulename 
  : name moduleActuals
  ;

moduleActuals 
  : (LB expressions RB)?
  ;

observeModule 
  : "OBSERVE" module "WITH" module
  ;

/* Declarations within modules */

inputdecl 
  : "INPUT" varDecls
  ;

outputdecl 
  : "OUTPUT" varDecls
  ;

globaldecl 
  : "GLOBAL" varDecls
  ;

localdecl
  : "LOCAL" varDecls
  ;

defdecl
  : "DEFINITION" definitions
  ;

invardecl
  : "INVARIANT" expression
  ;

initfordecl 
  : "INITFORMULA" expression
  ;

initdecl 
  : "INITIALIZATION" definitionorcommand (SEMI definitionorcommand)*
  ;

transdecl 
  : "TRANSITION" definitionorcommand (SEMI definitionorcommand)*
  ; 

labeledcommand 
  : identifier CLN guardedcommand
  ;

namedcommand 
  : (identifier CLN) => labeledcommand
  | guardedcommand 
  ;

multicommand 
  : LP ASYNC LP pvarDecls RP CLN somecommand RP 
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
  : identifiers CLN "TYPE";

actualparameters 
  : (actualtypes)? SEMI (actualexprs)?
  ;

actualtypes 
  : (type (COMMA type)*)?
  ;

actualexprs 
  : (expression (COMMA expression)*)?
  ;

identifier 
  : IDENTIFIER
  ;

numeral 
  : NUMERAL
  ;

// Whitespace
WS : (' ' | '\t' | '\n' | '\r' | '\f')+ { SKIP(); }
   ;

// Single-line comments
SL_COMMENT
  : "%" (~('\n'|'\r'))* ('\n'|'\r'('\n')?) { SKIP(); }
  ;

LP: '(';
RP: ')';
LB: '[';
RB: ']';
LC: '{';
RC: '}';
RECS: "[#";
RECE: "#]";
RECEXS: "(#";
RECEXE: "#)";
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
AND: "AND";
OR: "OR";
XOR: "XOR";
NOT: "NOT";
ASSIGN: ":=" ;
DOTDOT: ".." ;
QUOTE: "\'" ;
IMPLIES: "=>" ;
EQ: '=' ;
DIV: '/' ;
NEQ: "/=" ;
SLASH: '/';
SYNC: "||" ;
ASYNC: "[]";
PLUS: '+';
LONGARROW: "-->" ;
ARROW: "->" ;
MINUS: '-' ;
HYPHEN: '-';
MULT : '*';

// Relational operators
IFF : "<=>" ;
LE : "<=" ;
LT : '<' ;
GE : ">=" ;
GT : '>' ;

// Misc
UNBOUNDED : '_' ;

/* From the language description: an identifier is taken to be any string
of ASCII characters that is not a numeral and does not contain spaces,
parentheses, brackets, braces, the percent sign, equality, comma, period,
colon, semi-colon, and hash.  */

// IDENTIFIER
IDENTIFIER: (ALPHA (ALPHA|'0'..'9'|'?'|'_')*) | (OPCHAR1 (OPCHAR)*) ;
ALPHA: ('a'..'z'|'A'..'Z');
OPCHAR1: ('$'|'&'|'@'|'^'|'~');
OPCHAR: ~('a'..'z'|'A'..'Z'|'0'..'9'|'('|')'|'['|']'|'{'|'}'|'%'|','|'.'|':'|';'|'#'|'\''|'!'|'?'|'_'|'|'|' '|'\t'|'\n'|'\r'|'\f') ;

// The only purpose of the following line is to allow the user to use the double quote character inside comments.
DOUBLEQUOTE : "\"";

