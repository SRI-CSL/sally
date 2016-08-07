%{
open Mcmt_ast
%}

%token <int> INT
%token <float> REAL
%token <string> IDENT
%token INT_DECL REAL_DECL BOOL_DECL
%token OPEN_PAREN
%token CLOSE_PAREN
%token NOT
%token LET EQ NEQ GE GT LE LT AND OR XOR IMPLIES PLUS MINUS MUL DIV
%token ITE
%token TRUE
%token FALSE
%token DEFINE_STATE_TYPE DEFINE_STATES DEFINE_TRANSITION DEFINE_TRANSITION_SYSTEM DEFINE_CONSTANT ASSERT QUERY
%token COMMENT
%token EOF
%token LEX_ERROR

%start ctx

%type <Mcmt_ast.context> ctx

%%

ctx: definitions { $1 }

definitions:
| OPEN_PAREN definition CLOSE_PAREN definitions { $2::$4 }
| { [] }

definition:
| DEFINE_STATE_TYPE IDENT state_type { State_type ($2, fst $3, snd $3) }
| DEFINE_STATES IDENT expression expression { States ($2, $3, $4) }
| DEFINE_TRANSITION IDENT expression expression { Transition ($2, $3, $4) }
| DEFINE_TRANSITION_SYSTEM IDENT IDENT expression expression { Transition_system ($2, Ref $3, $4, $5) }
| DEFINE_TRANSITION_SYSTEM IDENT OPEN_PAREN state_type CLOSE_PAREN expression expression { Transition_system ($2, Anon (fst $4, snd $4), $6, $7) }
| DEFINE_CONSTANT IDENT expression { Constant ($2, $3) }
| ASSERT IDENT expression { Assert ($2, $3) }
| QUERY IDENT expression { Query ($2, $3) }

state_type:
| OPEN_PAREN declarations CLOSE_PAREN { ($2, []) }
| OPEN_PAREN declarations CLOSE_PAREN OPEN_PAREN declarations CLOSE_PAREN { ($2, $5) }

declarations:
| OPEN_PAREN declaration CLOSE_PAREN declarations { $2::$4 }
| { [] }

declaration:
| IDENT INT_DECL {Int_decl $1}
| IDENT REAL_DECL {Real_decl $1}
| IDENT BOOL_DECL {Bool_decl $1}

expression:
| value { $1 }
| OPEN_PAREN op CLOSE_PAREN { $2 }

value:
| TRUE { True }
| FALSE { False }
| INT { Int $1 }
| REAL { Real $1 }
| IDENT { Ident $1 }

op:
| NOT expression { Not $2 }
| EQ expression expression { Eq ($2, $3) }
| NEQ expression expression { Neq ($2, $3) }
| GE expression expression { Ge ($2, $3) }
| GT expression expression { Gt ($2, $3) }
| LE expression expression { Le ($2, $3) }
| LT expression expression { Lt ($2, $3) }
| PLUS expression expression { Add ($2, $3) }
| MINUS expression expression { Sub ($2, $3) }
| MUL expression expression { Mul ($2, $3) }
| DIV expression expression { Div ($2, $3) }
| AND expressions { And $2 }
| OR expressions { Or $2 }
| XOR expression expression { Xor ($2, $3) }
| IMPLIES expression expression { Implies ($2, $3) }
| ITE expression expression expression { Ite ($2, $3, $4) }
| LET OPEN_PAREN let_expressions CLOSE_PAREN expression { Let ($3, $5) }

expressions:
| expression expressions { $1::$2 }
| { [] }

let_expressions:
| OPEN_PAREN IDENT expression CLOSE_PAREN let_expressions { ($2, $3)::$5 }
| { [] }
