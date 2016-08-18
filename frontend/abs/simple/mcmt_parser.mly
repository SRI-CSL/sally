%{
open Mcmt_ast
%}

%token <int> INT
%token <float> REAL
%token <string> IDENT
%token <string> INPUT
%token <string> STATE
%token <string> NEXT
%token INT_DECL REAL_DECL BOOL_DECL
%token OPEN_PAREN
%token CLOSE_PAREN
%token NOT
%token LET EQ NEQ GE GT LE LT AND OR XOR IMPLIES PLUS MINUS MUL DIV
%token ITE
%token TRUE
%token FALSE
%token COND ELSE
%token DEFINE_STATE_TYPE DEFINE_STATES DEFINE_TRANSITION DEFINE_TRANSITION_SYSTEM DEFINE_CONSTANT ASSERT QUERY
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
| DEFINE_STATES IDENT IDENT expression { States ($2, Ref $3, $4) }
| DEFINE_STATES IDENT OPEN_PAREN state_type CLOSE_PAREN expression { States ($2, Anon (fst $4, snd $4), $6) }
| DEFINE_TRANSITION IDENT IDENT expression { Transition ($2, Ref $3, $4) }
| DEFINE_TRANSITION IDENT OPEN_PAREN state_type CLOSE_PAREN expression { Transition ($2, Anon (fst $4, snd $4), $6) }
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
| IDENT INT_DECL {$1, Int_type}
| IDENT REAL_DECL {$1, Real_type}
| IDENT BOOL_DECL {$1, Bool_type}

expression:
| value { $1 }
| OPEN_PAREN op CLOSE_PAREN { $2 }

value:
| TRUE { True }
| FALSE { False }
| INT { Int $1 }
| REAL { Real $1 }
| IDENT { Ident $1 }
| INPUT { Ident $1 }
| STATE { Ident $1 }

op:
| NOT nexpression { Not $2 }
| EQ nexpression nexpression { Eq ($2, $3) }
| NEQ nexpression nexpression { Neq ($2, $3) }
| GE nexpression nexpression { Ge ($2, $3) }
| GT nexpression nexpression { Gt ($2, $3) }
| LE nexpression nexpression { Le ($2, $3) }
| LT nexpression nexpression { Lt ($2, $3) }
| PLUS nexpression nexpression { Add ($2, $3) }
| MINUS nexpression { Mul (Int (-1), $2) }
| MINUS nexpression nexpression { Sub ($2, $3) }
| MUL nexpression nexpression { Mul ($2, $3) }
| DIV nexpression nexpression { Div ($2, $3) }
| AND nexpressions { And $2 }
| OR nexpressions { Or $2 }
| XOR nexpression nexpression { Xor ($2, $3) }
| IMPLIES nexpression nexpression { Implies ($2, $3) }
| ITE expression nexpression nexpression { Ite ($2, $3, $4) }
| COND cond_expressions { $2 }
| LET OPEN_PAREN let_expressions CLOSE_PAREN expression { Let ($3, $5) }

cond_expressions:
| OPEN_PAREN expression nexpression CLOSE_PAREN cond_expressions { Ite ($2, $3, $5) }
| OPEN_PAREN ELSE nexpression CLOSE_PAREN { $3 }

nexpression:
| expression { $1 }
| NEXT { Next (Ident $1) }

nexpressions:
| nexpression nexpressions { $1::$2 }
| { [] }

let_expressions:
| OPEN_PAREN IDENT nexpression CLOSE_PAREN let_expressions { ($2, $3)::$5 }
| { [] }
