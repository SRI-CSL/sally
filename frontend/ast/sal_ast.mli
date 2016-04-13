(*
 * Abtract syntax for the simplified SAL language
 *)

type state_var_tag = 
  | Local
  | Global
  | Input
  | Output

type assertion_tag =
  | Lemma
  | Theorem

type sal_type =
  | Base_type of string                        (* Primitive types *)
  | Range of sal_expr * sal_expr               (* [low .. high] *)
  | Enum of (string list)                      (* Enumeration/scalar type *)
  | Array of sal_type * sal_type               (* ARRAY index_type OF value_type *)
  | Subtype of string * sal_type * sal_expr    (* Predicate subtype *)

and sal_decl = (string list) * sal_type

and let_decl = string * sal_type * sal_expr   (* name : type = expr *)

and sal_expr =
  | Decimal of int
  | Float of float
  | Ident of string
  | Next of string
  | Funcall of string * (sal_expr list)
  | Array_access of sal_expr * sal_expr
  | Array_literal of string * sal_type * sal_expr
  | Set_literal of string * sal_type * sal_expr
  | Cond of ((sal_expr * sal_expr) list) * sal_expr  (* if-then-else *)
  | Opp of sal_expr
  | Add of sal_expr * sal_expr
  | Sub of sal_expr * sal_expr
  | Mul of sal_expr * sal_expr
  | Div of sal_expr * sal_expr
  | Ge of sal_expr * sal_expr
  | Gt of sal_expr * sal_expr
  | Le of sal_expr * sal_expr
  | Lt of sal_expr * sal_expr
  | Eq of sal_expr * sal_expr
  | Neq of sal_expr * sal_expr
  | Not of sal_expr
  | And of sal_expr * sal_expr
  | Or of sal_expr * sal_expr
  | Xor of sal_expr * sal_expr
  | Implies of sal_expr * sal_expr
  | Iff of sal_expr * sal_expr
  | Exists of sal_decl list * sal_expr
  | Forall of sal_decl list * sal_expr
  | Let of let_decl list * sal_expr

type state_var_decl = state_var_tag * (sal_decl list)

type sal_assignment =
  | Assign of sal_expr * sal_expr (* x := value or x' := value *)
  | Member of sal_expr * sal_expr (* x IN set of x' IN set *)

type guarded_command =
  | Guarded of sal_expr * (sal_assignment list)  (* expr -> assignments *)
  | Default of (sal_assignment list)             (* ELSE -> assignments *)

type sal_transition =
  | NoTransition                                 (* missing Transition clause *)
  | Assignments of sal_assignment list
  | GuardedCommands of guarded_command list

type sal_module = {
  state_vars: state_var_decl list;
  initialization: sal_assignment list;
  definition: sal_assignment list;
  invariant: sal_expr option;
  transition: sal_transition;
}

type sal_def = 
  | Type_decl of string
  | Type_def of string * sal_type
  | Constant_decl of string * sal_type
  | Constant_def of string * sal_type * sal_expr
  | Function_def of string * (sal_decl list) * sal_type * sal_expr
  | Assertion of string * assertion_tag * string * sal_expr
  | Module_def of string * sal_module

type sal_context = {
  ctx_name: string;
  definitions: sal_def list;
}
