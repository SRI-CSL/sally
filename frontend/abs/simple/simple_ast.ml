(* A simpler AST *)

type expr =
  | Nat of int
  | Int of int
  | Float of float
  | Ident of string
  | Constrained of (expr -> expr)
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Ge of expr * expr
  | Gt of expr * expr
  | Eq of expr * expr
  | Not of expr
  | And of expr * expr
  | Or of expr * expr
  | Assign of expr * expr
  | Cond of expr * expr * expr
  | True
  | False
  | Seq of expr list;;

type decl =
  | Nat_decl of string
  | Int_decl of string
  | Real_decl of string
  | Bool_decl of string
  | Enum_def of string * (string list)
  | Enum_decl of string * string
  | Constraint_decl of decl * expr

type prog = {
  decls : decl list;
  invs  : expr list;
  expr  : expr };;

type sal_prog = {
  constants       : decl list;
  state_vars      : decl list;
  next_state_vars : decl list;
  invariants      : expr list;
  initials        : expr;
  guarded         : (expr * expr) list;
  default         : expr option;
  no_transition   : expr }
