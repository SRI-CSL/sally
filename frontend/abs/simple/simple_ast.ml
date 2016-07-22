(* A simpler AST *)

type decl =
  | Nat_decl of string
  | Int_decl of string
  | Real_decl of string

type expr =
  | Nat of int
  | Int of int
  | Float of float
  | Ident of string
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Ge of expr * expr
  | Gt of expr * expr
  | Eq of expr * expr
  | Neq of expr * expr
  | Not of expr
  | And of expr * expr
  | Or of expr * expr
  | Assign of expr * expr
  | Cond of expr * expr * expr
  | True
  | False;;

type prog = {
  decls : decl list;
  invs  : expr list;
  exprs : expr list };;

type sal_prog = {
  constants  : decl list;
  state_vars : decl list;
  invariants : expr list;
  guarded    : (expr * expr list) list;
  default    : (expr list) option }
