(* Abstract version of simpler AST *)

open Apron;;

type 'a binary_abs = ('a abs_expr * 'a abs_expr) * 'a Abstract1.t option
and
'a abs_expr =
  | Val of Coeff.t
  | Ident of Var.t
  | Add of 'a binary_abs
  | Sub of 'a binary_abs
  | Mul of 'a binary_abs
  | Div of 'a binary_abs
  | Ge of 'a binary_abs
  | Gt of 'a binary_abs
  | Eq of 'a binary_abs
  | Neq of 'a binary_abs
  | Not of 'a abs_expr * 'a Abstract1.t option
  | And of 'a binary_abs
  | Or of 'a binary_abs
  | Assign of 'a binary_abs
  | Cond of ('a abs_expr * 'a abs_expr * 'a abs_expr) * 'a Abstract1.t option
  | True
  | False

type 'a abs_prog =
  { env   : Environment.t;
    man   : 'a Manager.t;
    invs  : 'a abs_expr list;
    exprs : 'a abs_expr list }
