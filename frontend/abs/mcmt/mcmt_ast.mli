type declaration =
  | Int_decl of string
  | Real_decl of string
  | Bool_decl of string

type expression =
  | Int of int
  | Real of float
  | Ident of string
  | Not of expression
  | Ge of expression * expression
  | Gt of expression * expression
  | Le of expression * expression
  | Lt of expression * expression
  | Eq of expression * expression
  | Neq of expression * expression
  | Add of expression * expression
  | Sub of expression * expression
  | Mul of expression * expression
  | Div of expression * expression
  | Ite of expression * expression * expression
  | And of expression * expression
  | Or of expression * expression
  | Xor of expression * expression
  | Implies of expression * expression
  | Let of (expression * expression) list * expression
  | True
  | False

type state_type =
  | Ref of string
  | Anon of declaration list * declaration list

type definition =
  | State_type of string * declaration list * declaration list
  | States of string * expression * expression
  | Transition of string * expression * expression
  | Transition_system of string * state_type * expression * expression
  | Constant of string * expression
  | Assume of string * expression
  | Query of string * expression

type context = definition list
