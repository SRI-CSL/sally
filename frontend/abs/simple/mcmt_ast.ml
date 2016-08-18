type mcmt_type =
  | Int_type
  | Real_type
  | Bool_type

type declaration = string * mcmt_type

type expression =
  | Int of int
  | Real of float
  | Ident of string
  | Next of expression
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
  | And of expression list
  | Or of expression list
  | Xor of expression * expression
  | Implies of expression * expression
  | Let of (string * expression) list * expression
  | True
  | False

type state_type =
  | Ref of string
  | Anon of declaration list * declaration list

type definition =
  | State_type of string * declaration list * declaration list
  | States of string * state_type * expression
  | Transition of string * state_type * expression
  | Transition_system of string * state_type * expression * expression
  | Constant of string * expression
  | Assert of string * expression
  | Query of string * expression

type context = definition list
