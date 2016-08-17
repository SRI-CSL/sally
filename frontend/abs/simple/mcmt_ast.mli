(** An AST for mcmt *)

(** Mcmt declaration types *)
type declaration =
  | Int_decl of string
  | Real_decl of string
  | Bool_decl of string

(** Mcmt expressions *)
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

(** Referring to mcmt state types *)
type state_type =
  | Ref of string (** Refer to the state type with name given by the string *)
  | Anon of declaration list * declaration list (** Refer to an unnamed state type *)

(** Mcmt definitions used to build an mcmt program *)
type definition =
  | State_type of string * declaration list * declaration list (** State type definition: the first list specifies state variables and the second specifies inputs *)
  | States of string * state_type * expression (** State definition *)
  | Transition of string * state_type * expression (** Transition definition *)
  | Transition_system of string * state_type * expression * expression (** Transition system definition *)
  | Constant of string * expression (** Constant definition *)
  | Assert of string * expression (** An assertion *)
  | Query of string * expression (** A query *)

(** An mcmt context, which is a list of definitions *)
type context = definition list
