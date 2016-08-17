(** AST for a simple language for performing abstract interpretation *)

(** Declarations *)
type decl =
  (* TODO: remove Nat_decl *)
  | Nat_decl of string (** Natural number declaration *)
  | Int_decl of string (** Integer declaration *)
  | Real_decl of string (** Real number declaration *)
  | Bool_decl of string (** Boolean declaration *)
  | Enum_def of string * (string list) (** Enum type definition *)
  | Enum_decl of string * string (** Enum declaration, where the second string gives the name of the enum type *)
  | Constraint_decl of decl * expr (** Constraint declaration, where the expression gives the constraint *)

and

(** Expressions *)
expr =
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
  | Seq of expr list
  | Branch of expr list
  | Local of decl * expr;;

(**
  Simple language Example:

  declarations:
    x: int;
    z: real;
    b: bool;
    y: int, (y >= 0); // example of constraint declaration

  invariants:
    list of invariants (always true)

  program: expressions
    seq:
      x := 1; // assign x to 1
      y := 5;
      (x < 0); // boolean expressions: assert that x < 0:
      branch: choose non-deterministic
        - x = 1
        - x = 0
*)
type prog = {
  decls : decl list;
  invs  : expr list;
  expr  : expr };;
