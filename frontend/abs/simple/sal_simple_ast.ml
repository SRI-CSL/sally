(* SAL converted into simple programs *)

open Simple_ast;;

type sal_prog = {
  constants       : decl list;
  state_vars      : decl list;
  next_state_vars : decl list;
  invariants      : expr list;
  initials        : expr;
  guarded         : (expr * expr) list;
  default         : expr option;
  no_transition   : expr }
