open Apron;;

(* capture an apron variable's sal_type, including different sal Base_types; ignore Subtype, IntegerRange/Proc for now *)
type def =
  | Nat of string
  | Int of string
  | Real of string
  | Bool of string
  | Bounded of string * string * string (* Range, Enum *)
  | Arr of string * def * def
  | Const_val of def * string
  | Const of def;;

(* capture all state variables for a transition system *)
type state_vars =
  { current_ints   : Var.t list
  ; next_ints      : Var.t list
  ; constant_ints  : Var.t list
  ; current_reals  : Var.t list
  ; next_reals     : Var.t list
  ; constant_reals : Var.t list
  ; constraints    : string list }

(* a transition system's Apron components *)
type ('a, 'b) trans_sys =
  { man        : 'b Manager.t
  ; vars       : state_vars
  ; env        : Environment.t
  ; invs       : 'a Abstract1.t
  ; init       : 'a Abstract1.t
  ; transition : 'a Abstract1.t }

(* a condition *)
type 'a cond =
  { constrained : Var.t list
  ; abs         : 'a Abstract1.t }

(* a condition/guard and an expression *)
type 'a guarded =
  { guard : 'a cond
  ; expr  : 'a Abstract1.t }
