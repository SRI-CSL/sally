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
  { man   : 'b Manager.t
  ; vars  : state_vars
  ; env   : Environment.t
  ; invs  : 'a Abstract1.t
  ; init  : 'a Abstract1.t
  ; trans : 'a transition }
and
(* transition *)
'a transition =
  | Assignment of 'a Abstract1.t
  | Guarded of 'a guard_list
and
(* a guarded expression *)
'a guarded =
  { guard : 'a Abstract1.t
  ; expr  : 'a Abstract1.t }
and
(* guarded expression list - a pair of a guarded list and an else expression *)
'a guard_list = 'a guarded list * 'a Abstract1.t

