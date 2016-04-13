open Ast.Sal_ast


(*
 * Pretty printing
 *)
val pp_type: Format.formatter -> sal_type -> unit
val pp_expr: Format.formatter -> sal_expr -> unit
val pp_module: Format.formatter -> sal_module -> unit
val pp_context: Format.formatter -> sal_context -> unit

(*
 * Variant: use the given output channel
 *)
val print_type: out_channel -> sal_type -> unit
val print_expr: out_channel -> sal_expr -> unit
val print_module: out_channel -> sal_module -> unit
val print_context: out_channel -> sal_context -> unit

