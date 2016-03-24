(*
 * Parser for simplified SAL
 *)

let ch =
  if Array.length Sys.argv > 1 then
    open_in Sys.argv.(1)
  else
    stdin
;;

let ctx = Sallex.parse ch in
  Sal_ast.print_context stdout ctx

