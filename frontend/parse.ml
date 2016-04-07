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
	let lispy = Sal2lisp.sal_context_to_lisp ctx in
	List.iter (Lisp_ast.print_query stdout) lispy

