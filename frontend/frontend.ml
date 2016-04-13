(*
 * Parser for simplified SAL
 *)

let ch =
  if Array.length Sys.argv > 1 then
    open_in Sys.argv.(1)
  else
    stdin
;;

let ctx = Io.Sal_lexer.parse ch in
	let lispy = Converter.Sal_to_lispy.sal_context_to_lisp ctx in
	List.iter (Io.Lispy_writer.print_query stdout) lispy

