(*
 * This file is part of sally.
 * Copyright (C) 2016 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 *)

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

