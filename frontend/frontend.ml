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

let create_channel_in = function
  | Some filename -> open_in filename
  | None -> stdin

let create_channel_out = function
  | Some filename -> open_out filename
  | None -> stdout

let _ =
  let mcmt_output = ref None in
  let only_convert = ref false in
  let engine = ref "kind" in
  let rest = ref "" in
  let input_file = ref None in
  let sally_cmd = ref "" in
  (let open Arg in
   Arg.parse [
     "--to-mcmt", String (fun s -> mcmt_output := Some s; only_convert := true), "Only convert input file to mcmt, and exit.";
     "--output-mcmt", Set only_convert, "Only convert input files to mcmt, print the result to stdout or to the file given with -to-mcmt, and exit.";
     "--engine", Set_string engine, "Use the given engine in Sally";
     "--", Rest (fun s -> rest := !rest ^ " " ^ s), "Give these options to Sally";
     "--sally-bin", Set_string sally_cmd, "Sally binary path";
   ] (fun f ->
       input_file := Some f) "Frontend for Sally, use '-- options' to give options to Sally.");
  if !sally_cmd = "" then
    sally_cmd := Find_binary.find "sally" ["./sally"; "src/sally"; "../src/sally"; Sys.executable_name ^ "/../../src/sally"];
  create_channel_in !input_file
  |> Io.Sal_lexer.parse
  |> Converter.Sal_to_lispy.sal_context_to_lisp
  |> Ast.Lispy_simplifier.simplify_context
  |> Io.Lispy_writer.output_context_to_channel
  |> fun write_to -> if !only_convert then
    create_channel_out !mcmt_output
    |> write_to
  else
    let sally_in = Unix.open_process_out (!sally_cmd ^ " --from-stdin --engine " ^ !engine ^ " " ^ !rest) in
    let () = write_to sally_in in
    let _ = Unix.close_process_out sally_in in
    ()


(* Local Variables: *)
(* compile-command: "make -C ../build/" *)
(* End: *)
