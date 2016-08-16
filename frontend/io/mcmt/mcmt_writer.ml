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

(* Abstract syntax for the mcmt style of the .mcmt files read by Sally *)

open Ast.Mcmt_ast

type indentation = In | Out | None

let rec print_expr f =
  let print_folded s a b =
    Format.fprintf f "(%s @[<v>" s;
    print_expr f a; Format.fprintf f " "; print_expr f b;
    Format.fprintf f "@])"
  in
  let print_folded_exists s a b =
    Format.fprintf f "(%s " s;
    print_expr f a;
    Format.fprintf f "@\n  @[<v>";
    print_expr f b;
    Format.fprintf f "@])"
  in
  let print_folded3 s a b c =
    Format.fprintf f "(%s @[<v>" s;
    print_expr f a; Format.fprintf f "@;";
    print_expr f b; Format.fprintf f "@;";
    print_expr f c;
    Format.fprintf f "@])"
  in
  function
  | Forall(n, t, expr) -> print_folded_exists "forall " (Ident("((" ^ n ^ " " ^ mcmt_type_to_string t ^ "))", Real)) expr
  | Exists(n, t, expr) -> print_folded_exists "exists" (Ident("((" ^ n ^ " " ^ mcmt_type_to_string t ^ "))", Real)) expr
  | Select(expr, index) -> print_folded "select" expr index
  | Equality(a, b) -> print_folded "=" a b
  | Value(s) -> Format.fprintf f "%s" s
  | Ident(s, _) -> Format.fprintf f "%s" s
  | GreaterEqual(a, b) ->
    print_folded ">=" a b
  | Greater(a, b) ->
    print_folded ">" a b
  | Or(a, b) ->
    begin
      Format.fprintf f "@[(or@\n  @[<v>";
      let rec expand_or = function
        | Or(c, d) ->
          begin
            expand_or c;
            Format.fprintf f "@\n";
            expand_or d;
          end
        | a -> print_expr f a;
      in
      expand_or a;
      Format.fprintf f "@\n";
      expand_or b;
      Format.fprintf f "@])@]";
    end
  | Add(a, b) ->
    print_folded "+" a b
  | Sub(a, b) ->
    print_folded "-" a b
  | Div(a, b) ->
    print_folded "/" a b
  | Mul(a, b) ->
    print_folded "*" a b
  | And(a, b) ->
    begin
      Format.fprintf f "@[(and@\n  @[<v>";
      let rec expand_and = function
        | And(c, d) ->
          begin
            expand_and c;
            Format.fprintf f "@\n";
            expand_and d;
          end
        | a -> print_expr f a
      in
      expand_and a;
      Format.fprintf f "@\n";
      expand_and b;
      Format.fprintf f "@])@]";
    end
  | Ite(a, b, c) ->
    print_folded3 "ite" a b c
  | Not(a) ->
    begin
      Format.fprintf f "@[(not ";
      print_expr f a;
      Format.fprintf f ")@]";
    end
  | LProc_cardinal s -> Format.fprintf f "@[(size %s)@]" s
  | Store (a, b, c) -> 
    Format.fprintf f "@[(store %a %a %a)@]"
      print_expr a print_expr b print_expr c
  | LSet_cardinal (n, t, expr) -> 
    print_folded_exists "#" (Ident("((" ^ n ^ " " ^ mcmt_type_to_string t ^ "))", Real)) expr
  | True -> Format.fprintf f "true"
  | False -> Format.fprintf f "false"

and mcmt_type_to_string = function
  | Real -> "Real"
  | Bool -> "Bool"
  | Range(_, _) -> "Real"
  | Array(ProcessType(n), t) -> "(Array (" ^ mcmt_type_to_string (ProcessType n) ^ ") ("^ mcmt_type_to_string t ^ "))"
  | Array(a, b) -> Format.sprintf "(Array (%s) (%s))" (mcmt_type_to_string a) (mcmt_type_to_string b)
  | ProcessType(n) -> n


let print_transition f (transition:transition) =
  Format.fprintf f "@[(define-transition %s state @;  " transition.id;
  print_expr f transition.formula;
  Format.fprintf f ")@]"

let print_state f (state:state) =
  Format.fprintf f "@[(define-states %s state @;  " state.id;
  print_expr f state.condition;
  Format.fprintf f ")@]"


let rec mcmt_type_to_debug = function
  | Real -> "Real"
  | Bool -> "Bool"
  | Range(b, a) -> "[" ^ string_of_int b ^ ".." ^ string_of_int a ^ "]"
  | Array(a, b) -> mcmt_type_to_debug a ^ " -> " ^ mcmt_type_to_debug b
  | ProcessType(n) -> n ^ ":[..]"


let print_state_type f (ident, var_list) =
  Format.fprintf f "@[(define-state-type state @;  (@[<v>";
  let rec print_variable (name, mcmt_type) =
    match mcmt_type with
    | Array(Range(array_inf, array_sup), b) ->
      begin
        for i = array_inf to array_sup do
          print_variable (name ^ "!" ^ string_of_int i, b);
        done;
      end
    | _ ->
      Format.fprintf f "(%s %s)@\n" name (mcmt_type_to_string mcmt_type)
  in
  List.iter print_variable var_list;
  Format.fprintf f "@]))@]@\n"

let print_transition_system f ts =
  print_state_type f ts.state_type;
  Format.fprintf f "@\n";
  print_state f ts.initial_state;
  Format.fprintf f "@\n";
  print_transition f ts.transition;
  Format.fprintf f "@\n";
  Format.fprintf f "(define-transition-system %s state init trans)@." ts.id

let print_query f q =
  Format.fprintf f "@[(query %s " (q.transition_system.id);
  print_expr f q.condition;
  Format.fprintf f "@])"

let output_context_to_channel c ch =
  let f = Format.formatter_of_out_channel ch in
  List.iter (fun parametrized_type ->
      Format.fprintf f "(define-process-type %s)@\n" parametrized_type;
    ) c.parametrized_types;
  Format.fprintf f "@\n";
  let _ = List.fold_left (fun ts_written q ->
      let ts_written = 
        let ts_id = q.transition_system.id in
        if List.mem ts_id ts_written then
          ts_written
        else
          let _ = print_transition_system f q.transition_system in
          let _ = Format.fprintf f "@;@\n" in
          ts_id::ts_written
      in
      print_query f q;
      Format.fprintf f "@;@\n";
      ts_written
    ) [] c.queries
  in ()

(* Local Variables: *)
(* compile-command: "make -C ../../../build/ -j 4" *)
(* caml-annot-dir: "../../../build/frontend/io/mcmt/" *)
(* End: *)
