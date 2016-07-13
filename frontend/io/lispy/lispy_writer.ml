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

(* Abstract syntax for the lispy style of the .mcmt files read by Sally *)

open Ast.Lispy_ast

type indentation = In | Out | None

let print_enum =
  let c = ref 0 in
  fun f l ->
  List.iter (fun a ->
      Format.fprintf f "(define-constant %s %d)@\n" a !c;
      incr c;
    ) l
      
                 
let rec print_expr f =
  let print_nosep s a b =
    Format.fprintf f "(%s @[<v>%a %a@])" s print_expr a print_expr b;
  in
  let print_nosep_3 s a b c =
    Format.fprintf f "(%s @[<v>%a@;%a@;%a@])" s print_expr a print_expr b print_expr c;
  in
  let print_sep s n t e =
    Format.fprintf f "(%s @[<v>((%s %a))@\n%a@])" s n print_sally_type t print_expr e;
  in
  function
  | Forall(n, t, expr) -> 
     print_sep "forall" n t expr;
  | Exists(n, t, expr) -> 
     print_sep "exists" n t expr;
  | Select(expr, index) -> 
     print_nosep "select" expr index
  | Equality(a, b) -> print_nosep "=" a b
  | Value(s) -> Format.fprintf f "%s" s
  | LEnumItem s -> Format.fprintf f "%s" s
  | Ident(s, _) -> Format.fprintf f "%s" s
  | GreaterEqual(a, b) ->
    print_nosep ">=" a b
  | Greater(a, b) ->
    print_nosep ">" a b
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
    print_nosep "+" a b
  | Sub(a, b) ->
    print_nosep "-" a b
  | Div(a, b) ->
    print_nosep "/" a b
  | Mul(a, b) ->
    print_nosep "*" a b
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
  | Ite(a, b, c) -> print_nosep_3 "ite" a b c
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
  | LSet_cardinal (n, t, expr) -> print_sep "#" n t expr
  | True -> Format.fprintf f "true"
  | False -> Format.fprintf f "false"

and print_sally_type f = function
  | Real -> Format.fprintf f "Real"
  | LEnum l -> Format.fprintf f "Real"
  | Bool -> Format.fprintf f "Bool"
  | Range(_, _) -> Format.fprintf f "Real"
  | Array(a, b) -> Format.fprintf f "(Array (%a) (%a))" 
                     print_sally_type a print_sally_type b
  | ProcessType n -> Format.fprintf f "%s" n


let print_transition f (transition:transition) =
  Format.fprintf f "@[(define-transition %s state @;  " transition.id;
  print_expr f transition.formula;
  Format.fprintf f ")@]"

let print_state f (state:state) =
  Format.fprintf f "@[(define-states %s state @;  " state.id;
  print_expr f state.condition;
  Format.fprintf f ")@]"


let rec sally_type_to_debug = function
  | Real -> "Real"
  | LEnum l -> Format.sprintf "{Enum}" 
  | Bool -> "Bool"
  | Range(b, a) -> "[" ^ string_of_int b ^ ".." ^ string_of_int a ^ "]"
  | Array(a, b) -> sally_type_to_debug a ^ " -> " ^ sally_type_to_debug b
  | ProcessType n -> n


let print_state_type f (ident, var_list) =
  Format.fprintf f "@[(define-state-type state @;  (@[<v>";
  let rec print_variable (name, sally_type) =
    match sally_type with
    | Array(Range(array_inf, array_sup), b) ->
      begin
        for i = array_inf to array_sup do
          print_variable (name ^ "!" ^ string_of_int i, b);
        done;
      end
    | _ ->
      Format.fprintf f "(%s %a)@\n" name print_sally_type sally_type
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
  List.iter (fun enum_type ->
      Format.fprintf f "%a@\n" print_enum enum_type;
    ) c.enum_types;

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
  in Format.fprintf f "@."

(* Local Variables: *)
(* compile-command: "make -C ../../../build/ -j 4" *)
(* caml-annot-dir: "../../../build/frontend/io/lispy/" *)
(* End: *)
