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

