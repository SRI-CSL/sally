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

let find name candidates = 
  let binary_path = ref None in
  let candidates = 
    try let dir = Sys.getenv (String.capitalize name ^ "DIR") 
      in (dir ^ "/" ^ name) :: candidates
    with Not_found -> candidates in
  let try_path l =
    ignore (Unix.stat l);
    if !binary_path = None then
      binary_path := Some l
  in
  List.iter (fun l ->
      try
        try_path l
      with
      | Unix.Unix_error(_) -> ()
    ) candidates;
  let wcmd = Format.sprintf "which %s > /dev/null" name in
  if Sys.command wcmd = 0 then
    if !binary_path = None then
      binary_path := Some name;
  match !binary_path with
  | Some s -> s
  | None ->
      Format.eprintf 
        "%s is required but can not be found\n\
         Please check the options.@." name;
      exit 1
