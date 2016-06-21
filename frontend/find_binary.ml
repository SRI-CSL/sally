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
