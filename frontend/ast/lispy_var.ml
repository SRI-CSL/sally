let count = ref 0

let get_fresh_variable () =
	incr count;
	"v!!" ^ string_of_int !count

(* Local Variables: *)
(* compile-command: "make -C ../../build/" *)
(* End: *)
