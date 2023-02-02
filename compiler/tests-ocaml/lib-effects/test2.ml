(* TEST
 *)

open Effect
open Effect.Deep

type _ t += E : int -> int t

let f () =
  print_endline "perform effect (E 0)\n"; flush stdout;
  let v = perform (E 0) in
  print_string "perform returns "; print_int v; print_newline (); flush stdout;
  v + 1

let h : type a. a t -> ((a, 'b) continuation -> 'b) option = function
  | E v -> Some (fun k ->
      print_string "caught effect (E "; print_int v; print_string "). continuing..\n"; flush stdout;
      let v = continue k (v + 1) in
      print_string "continue returns "; print_int v; print_string "\n"; flush stdout;
      v + 1)
  | e -> None

let v =
  match_with f ()
  { retc = (fun v -> print_string "done "; print_int v; print_string "\n"; flush stdout; v + 1);
    exnc = (fun e -> raise e);
    effc = h }

let () = print_string "result="; print_int v; print_string "\n"; flush stdout
