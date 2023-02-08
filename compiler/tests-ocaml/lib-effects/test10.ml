(* TEST
 *)

open Effect
open Effect.Deep

type _ t += Peek : int t
type _ t += Poke : unit t

let a i = perform Peek + Random.int i
let b i = a i + Random.int i
let c i = b i + Random.int i

let d i =
  Random.int i +
  try_with c i
  { effc = fun (type a) (e : a t) ->
      match e with
      | Poke -> Some (fun (k : (a,_) continuation) -> continue k ())
      | _ -> None }

let e i =
  Random.int i +
  try_with d i
  { effc = fun (type a) (e : a t) ->
      match e with
      | Peek -> Some (fun (k : (a,_) continuation) ->
          ignore (Deep.get_callstack k 100);
          continue k 42)
      | _ -> None }

let _ =
  ignore (e 1);
  print_string "ok\n"
