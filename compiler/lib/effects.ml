open Code

let fresh2 () = Var.fresh (), Var.fresh ()

let fresh3 () = Var.fresh (), Var.fresh (), Var.fresh ()

(* [DStack.t] represents runtime stacks of continuations (currently implemented
   as linked lists). *)
module DStack : sig
  type t = Var.t

  val cons : Var.t -> t -> instr list * t
  (** [cons k ks] returns a pair [(instrs,ks')], where [instrs] is the list of
      instructions necessary to push [k] onto [ks] and [ks'] is the resulting
      runtime stack. *)

  val split : t -> instr list * Var.t * t
  (** [split ks] returns [(instrs,k,ks')], where [instrs] is the list of
      instructions necessary to evaluate the top of the stack
      and bind it to [k], leaving the rest of the stack [ks]. *)
end = struct
  type t = Var.t

  let cons k ks =
    let res = Var.fresh () in
    [ Let (res, Block (2, [| k; ks |], Array)) ], res

  let split ks =
    let k, ks' = fresh2 () in
    [ Let (k, Field (ks, 0)); Let (ks', Field (ks, 1)) ], k, ks'
end

(* [Stack.t] represents partially static stacks of continuations. [Reflect]
   means that no information is known statically and the stack evaluation is
   left to the target language. *)
module Stack : sig
  type t =
    | ( :: ) of Var.t * t
    | []
    | Reflect of DStack.t

  val reify : t -> instr list * DStack.t
  (** Create a dynamic stack from a static one. [reify ks] retuns a pair
      [(instrs,v)], where [instrs] are the instructions necessary to create the
      dynamic stack and bind it to [v]. *)

  val reflect : DStack.t -> t
  (** Represent a runtime stack. *)

  val split : t -> instr list * Var.t * t
  (** [split ks] returns [(instrs,k,ks')], where [instrs] is the (possibly
      empty) list of instructions necessary to evaluate the top of the stack
      and bind it to [k], leaving the rest of the stack [ks]. *)
end = struct
  type t =
    | ( :: ) of Var.t * t
    | []
    | Reflect of Var.t

  let reflect v = Reflect v

  let rec reify : t -> instr list * DStack.t = function
    | [] ->
        let a = Var.fresh () in
        [ Let (a, Block (0, [||], Array)) ], a
    | k :: ks ->
        let instrs, v = reify ks in
        let cons_instrs, v' = DStack.cons k v in
        instrs @ cons_instrs, v'
    | Reflect v -> [], v

  let split = function
    | k :: ks ->
        ( (let open! List in
          [])
        , k
        , ks )
    | Reflect ks ->
        let a = Var.fresh () and b = Var.fresh () in
        [ Let (a, Field (ks, 0)); Let (b, Field (ks, 1)) ], a, Reflect b
    | [] -> raise (Invalid_argument "Stack.split")
end

type st = { program : Code.program }

let closure_of_pc : Addr.t -> st -> Var.t * st = assert false

(* Translate all the blocks in the transitive closure of [st] into CPS, and add
   them to the program in [st]. This is done only if the block's address is not
   already mapped in the program being created. *)
let rec cps_block : st -> Code.block -> Addr.t -> Stack.t -> st =
 fun st block block_addr ks ->
  if Addr.Map.mem block_addr st.program.blocks
  then st
  else
    let st, additional_instrs, branch, (translate_next : (Addr.t * Stack.t) list) =
      match block.branch with
      | Return x ->
          let split_instrs, k, ks = Stack.split ks in
          let reify_instrs, ks = Stack.reify ks in
          let ret = Var.fresh () in
          ( st
          , split_instrs @ reify_instrs @ [ Let (ret, Apply (k, [ x; ks ], true)) ]
          , Return ret
          , [] )
      | Raise (x, _) ->
          let split_instrs, _k, ks = Stack.split ks in
          let split_instrs', kx, ks = Stack.split ks in
          let split_instrs'', _kf, ks = Stack.split ks in
          let reify_instrs, ks = Stack.reify ks in
          let a = Var.fresh () in
          ( st
          , split_instrs
            @ split_instrs'
            @ split_instrs''
            @ reify_instrs
            @ [ Let (a, Apply (kx, [ x; ks ], true)) ]
          , Return a
          , [] )
      | Stop -> st, [], Stop, []
      | Branch (pc, args) ->
          let ret = Var.fresh () in
          let closure, st = closure_of_pc pc st in
          let reify_instrs, ks_r = Stack.reify ks in
          let args = args @ [ks_r] in
          ( st
          , reify_instrs @ [ Let (ret, Apply (closure, args, true)) ]
          , assert false
          , [ (pc,ks) ] )
      | Cond (_, _, _) -> _
      | Switch (_, _, _) -> _
      | Pushtrap (_, _, _, _) -> _
      | Poptrap (_, _) -> _
      | Resume (_, _, _) -> _
      | Perform (_, _, _) -> _
      | Reperform (_, _) -> _
      | LastApply (_, _, _) -> _
    in
    let block =
      { block with
        params = block.params @ [ Var.fresh () ] (* Additional continuation argument *)
      ; body = block.body @ additional_instrs
      ; branch
      }
    in
    let blocks = Addr.Map.add block_addr block st.program.blocks in
    let st = { program = { st.program with blocks } } in
    match translate_next with
    | [ (addr, ks) ] ->
        (* Tail call for the single-successor case *)
        cps_block st (Addr.Map.find addr st.program.blocks) addr ks
    | _ ->
        List.fold_left
          (fun acc_st (addr, ks) ->
            cps_block acc_st (Addr.Map.find addr st.program.blocks) addr ks)
          st
          translate_next
