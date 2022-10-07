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

type st =
  { program : Code.program
  ; memoized_blocks : Code.block list Addr.Map.t
      (** The meaning of a mapping [a -> block] is
          that the block at address [a] in the original program has already
          been translated into [block]. *)
  }

let add_block ~st block =
  let free_pc = st.program.free_pc in
  let blocks = Addr.Map.add free_pc block st.program.blocks in
  free_pc, { st with program = { st.program with blocks; free_pc = free_pc + 1 } }

(* Create a closure to call a block. The paramater names in [params] should be
   fresh. (The only reason we take them in argument here is that sometimes we
   need to be able to control those names, like when translating an exception
   handler.) *)
let closure_of_pc_explicit_params (pc : Addr.t) ~(params : Var.t list) :
    instr list * Var.t =
  let name = Var.fresh () in
  [ Let (name, Closure (params, (pc, params))) ], name

let closure_of_pc pc ~arity =
  let params = List.init arity (fun _ -> Var.fresh ()) in
  closure_of_pc_explicit_params pc ~params

(* Add a new block performing a call to a function, supplying the block
   parameters as arguments. Therefore, [arity] must be function's arity. *)
let add_call_block ~st closure ~arity =
  let params = List.init arity (fun _ -> Var.fresh ()) in
  let ret = Var.fresh () in
  add_block
    ~st
    { params
    ; handler = None
    ; body = [ Let (ret, Apply (closure, params, true)) ]
    ; branch = Return ret
    }

(* CPS-translate a jump. This requires turning the jump into a function call,
   inserting the calling code in a new block, and jumping to that block. This
   function returns the instructions constructing the closure, the
   jump address and arguments, and the new translation state. *)
let cps_call_of_jump ~st cont ~(ks : DStack.t) : instr list * cont * st =
  let addr, args = cont in
  let args = args @ [ ks ] in
  (* Add the continuation parameter *)
  let def_instrs, closure = closure_of_pc addr ~arity:(List.length args) in
  let pc_call_block, st = add_call_block ~st closure ~arity:(List.length args) in
  def_instrs, (pc_call_block, args), st

let drop_exc_eff_conts () =
  let x, ks = fresh2 () in
  let split1, _kx, ks' = DStack.split ks in
  let split2, _kf, ks' = DStack.split ks' in
  let split3, k, ks' = DStack.split ks' in
  let ret = Var.fresh () in
  let body = split1 @ split2 @ split3 @ [ Let (ret, Apply (k, [ x; ks' ], true)) ] in
  { params = [ x; ks ]; handler = None; body; branch = Return ret }

(* Translate all the blocks in the transitive closure of [block] into CPS, and add
   them to the program in [st_to], the program being created. For convenience,
   also returns the translation of [block].
   When this function several times on the same block from [st_to], a memoized
   result is returned. However, this is only possible if the statically known
   prefix of the continuation stack [ks] has the same length in both cases.
   Otherwise, the block is re-translated. *)
let rec cps_block : orig:Code.program -> st:st -> Code.block -> addr:Addr.t -> Code.block * st =
 fun ~orig ~st block ~addr ->
  try Addr.Map.find addr st.program.blocks, st
  with Not_found ->
    let cps_block' ~st ~addr =
      let block = Addr.Map.find addr orig.blocks in
      cps_block ~orig ~st block ~addr
    in

    (let ks = Var.fresh () in (* Name of the continuation parameter in the
                                 translated block *)
     (* Instructions to insert at the end of the block's body, new branching
        instruction *)
     let st, additional_instrs, branch =
       match block.branch with
       | Return x ->
           let split_instrs, k, ks = Stack.split ks in
           let reify_instrs, ks = Stack.reify ks in
           let ret = Var.fresh () in
           ( st
           , split_instrs @ reify_instrs @ [ Let (ret, Apply (k, [ x; ks ], true)) ]
           , Return ret )
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
           , Return a )
       | Stop -> st, [], Stop
       | Branch (pc, args) ->
           let ret = Var.fresh () in
           let next_block, st = cps_block' ~st ~addr:pc in
           let create_closure, closure =
             closure_of_pc pc ~arity:(List.length next_block.params)
           in
           ( st
           , create_closure @ [ Let (ret, Apply (closure, args @ [ks], true)) ]
           , Return ret )
       | Cond (cond, ((addr1, _) as cont1), ((addr2, _) as cont2)) ->
           let reify_instrs, ks_r = Stack.reify ks in
           let constr_call1, cont1, st = cps_call_of_jump ~st cont1 ~ks:ks_r in
           let constr_call2, cont2, st = cps_call_of_jump ~st cont2 ~ks:ks_r in
           ( st
           , reify_instrs @ constr_call1 @ constr_call2
           , Cond (cond, cont1, cont2)
           , [ addr1, ks; addr2, ks ] )
       | Switch (x, block_conts, int_conts) ->
           let reify_instrs, ks_r = Stack.reify ks in
           let (closure_constr, st), block_conts =
             Array.fold_left_map
               (fun (acc_instrs, st) cont ->
                 let constr_call, cont, st = cps_call_of_jump ~st cont ~ks:ks_r in
                 (acc_instrs @ constr_call, st), cont)
               ([], st)
               block_conts
           in
           let (closure_constr, st), int_conts =
             Array.fold_left_map
               (fun (acc_instrs, st) cont ->
                 let constr_call, cont, st = cps_call_of_jump ~st cont ~ks:ks_r in
                 (acc_instrs @ constr_call, st), cont)
               (closure_constr, st)
               int_conts
           in
           ( st
           , reify_instrs @ closure_constr
           , Switch (x, block_conts, int_conts)
           , Array.to_list
             @@ Array.map (fun (addr, _) -> addr, ks)
             @@ Array.append block_conts int_conts )
       | Pushtrap (cont_body, _x, cont_handler, _poptraps) ->
           (* Read continuations on the stack *)
           let split_instrs, _k, ks' = Stack.split ks in
           let split_instrs', _kx, ks' = Stack.split ks' in
           let split_instrs'', kf, ks' = Stack.split ks' in

           (* Construct body closure *)
           let addr_body, args_body = cont_body in
           let body_closure_constr, closure_body =
             closure_of_pc addr_body ~arity:(List.length args_body + 1)
           in

           (* Construct pure continuation *)
           let kret_addr, st = add_block ~st (drop_exc_eff_conts ()) in
           let constr_kret, kret = closure_of_pc kret_addr ~arity:2 in

           (* Construct handler closure *)
           let handler_addr, handler_args = cont_handler in
           let handler_ks = Var.fresh () in
           let kh = Var.fresh () in
           let handler_wrapper_args =
             List.map (fun _ -> Var.fresh ()) handler_args @ [ handler_ks ]
           in
           let constr_kh =
             [ Let
                 (kh, Closure (handler_wrapper_args, (handler_addr, handler_wrapper_args)))
             ]
           in

           (* Construct body stack *)
           let stack_body =
             let open! Stack in
             kret :: kh :: kf :: ks'
           in
           let reify_stack_body, stack_body_r = Stack.reify stack_body in

           let ret = Var.fresh () in
           ( st
           , split_instrs
             @ split_instrs'
             @ split_instrs''
             @ body_closure_constr
             @ reify_stack_body
             @ constr_kret
             @ constr_kh
             @ [ Let (ret, Apply (closure_body, args_body @ [ stack_body_r ], true)) ]
           , Return ret
           , [ addr_body, stack_body; handler_addr, Stack.reflect handler_ks ] )
       | Poptrap (cont, _pushtrap) ->
           let next_pc, args = cont in
           let split1, _kret, ks = Stack.split ks in
           let split2, _kh, ks = Stack.split ks in
           let split3, _kf, ks = Stack.split ks in

           let create_clos, next_closure =
             closure_of_pc next_pc ~arity:(List.length args + 1)
           in

           let reify, ks_r = Stack.reify ks in
           let args = args @ [ ks_r ] in

           let ret = Var.fresh () in

           ( st
           , split1
             @ split2
             @ split3
             @ create_clos
             @ reify
             @ [ Let (ret, Apply (next_closure, args, true)) ]
           , Return ret
           , [ next_pc, ks ] )
       | Resume (_, _, _) -> _
       | Perform (_, _, _) -> _
       | Reperform (_, _) -> _
       | LastApply (x, (f, args, fully_applied), None) ->
           let reify, ks_r = Stack.reify ks in
           st, reify @ [ Let (x, Apply (f, args @ [ ks_r ], fully_applied)) ], Return x, []
       | LastApply (_x, (f, f_args, fully_applied), Some cont) ->
           let split, k, ks = Stack.split ks in

           let ret = Var.fresh () in
           let cont_addr, cont_args = cont in

           (* Construct continuation (see the formal definition of the transform) *)
           let constr_clos, cont_clos =
             closure_of_pc cont_addr ~arity:(List.length cont_args + 1)
           in
           let wrapper_block =
             let wrapper_ks = Var.fresh () in
             let cont_ks =
               let open! Stack in
               k :: Stack.reflect wrapper_ks
             in
             let reify_cont_ks, cont_ks_r = Stack.reify cont_ks in
             let ret = Var.fresh () in
             { params = List.map (fun _ -> Var.fresh ()) cont_args @ [ wrapper_ks ]
             ; handler = None
             ; body =
                 constr_clos
                 @ reify_cont_ks
                 @ [ Let (ret, Apply (cont_clos, cont_args @ [ cont_ks_r ], true)) ]
             ; branch = Return ret
             }
           in
           let wrapper_addr, st = add_block ~st wrapper_block in
           let constr_wrapper_clos, wrapper_clos =
             closure_of_pc wrapper_addr ~arity:(List.length cont_args + 1)
           in

           let f_ks =
             let open! Stack in
             wrapper_clos :: ks
           in
           let reify_f_ks, f_ks_r = Stack.reify f_ks in

           ( st
           , split
             @ reify_f_ks
             @ constr_wrapper_clos
             @ [ Let (ret, Apply (f, f_args @ [ f_ks_r ], fully_applied)) ]
           , Return ret
           , [ cont_addr, assert false ] )
     in
     let block =
       { block with
         params = block.params @ [ Var.fresh () ] (* Additional continuation argument *)
       ; body = block.body @ additional_instrs
       ; branch
       }
     in
     let blocks = Addr.Map.add block_addr block st.program.blocks in
     let st = { st with program = { st.program with blocks } } in
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
      )
