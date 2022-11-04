(* The following CPS transform is the one proposed in D. Hillerström, S.
   Lindley, R. Atkey, and K. C. Sivaramakrishnan, “Continuation Passing Style
   for Effect Handlers” (FSCD 2017), with adaptations to account for exception
   handlers (which are not considered in detail in the paper) and for the fact
   that the language is an SSA form rather than a classical lambda calculus.

   It is a one-pass CPS transform which passes continuations, effect handlers
   and exception handlers in an explicit stack. The transformation pass
   performs some partial evaluation to perform administrative reductions during
   the translation as much as possible, rather than leaving them for runtime. *)

open Code

let debug = Debug.find "eff"

type graph =
  { succs : (Addr.t, Addr.Set.t) Hashtbl.t
  ; reverse_post_order : Addr.t list
  }

let build_graph blocks pc =
  let succs = Hashtbl.create 16 in
  let l = ref [] in
  let visited = Hashtbl.create 16 in
  let rec traverse pc =
    if not (Hashtbl.mem visited pc)
    then (
      Hashtbl.add visited pc ();
      let successors = Code.fold_children blocks pc Addr.Set.add Addr.Set.empty in
      let successors =
        (* Changed from Generate.build_graph *)
        match (Addr.Map.find pc blocks).branch with
        | Pushtrap (_, _, (pc', _), _) -> Addr.Set.add pc' successors
        | _ -> successors
      in
      Hashtbl.add succs pc successors;
      Addr.Set.iter traverse successors;
      l := pc :: !l)
  in
  traverse pc;
  { succs; reverse_post_order = !l }

let dominator_tree g =
  (* A Simple, Fast Dominance Algorithm
     Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy *)
  let dom = Hashtbl.create 16 in
  let order = Hashtbl.create 16 in
  List.iteri (fun i pc -> Hashtbl.add order pc i) g.reverse_post_order;
  let rec inter pc pc' =
    (* Compute closest common ancestor *)
    if pc = pc'
    then pc
    else if Hashtbl.find order pc < Hashtbl.find order pc'
    then inter pc (Hashtbl.find dom pc')
    else inter (Hashtbl.find dom pc) pc'
  in
  List.iter
    (fun pc ->
      let l = Hashtbl.find g.succs pc in
      Addr.Set.iter
        (fun pc' ->
          let d = try inter pc (Hashtbl.find dom pc') with Not_found -> pc in
          Hashtbl.replace dom pc' d)
        l)
    g.reverse_post_order;
  (* Check we have reached a fixed point (reducible graph) *)
  List.iter
    (fun pc ->
      let l = Hashtbl.find g.succs pc in
      Addr.Set.iter
        (fun pc' ->
          let d = Hashtbl.find dom pc' in
          assert (inter pc d = d))
        l)
    g.reverse_post_order;
  dom

type jump_closures =
  { closure_of_jump : Var.t Addr.Map.t
  ; closure_of_alloc_site : (Var.t * Addr.t) list Addr.Map.t
  ; allocated_call_blocks : (Var.t, Addr.t) Hashtbl.t
  }

let jump_closures idom : jump_closures =
  let closure_of_jump, closure_of_alloc_site =
    Hashtbl.fold
      (fun node idom_node (c_o_j, c_o_a_s) ->
        let cname = Var.fresh () in
        let closures_to_allocate =
          try Addr.Map.find idom_node c_o_a_s with Not_found -> []
        in
        let c_o_j = Addr.Map.add node cname c_o_j in
        let c_o_a_s =
          Addr.Map.add idom_node ((cname, node) :: closures_to_allocate) c_o_a_s
        in
        c_o_j, c_o_a_s)
      idom
      (Addr.Map.empty, Addr.Map.empty)
  in

  { closure_of_jump; closure_of_alloc_site; allocated_call_blocks = Hashtbl.create 37 }

(******************************************************************************)

type st =
  { mutable new_blocks : Code.block Addr.Map.t * Code.Addr.t
  ; blocks : Code.block Addr.Map.t
  ; jc : jump_closures
  }

let fresh2 () = Var.fresh (), Var.fresh ()

let add_block st block =
  let blocks, free_pc = st.new_blocks in
  st.new_blocks <- Addr.Map.add free_pc block blocks, free_pc + 1;
  free_pc

let filter_cont_params st cont =
  let block = Addr.Map.find (fst cont) st.blocks in
  let cont_params = snd cont in
  let block_params = block.params in
  let rec loop = function
    | x :: xs, _y :: ys -> x :: loop (xs, ys)
    | _, [] -> []
    | [], _ -> assert false
  in
  fst cont, loop (cont_params, block_params)

let add_call_block st cname params =
  let fresh_params = List.map (fun _ -> Var.fresh ()) params in
  let ret = Var.fresh () in
  let addr =
    add_block
      st
      { params = fresh_params
      ; handler = None
      ; body = [ Let (ret, Apply (cname, params, true)) ]
      ; branch = Return ret
      }
  in
  Hashtbl.add st.jc.allocated_call_blocks cname addr;
  addr

let cps_branch st _pc ks cont =
  let cont = filter_cont_params st cont in
  let caddr = fst cont in
  let params = snd cont @ [ ks ] in
  try
    let cname = Addr.Map.find caddr st.jc.closure_of_jump in
    if not @@ debug ()
    then ()
    else (
      Printf.eprintf "cps_branch: %d ~> call v%d params:" caddr (Var.idx cname);
      List.iter (fun v -> Printf.eprintf " v%d" (Var.idx v)) params;
      Printf.eprintf "\n\n");
    let ret = Var.fresh () in
    [ Let (ret, Apply (cname, params, true)) ], Return ret
  with Not_found -> [], Branch (caddr, params)
(* ) *)

(* Create a function whose body starts at [pc]. If the original program already
   such a function, use it, otherwise we create it. *)
let closure_of_pc ~st pc ~arity =
  try [], Addr.Map.find pc st.jc.closure_of_jump
  with Not_found ->
    let name = Var.fresh () in
    let params = List.init arity (fun _ -> Var.fresh ()) in

    let addr_new_block =
      let params_block = List.init arity (fun _ -> Var.fresh ()) in
      add_block
        st
        { params = params_block
        ; handler = None
        ; body = []
        ; branch = Branch (pc, params_block)
        }
    in

    [ Let (name, Closure (params, (addr_new_block, params))) ], name

(* FIXME uncomment and use (or remove) *)
(*
let alloc_stack_k hv k kx kf =
  let v, ret = Var.fresh (), Var.fresh () in
  { params = [ v ]
  ; handler = None
  ; body = [ Let (ret, Apply (hv, [ k; kx; kf; v ], true)) ]
  ; branch = Return ret
  }

let alloc_stack_kx hx k kx kf = alloc_stack_k hx k kx kf

let alloc_stack_kf hf k kx kf =
  let v, v', ret = Var.fresh (), Var.fresh (), Var.fresh () in
  { params = [ v; v' ]
  ; handler = None
  ; body = [ Let (ret, Apply (hf, [ k; kx; kf; v; v' ], true)) ]
  ; branch = Return ret
  }

let alloc_stack k kx kf =
  let f, x, ret = Var.fresh (), Var.fresh (), Var.fresh () in
  { params = [ f; x ]
  ; handler = None
  ; body = [ Let (ret, Apply (f, [ k; kx; kf; x ], true)) ]
  ; branch = Return ret
  }

let cps_alloc_stack
    st
    (ret : Var.t)
    (kx : Var.t)
    (kf : Var.t)
    (hv : Var.t)
    (hx : Var.t)
    (hf : Var.t) =
  let id, stack_k, stack_kx, stack_kf = fresh4 () in
  let f = Var.fresh () in
  let v1, v2, v3, v4, v5, v6 = fresh6 () in
  let id_addr = add_block st (identity ()) in
  let stack_k_addr = add_block st (alloc_stack_k hv id kx kf) in
  let stack_kx_addr = add_block st (alloc_stack_kx hx id kx kf) in
  let stack_kf_addr = add_block st (alloc_stack_kf hf id kx kf) in
  let stack_addr = add_block st (alloc_stack stack_k stack_kx stack_kf) in
  [ Let (id, Closure ([ v1 ], (id_addr, [ v1 ])))
  ; Let (stack_k, Closure ([ v2 ], (stack_k_addr, [ v2 ])))
  ; Let (stack_kx, Closure ([ v3 ], (stack_kx_addr, [ v3 ])))
  ; Let (stack_kf, Closure ([ v4; v5 ], (stack_kf_addr, [ v4; v5 ])))
  ; Let (ret, Closure ([ f; v6 ], (stack_addr, [ f; v6 ])))
  ]
*)

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

  val pop_trap : t -> instr list * Var.t * t

  val push_trap : Var.t -> t -> instr list * t
end = struct
  type t = Var.t

  let cons k ks =
    let res = Var.fresh () in
    [ Let (res, Block (0, [| k; ks |], NotArray)) ], res

  let split ks =
    let k, ks' = fresh2 () in
    [ Let (k, Field (ks, 0)); Let (ks', Field (ks, 1)) ], k, ks'

  let pop_trap ks =
    (*  (k, ((e, k', es), fs)) ==> e (k', (es, fs)) *)
    let h = Var.fresh () in
    let es = Var.fresh () in
    let es' = Var.fresh () in
    let fs = Var.fresh () in
    let e = Var.fresh () in
    let k' = Var.fresh () in
    let h' = Var.fresh () in
    let ks' = Var.fresh () in
    ( [ Let (h, Field (ks, 1))
      ; Let (es', Field (h, 0))
      ; Let (fs, Field (h, 1))
      ; Let (e, Field (es', 0))
      ; Let (k', Field (es', 1))
      ; Let (es, Field (es', 2))
      ; Let (h', Block (0, [| es; fs |], NotArray))
      ; Let (ks', Block (0, [| k'; h' |], NotArray))
      ]
    , e
    , ks' )

  let push_trap e ks =
    (* push_trap: e (k, (es, fs))  ==> (k, ((e, k, es), fs)) *)
    let k = Var.fresh () in
    let h = Var.fresh () in
    let es = Var.fresh () in
    let fs = Var.fresh () in
    let es' = Var.fresh () in
    let h' = Var.fresh () in
    let ks' = Var.fresh () in
    ( [ Let (k, Field (ks, 0))
      ; Let (h, Field (ks, 1))
      ; Let (es, Field (h, 0))
      ; Let (fs, Field (h, 1))
      ; Let (es', Block (0, [| e; k; es |], NotArray))
      ; Let (h', Block (0, [| es'; fs |], NotArray))
      ; Let (ks', Block (0, [| k; h' |], NotArray))
      ]
    , ks' )
end

let cps_last ~st ~(block_addr : Addr.t) (last : last) ~(ks : DStack.t) : instr list * last
    =
  let ( @> ) instrs1 (instrs2, last) = instrs1 @ instrs2, last in

  let cps_jump_cont cont =
    let pc, args = filter_cont_params st cont in
    let args = args @ [ ks ] in
    try
      let cname = Addr.Map.find pc st.jc.closure_of_jump in
      let call_block = add_call_block st cname args in
      call_block, args
    with Not_found -> pc, args
  in

  let cps_branch' = cps_branch st block_addr ks in

  match last with
  | Return x ->
      let split_instrs, k, ks = DStack.split ks in
      let ret = Var.fresh () in
      split_instrs @ [ Let (ret, Apply (k, [ x; ks ], true)) ], Return ret
  | Raise (x, _) ->
      let pop_instrs, kx, ks = DStack.pop_trap ks in
      let ret = Var.fresh () in
      ( pop_instrs
        @ [ Let (Var.fresh (), Prim (Extern "caml_pop_trap", [])) ]
        @ [ Let (ret, Apply (kx, [ x; ks ], true)) ]
      , Return ret )
  | Stop ->
      (* ??? *)
      [], Stop
  | Branch cont -> cps_branch' cont
  | Cond (x, cont1, cont2) -> [], Cond (x, cps_jump_cont cont1, cps_jump_cont cont2)
  | Switch (x, c1, c2) ->
      [], Switch (x, Array.map cps_jump_cont c1, Array.map cps_jump_cont c2)
  | Pushtrap (cont_body, x, cont_handler, _) ->
      (* Construct body closure *)
      let body_addr, body_args = cont_body in
      let constr_body_closure, body_closure =
        closure_of_pc ~st body_addr ~arity:(List.length body_args + 1)
      in

      (* Construct handler closure *)
      let handler_addr, handler_args = cont_handler in
      let handler_ks = Var.fresh () in
      let new_kx = Var.fresh () in
      let handler_wrapper_args = [ x; handler_ks ] in
      let handler_wrapper_block =
        let x, ks = Var.fresh (), Var.fresh () in
        { params = [ x; ks ]
        ; handler = None
        ; body = []
        ; branch = Branch (handler_addr, handler_args @ [ ks ])
        }
      in
      let handler_wrapper_addr = add_block st handler_wrapper_block in
      let constr_new_kx =
        [ Let
            ( new_kx
            , Closure (handler_wrapper_args, (handler_wrapper_addr, handler_wrapper_args))
            )
        ]
      in

      (* Construct body continuation stack *)
      let constr_body_ks, body_ks = DStack.push_trap new_kx ks in

      let ret = Var.fresh () in
      ( constr_body_closure
        @ constr_new_kx
        @ constr_body_ks
        @ [ Let (Var.fresh (), Prim (Extern "caml_push_trap", [ Pv new_kx; Pv ks ])) ]
        @ [ Let (ret, Apply (body_closure, body_args @ [ body_ks ], true)) ]
      , Return ret )
  | Poptrap ((next_pc, args), _) ->
      let pop, _, ks = DStack.pop_trap ks in

      let constr_closure, closure_next =
        closure_of_pc ~st next_pc ~arity:(List.length args + 1)
      in

      let ret = Var.fresh () in
      ( pop
        @ constr_closure
        @ [ Let (Var.fresh (), Prim (Extern "caml_pop_trap", [])) ]
        @ [ Let (ret, Apply (closure_next, args @ [ ks ], true)) ]
      , Return ret )
  | Resume (stack, func, args, cont_opt) -> (
      match cont_opt with
      | None ->
          let split_instrs, k, ks = DStack.split ks in
          let ret = Var.fresh () in
          ( [ Let (ret, Apply (stack, [ func; args ], true)) ]
            @ split_instrs
            @ [ Let (ret, Apply (k, [ ret; ks ], true)) ]
          , Return ret )
      | Some (ret, cont) ->
          [ Let (ret, Apply (stack, [ func; args ], true)) ] @> cps_branch' cont
          (*| Perform (eff, ret, cont) ->*))
  | Perform _ ->
      (*
      let cur_stack = Var.fresh () in
      let f, v = fresh2 () in
      let kfret = Var.fresh () in
      let cur_k, cur_k_closure = closure_of_cont' [ ret ] cont in
      let stack = add_block st (alloc_stack cur_k kx kf) in
      ( [ Let (cur_k, cur_k_closure)
        ; Let (cur_stack, Closure ([ f; v ], (stack, [ f; v ])))
        ; Let (kfret, Apply (kf, [ eff; cur_stack ], true))
        ]
      , Return kfret
    *)
      failwith "not implemented"
  (*| Reperform (eff, stack) ->*)
  | Reperform _ ->
      (*
      let kfret = Var.fresh () in
      [ Let (kfret, Apply (kf, [ eff; stack ], true)) ], Return kfret
    *)
      failwith "not implemented"

let cps_instr _st ~ks:(_ks : DStack.t) (instr : instr) : instr list =
  match instr with
  | Let (_x, Prim (Extern "caml_alloc_stack", [ Pv _hv; Pv _hx; Pv _hf ])) ->
      failwith "not implemented" (*cps_alloc_stack st x kx kf hv hx hf*)
  | Let (x, Closure (params, (pc, args))) ->
      let ks = Var.fresh () in
      [ Let (x, Closure (params @ [ ks ], (pc, args @ [ ks ]))) ]
  | Let (_, Apply _) -> assert false
  | _ -> [ instr ]

let cps_block st block_addr block =
  let ks = Var.fresh () in

  let alloc_jump_closure =
    try
      let to_allocate = Addr.Map.find block_addr st.jc.closure_of_alloc_site in
      List.map
        (fun (cname, jump_addr) ->
          let jump_block = Addr.Map.find jump_addr st.blocks in
          let ks = Var.fresh () in
          let fresh_params =
            List.map (fun _ -> Var.fresh ()) jump_block.params @ [ ks ]
          in
          Let (cname, Closure (fresh_params, (jump_addr, fresh_params))))
        to_allocate
    with Not_found -> []
  in

  let body, last =
    (* We handle the case of function applications (which should always end a
       block) here, and the rest in [cps_last] *)
    match Stdlib.List.split_last block.body, block.branch with
    | Some (body_prefix, Let (x, Apply (f, args, fully_applied))), Return ret ->
        assert (alloc_jump_closure = []);
        ( (List.map (cps_instr st ~ks) body_prefix |> List.flatten)
          @ alloc_jump_closure
          @ [ Let (x, Apply (f, args @ [ ks ], fully_applied)) ]
        , Return ret )
    | Some (body_prefix, Let (x, Apply (f, args, fully_applied))), Branch cont ->
        let split, k, ks = DStack.split ks in

        let ret = Var.fresh () in
        let cont_addr, cont_args = cont in

        (* Construct continuation (see the formal definition of the transform) *)
        let constr_closure, cont_closure =
          closure_of_pc ~st cont_addr ~arity:(List.length cont_args + 1)
        in
        let wrapper_block =
          let wrapper_ks = Var.fresh () in
          let constr_cont_ks, cont_ks = DStack.cons k wrapper_ks in
          let ret = Var.fresh () in
          { params = [ x; wrapper_ks ]
          ; handler = None
          ; body =
              alloc_jump_closure
              @ constr_closure
              @ constr_cont_ks
              @ [ Let (ret, Apply (cont_closure, cont_args @ [ cont_ks ], true)) ]
          ; branch = Return ret
          }
        in
        let wrapper_addr = add_block st wrapper_block in
        let constr_wrapper, wrapper_clos = closure_of_pc wrapper_addr ~st ~arity:2 in

        let constr_f_ks, f_ks = DStack.cons wrapper_clos ks in

        ( (List.map (cps_instr st ~ks) body_prefix |> List.flatten)
          @ split
          @ constr_wrapper
          @ constr_f_ks
          @ [ Let (ret, Apply (f, args @ [ f_ks ], fully_applied)) ]
        , Return ret )
    | Some (_, Let (_, Apply _)), _ -> assert false
    | Some _, _ | None, _ ->
        let last_instrs, last = cps_last ~st ~block_addr block.branch ~ks in
        let body =
          (List.map (cps_instr st ~ks) block.body |> List.flatten)
          @ alloc_jump_closure
          @ last_instrs
        in
        body, last
  in

  { params = block.params @ [ ks ]; handler = None; body; branch = last }

let f (p : Code.program) : Code.program =
  let p =
    Code.fold_closures
      p
      (fun _ _ (start, _) ({ blocks; free_pc; _ } as p) ->
        if not @@ debug () then () else Printf.eprintf ">> Start: %d\n\n" start;

        let idom =
          let cfg = build_graph blocks start in
          dominator_tree cfg
        in

        let closure_jc = jump_closures idom in

        if debug ()
        then (
          Printf.eprintf "\nidom:\n";

          Hashtbl.iter (fun node dom -> Printf.eprintf "%d -> %d\n" node dom) idom;

          Printf.eprintf "\nClosure of alloc site:\n";
          Addr.Map.iter
            (fun block to_allocate ->
              List.iter
                (fun (cname, caddr) ->
                  Printf.eprintf "%d -> v%d, %d\n" block (Var.idx cname) caddr)
                to_allocate)
            closure_jc.closure_of_alloc_site;

          Printf.eprintf "\nClosure of jump:\n";
          Addr.Map.iter
            (fun block cname -> Printf.eprintf "%d -> v%d\n" block (Var.idx cname))
            closure_jc.closure_of_jump;
          Printf.eprintf "\n");

        let st = { new_blocks = Addr.Map.empty, free_pc; blocks; jc = closure_jc } in
        let blocks =
          Code.traverse
            { fold = Code.fold_children }
            (fun pc blocks ->
              Addr.Map.add pc (cps_block st pc (Addr.Map.find pc blocks)) blocks)
            start
            st.blocks
            st.blocks
        in
        let new_blocks, free_pc = st.new_blocks in
        let blocks = Addr.Map.fold Addr.Map.add new_blocks blocks in
        { p with blocks; free_pc })
      p
  in

  let new_start = p.free_pc in
  let blocks =
    let main = Var.fresh () in
    let main_arg = Var.fresh () in
    let args = Var.fresh () in
    let res = Var.fresh () in
    Addr.Map.add
      new_start
      { params = []
      ; handler = None
      ; body =
          [ Let (main, Closure ([ main_arg ], (p.start, [ main_arg ])))
          ; Let (args, Prim (Extern "%js_array", []))
          ; Let (res, Prim (Extern "caml_callback", [ Pv main; Pv args ]))
          ]
      ; branch = Return res
      }
      p.blocks
  in
  { start = new_start; blocks; free_pc = new_start + 1 }

let f p =
  let t = Timer.make () in
  let p' = f p in
  if Debug.find "times" () then Format.eprintf "  effects: %a@." Timer.print t;
  p'
