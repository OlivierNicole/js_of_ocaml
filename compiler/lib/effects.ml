(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, with linking exception;
 * either version 2.1 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)

(* The following CPS transform is based on the one proposed in D.
   Hillerström, S. Lindley, R. Atkey, and K. C. Sivaramakrishnan,
   “Continuation Passing Style for Effect Handlers” (FSCD 2017), with
   adaptations to account for exception handlers (which are not
   considered in detail in the paper) and for the fact that the
   language is an SSA form rather than a classical lambda calculus.

   Rather than using a stack of continuations, and effect and
   exception handlers, only the current continuation is passed between
   functions, while exception handlers and effect handlers are stored
   in global variables. This avoid having to manipulate the stack each
   time the current continuation changes. This also allows us to deal
   with exceptions from the runtime or from JavaScript code (a [try
   ... with] at the top of stack can have access to the current
   exception handler and resume the execution from there; see the
   definition of runtime function [caml_callback]).

   We rely on inlining to eliminate some administrative redexes.
*)
open! Stdlib
open Code

type graph =
  { succs : (Addr.t, Addr.Set.t) Hashtbl.t
  ; exn_handlers : (Addr.t, unit) Hashtbl.t
  ; reverse_post_order : Addr.t list
  }

let build_graph blocks pc =
  let succs = Hashtbl.create 16 in
  let exn_handlers = Hashtbl.create 16 in
  let l = ref [] in
  let visited = Hashtbl.create 16 in
  let rec traverse pc =
    if not (Hashtbl.mem visited pc)
    then (
      Hashtbl.add visited pc ();
      let successors = Code.fold_children blocks pc Addr.Set.add Addr.Set.empty in
      (match (Addr.Map.find pc blocks).branch with
      | Pushtrap (_, _, (pc', _), _) -> Hashtbl.add exn_handlers pc' ()
      | _ -> ());
      Hashtbl.add succs pc successors;
      Addr.Set.iter traverse successors;
      l := pc :: !l)
  in
  traverse pc;
  { succs; exn_handlers; reverse_post_order = !l }

let dominator_tree g =
  (* A Simple, Fast Dominance Algorithm
     Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy *)
  let dom = Hashtbl.create 16 in
  let order = Hashtbl.create 16 in
  List.iteri g.reverse_post_order ~f:(fun i pc -> Hashtbl.add order pc i);
  let rec inter pc pc' =
    (* Compute closest common ancestor *)
    if pc = pc'
    then pc
    else if Hashtbl.find order pc < Hashtbl.find order pc'
    then inter pc (Hashtbl.find dom pc')
    else inter (Hashtbl.find dom pc) pc'
  in
  List.iter g.reverse_post_order ~f:(fun pc ->
      let l = Hashtbl.find g.succs pc in
      Addr.Set.iter
        (fun pc' ->
          let d = try inter pc (Hashtbl.find dom pc') with Not_found -> pc in
          Hashtbl.replace dom pc' d)
        l);
  (* Check we have reached a fixed point (reducible graph) *)
  List.iter g.reverse_post_order ~f:(fun pc ->
      let l = Hashtbl.find g.succs pc in
      Addr.Set.iter
        (fun pc' ->
          let d = Hashtbl.find dom pc' in
          assert (inter pc d = d))
        l);

  dom

(* Each block is turned into a function which is defined in the
   dominator of the block. [closure_of_jump] provides the name of the
   function correspoding to each block. [closures_of_alloc_site]
   provides the list of functions which should be defined in a given
   block. The keys are the addresses of the original (direct-style) blocks.
   Exception handlers are dealt with separately.
*)
type jump_closures =
  { closure_of_jump : Var.t Addr.Map.t
  ; closures_of_alloc_site : (Var.t * Addr.t) list Addr.Map.t
  }

let jump_closures g idom : jump_closures =
  Hashtbl.fold
    (fun node idom_node jc ->
      if Hashtbl.mem g.exn_handlers node
      then jc
      else
        let cname = Var.fresh () in
        { closure_of_jump = Addr.Map.add node cname jc.closure_of_jump
        ; closures_of_alloc_site =
            Addr.Map.add
              idom_node
              ((cname, node)
              ::
              (try Addr.Map.find idom_node jc.closures_of_alloc_site
               with Not_found -> []))
              jc.closures_of_alloc_site
        })
    idom
    { closure_of_jump = Addr.Map.empty; closures_of_alloc_site = Addr.Map.empty }

type st =
  { mutable new_blocks : Code.block Addr.Map.t * Code.Addr.t
  ; blocks : Code.block Addr.Map.t
  ; jc : jump_closures
  ; closure_continuation : Addr.t -> Var.t
  ; cps_pc_of_direct : Addr.t -> Addr.t
  ; ident_fn : Var.t
  }

let add_block st block =
  let blocks, free_pc = st.new_blocks in
  st.new_blocks <- Addr.Map.add free_pc block blocks, free_pc + 1;
  Printf.eprintf "add_block returns %d\n%!" free_pc;
  free_pc

let closure_of_pc ~st pc =
  Printf.eprintf "closure_of_pc %d\n%!" pc;
  try Addr.Map.find pc st.jc.closure_of_jump with Not_found -> assert false

let allocate_closure ~st ~params ~body ~branch =
  let block = { params = []; body; branch } in
  let pc = add_block st block in
  let name = Var.fresh () in
  [ Let (name, Closure (params, (pc, []))) ], name

let cps_branch ~st (pc, args) =
  let ret = Var.fresh () in
  [ Let (ret, Apply { f = closure_of_pc ~st pc; args; exact = true }) ], Return ret

let cps_jump_cont ~st cont =
  let call_block =
    let body, branch = cps_branch ~st cont in
    add_block st { params = []; body; branch }
  in
  call_block, []

let cps_last ~st (last : last) ~k : instr list * last =
  match last with
  | Return x ->
      let ret = Var.fresh () in
      [ Let (ret, Apply { f = k; args = [ x ]; exact = true }) ], Return ret
  | Raise (x, _) ->
      let ret = Var.fresh () in
      let exn_handler = Var.fresh_n "raise" in
      ( [ Let (exn_handler, Prim (Extern "caml_pop_trap", []))
        ; Let (ret, Apply { f = exn_handler; args = [ x ]; exact = true })
        ]
      , Return ret )
  | Stop -> [], Stop
  | Branch cont -> cps_branch ~st cont
  | Cond (x, cont1, cont2) ->
      [], Cond (x, cps_jump_cont ~st cont1, cps_jump_cont ~st cont2)
  | Switch (x, c1, c2) ->
      (* To avoid code duplication during JavaScript generation, we need
         to create a single block per continuation *)
      let cps_jump_cont = Fun.memoize (cps_jump_cont ~st) in
      [], Switch (x, Array.map c1 ~f:cps_jump_cont, Array.map c2 ~f:cps_jump_cont)
  | Pushtrap ((pc, args), x, handler_cont, _) ->
      let constr_handler, exn_handler =
        (* Construct handler closure *)
        let handler_pc, handler_args = handler_cont in
        let handler_cps_cont = st.cps_pc_of_direct handler_pc, handler_args in
        allocate_closure ~st ~params:[ x ] ~body:[] ~branch:(Branch handler_cps_cont)
      in
      let ret = Var.fresh () in
      ( constr_handler
        @ [ Let (Var.fresh (), Prim (Extern "caml_push_trap", [ Pv exn_handler ]))
          ; Let (ret, Apply { f = closure_of_pc ~st pc; args; exact = true })
          ]
      , Return ret )
  | Poptrap (pc, args) ->
      let ret = Var.fresh () in
      let exn_handler = Var.fresh () in
      ( [ Let (exn_handler, Prim (Extern "caml_pop_trap", []))
        ; Let (ret, Apply { f = closure_of_pc ~st pc; args; exact = true })
        ]
      , Return ret )

let cps_instr ~st (instr : instr) : instr list =
  match instr with
  | Let (c, Closure (params, (pc, args))) ->
      (* Also add CPS closure (this one becomes direct style) and create a pair *)
      let direct_c = Var.fresh () in
      let cps_c = Var.fresh () in
      let cps_pc = st.cps_pc_of_direct pc in
      [ Let (cps_c, Closure (params @ [ st.closure_continuation cps_pc ], (cps_pc, args)))
      ; Let (direct_c, Closure (params, (pc, args)))
      ; Let (c, Block (0, [| direct_c; cps_c |], NotArray)) ]
  | Let (x, Prim (Extern "caml_alloc_dummy_function", [ size; arity ])) -> (
      match arity with
      | Pc (Int a) ->
          [ Let
              ( x
              , Prim (Extern "caml_alloc_dummy_function", [ size; Pc (Int (Int32.succ a)) ])
              ) ]
      | _ -> assert false)
  | Let (_, (Apply _ | Prim (Extern ("%resume" | "%perform" | "%reperform"), _))) ->
      assert false
  | _ -> [ instr ]

let cps_block ~st ~k ~orig_pc ~cps_pc block =
  Printf.eprintf "cps_block %d mapped to %d\n%!" orig_pc cps_pc;
  let alloc_jump_closures =
    match Addr.Map.find orig_pc st.jc.closures_of_alloc_site with
    | to_allocate ->
        List.map to_allocate ~f:(fun (cname, jump_pc) ->
            let jump_block = Addr.Map.find jump_pc st.blocks in
            let fresh_params = List.map jump_block.params ~f:(fun _ -> Var.fresh ()) in
            let cps_jump_pc = st.cps_pc_of_direct jump_pc in
            Let (cname, Closure (fresh_params, (cps_jump_pc, fresh_params))))
    | exception Not_found -> []
  in

  let rewrite_instr e =
    match e with
    | Apply { f; args; exact } ->
        Some (fun ~x ~k ->
          let f_cps = Var.fresh () in
          [ Let (f_cps, Field (f, 1))
          ; Let (x, Apply { f = f_cps; args = args @ [ k ]; exact }) ])
    | Prim (Extern "%resume", [ Pv stack; Pv f; Pv arg ]) ->
        Some
          (fun ~x ~k ->
            let k' = Var.fresh_n "cont" in
            [ Let (k', Prim (Extern "caml_resume_stack", [ Pv stack; Pv k ]))
            ; Let (x, Apply { f; args = [ arg; k' ]; exact = false })
            ])
    | Prim (Extern "%perform", [ Pv effect ]) ->
        Some
          (fun ~x ~k ->
            [ Let
                (x, Prim (Extern "caml_perform_effect", [ Pv effect; Pc (Int 0l); Pv k ]))
            ])
    | Prim (Extern "%reperform", [ Pv eff; Pv continuation ]) ->
        Some
          (fun ~x ~k ->
            [ Let
                (x, Prim (Extern "caml_perform_effect", [ Pv eff; Pv continuation; Pv k ]))
            ])
    | _ -> None
  in

  let rewritten_block =
    match List.split_last block.body, block.branch with
    | Some (body_prefix, Let (x, e)), Return ret ->
        Option.map (rewrite_instr e) ~f:(fun instrs ->
            assert (List.is_empty alloc_jump_closures);
            assert (Var.equal x ret);
            body_prefix, instrs ~x ~k, block.branch)
    | Some (body_prefix, Let (x, e)), Branch cont ->
        let allocate_continuation f =
          let constr_cont, k' =
            (* Construct continuation: it binds the return value [x],
               allocates closures for dominated blocks and jumps to the
               next block. *)
            let pc, args = cont in
            let ret = Var.fresh () in
            let f' = closure_of_pc ~st pc in
            allocate_closure
              ~st
              ~params:[ x ]
              ~body:
                (alloc_jump_closures @ [ Let (ret, Apply { f = f'; args; exact = true }) ])
              ~branch:(Return ret)
          in
          let ret = Var.fresh () in
          body_prefix, constr_cont @ f ~x:ret ~k:k', Return ret
        in
        Option.map (rewrite_instr e) ~f:allocate_continuation
    | Some (_, (Set_field _ | Offset_ref _ | Array_set _ | Assign _)), _
    | Some _, (Raise _ | Stop | Cond _ | Switch _ | Pushtrap _ | Poptrap _)
    | None, _ -> None
  in

  let body, last =
    match rewritten_block with
    | Some (body_prefix, last_instrs, last) ->
        List.concat (List.map body_prefix ~f:(fun i -> cps_instr ~st i))
        @ last_instrs, last
    | None ->
        let last_instrs, last = cps_last ~st block.branch ~k in
        let body =
          List.concat (List.map block.body ~f:(fun i -> cps_instr ~st i))
          @ alloc_jump_closures
          @ last_instrs
        in
        body, last
  in

  { params = block.params; body; branch = last }

let split_blocks (p : Code.program) =
  (* Ensure that function applications and effect primitives are in
     tail position *)
  let split_block pc block p =
    let is_split_point i r branch =
      match i with
      | Let (x, (Apply _ | Prim (Extern ("%resume" | "%perform" | "%reperform"), _))) -> (
          (not (List.is_empty r))
          ||
          match branch with
          | Branch _ -> false
          | Return x' -> not (Var.equal x x')
          | _ -> true)
      | _ -> false
    in
    let rec split (p : Code.program) pc block accu l branch =
      match l with
      | [] ->
          let block = { block with body = List.rev accu } in
          { p with blocks = Addr.Map.add pc block p.blocks }
      | (Let (x', e) as i) :: r when is_split_point i r branch ->
          let x = Var.fork x' in
          let pc' = p.free_pc in
          let block' = { params = [ x' ]; body = []; branch = block.branch } in
          let block =
            { block with
              body = List.rev (Let (x, e) :: accu)
            ; branch = Branch (pc', [ x ])
            }
          in
          let p = { p with blocks = Addr.Map.add pc block p.blocks; free_pc = pc' + 1 } in
          split p pc' block' [] r branch
      | i :: r -> split p pc block (i :: accu) r branch
    in
    let rec should_split l branch =
      match l with
      | [] -> false
      | i :: r -> is_split_point i r branch || should_split r branch
    in
    if should_split block.body block.branch
    then split p pc block [] block.body block.branch
    else p
  in
  Addr.Map.fold split_block p.blocks p

(* Modify all function applications and closure creations to take into account
   the fact that closure are turned into (direct style closure, CPS closure)
   pairs. Also rewrite the effect primitives to switch to the CPS versions of
   functions (for resume) or fail (for perform). *)
let rewrite_direct_block ~st block =
  let rewrite_instr = function
    | Let (x, Apply { f; args; exact }) ->
        let f_direct = Var.fresh () in
        [ Let (f_direct, Field (f, 0))
        ; Let (x, Apply { f = f_direct; args; exact }) ]
    | Let (x, Closure (params, (pc, args))) ->
        let direct_c = Var.fresh () in
        let cps_c = Var.fresh () in
        let cps_pc = st.cps_pc_of_direct pc in
        [ Let (direct_c, Closure (params, (pc, args)))
        ; Let ( cps_c, Closure (params @ [ st.closure_continuation cps_pc ]
              , (cps_pc, args)) )
        ; Let (x, Block (0, [| direct_c; cps_c |], NotArray)) ]
    | Let (x, Prim (Extern "%resume", [ Pv stack; Pv f; Pv arg ])) ->
        (* Pass the identity as a continuation and call the CPS version of [f] *)
        let k = Var.fresh () in
        let f_cps = Var.fresh () in
        [ Let (k, Prim (Extern "caml_resume_stack", [ Pv stack; Pv st.ident_fn ]))
        ; Let (f_cps, Field (f, 2))
        ; Let (x, Apply { f = f_cps; args = [ arg; k ]; exact = false })
        ]
    | Let (x, Prim (Extern "%perform", [ Pv effect ])) ->
        (* Perform the effect, which should call the "Unhandled effect"
           handler. *)
        let k = Int 0l in (* Will not be used *)
        [ Let (x, Prim (Extern "caml_perform_effect", [ Pv effect; Pc (Int 0l); Pc k ]))
        ]
    | Let (x, Prim (Extern "%reperform", [ Pv effect; Pv continuation ])) ->
        (* Similar to previous case *)
        let k = Int 0l in (* Will not be used *)
        [ Let (x, Prim (Extern "caml_perform_effect", [ Pv effect; Pv continuation; Pc k ]))
        ]
    | (Let _ | Assign _ | Set_field _ | Offset_ref _ | Array_set _) as instr ->
        [ instr ]
  in
  { block with body = List.concat_map ~f:rewrite_instr block.body }

(* Substitute all bound variables with fresh ones, in a subset of program blocks. *)
let subst_bound_with_fresh ~block_subset p =
  let bound =
    Addr.Map.fold
      (fun _ block bound ->
        Var.Set.union bound (Freevars.block_bound_vars ~closure_params:true block))
      p.Code.blocks
      Var.Set.empty
  in
  let s =
    let tbl = Hashtbl.create (Var.count ()) in
    fun v ->
      try Hashtbl.find tbl (Var.idx v)
      with Not_found ->
        let new_ = if Var.Set.mem v bound then Var.fresh () else v in
        Hashtbl.add tbl (Var.idx v) new_;
        new_
  in
  let blocks =
    Addr.Map.mapi
      (fun pc block ->
        if Addr.Set.mem pc block_subset then begin
          Format.eprintf "@[<v>block before subst: @,";
          Code.Print.block (fun _ _ -> "") pc block;
          Format.eprintf "@]";
          let res = Subst.Bound.block s block in
          Format.eprintf "@[<v>block after subst: @,";
          Code.Print.block (fun _ _ -> "") pc res;
          Format.eprintf "@]";
          res
        end else block
        )
      p.blocks
  in
  { p with blocks }

let f (p : Code.program) =
  let p = split_blocks p in
  let closure_continuation =
    (* Provide a name for the continuation of a closure (before CPS
       transform), which can be referred from all the blocks it contains *)
    let tbl = Hashtbl.create 4 in
    fun pc ->
      try Hashtbl.find tbl pc
      with Not_found ->
        let k = Var.fresh_n "cont" in
        Hashtbl.add tbl pc k;
        k
  in
  let cps_pc_of_direct =
    (* Provide the address of the CPS translation of a block *)
    let tbl = Hashtbl.create 4 in
    fun ~st pc ->
      try Hashtbl.find tbl pc
      with Not_found ->
        let new_blocks, free_pc = st.new_blocks in
        st.new_blocks <- new_blocks, free_pc + 1;
        Hashtbl.add tbl pc free_pc;
        free_pc
  in
  (* Define an identity function, needed for the boilerplate around "resume" *)
  let ident_fn = Var.fresh () in
  let id_pc, p =
    let blocks =
      let id_arg = Var.fresh () in
      Addr.Map.add
        p.free_pc
        { params = [ id_arg ]
        ; body = []
        ; branch = Return id_arg
        }
        p.blocks
    in
    p.free_pc, { start = p.start; blocks; free_pc = p.free_pc + 1 }
  in
  let p, cps_blocks =
    Code.fold_closures
      p
      (fun _ _ (start, _) ({ blocks; free_pc; _ } as p, cps_blocks) ->
        Printf.eprintf "Translating closure starting at %d ;    " start;
        Printf.eprintf "free_pc = %d\n%!" free_pc;
        let cfg = build_graph blocks start in
        let closure_jc =
          let idom = dominator_tree cfg in
          jump_closures cfg idom in
        let rec st =
          { new_blocks = Addr.Map.empty, free_pc
          ; blocks
          ; jc = closure_jc
          ; closure_continuation
          ; ident_fn
          ; cps_pc_of_direct = fun pc -> cps_pc_of_direct ~st pc
          }
        in
        let start_cps = st.cps_pc_of_direct start in
        let add_cps_translation : Addr.t -> (Addr.t -> block) -> unit =
          fun direct_addr mk_block ->
            let cps_pc = st.cps_pc_of_direct direct_addr in
            let new_block = mk_block cps_pc in
            let new_blocks, free_pc = st.new_blocks in
            st.new_blocks <- Addr.Map.add cps_pc new_block new_blocks, free_pc
        in
        let k = closure_continuation start_cps in
        (* For every block in the closure,
           1. add its CPS translation to the block map at a fresh address
           2. keep the direct-style block but modify all function applications
              to take into account the fact that closure are turned into
              (direct style closure, CPS closure) pairs, and modify uses of the
              %resume and %perform primitives. *)
        let blocks =
          Code.traverse
            { fold = Code.fold_children }
            (fun pc blocks ->
              Printf.eprintf "running block translation function ;     ";
              Printf.eprintf "free_pc = %d\n%!" @@ snd @@ st.new_blocks;
              add_cps_translation
                pc
                (fun cps_pc ->
                  Printf.eprintf "inner block translation function ;      ";
                  Printf.eprintf "free_pc = %d\n%!" @@ snd @@ st.new_blocks;
                  Printf.eprintf "Translating block %d mapped to %d\n%!" pc (st.cps_pc_of_direct pc);
                  let res = cps_block ~st ~k ~orig_pc:pc ~cps_pc (Addr.Map.find pc blocks) in
                  Printf.eprintf "end of inner block translation function ;      ";
                  Printf.eprintf "free_pc = %d\n%!" @@ snd @@ st.new_blocks;
                  res
                );
              let res = Addr.Map.add
                 pc
                 (rewrite_direct_block ~st (Addr.Map.find pc blocks))
                 blocks in
              Printf.eprintf "finished translating block %d ;      " pc;
              Printf.eprintf "free_pc = %d\n%!" @@ snd @@ st.new_blocks;
              res)
            start
            st.blocks
            st.blocks
        in
        let new_blocks, free_pc = st.new_blocks in
        let blocks = Addr.Map.fold Addr.Map.add new_blocks blocks in
        let cps_blocks =
          Addr.Map.fold (fun pc _ acc -> Addr.Set.add pc acc) new_blocks cps_blocks
        in
        Printf.eprintf "finished translating closure %d ;      " start;
        Printf.eprintf "free_pc = %d\n%!" free_pc;
        { p with blocks; free_pc }, cps_blocks)
      (p, Addr.Set.empty)
  in

  (* Substitute all variables bound in the CPS blocks with fresh variables to
     avoid clashing with the definitions in the original blocks. *)
  let p = subst_bound_with_fresh ~block_subset:cps_blocks p in

  (* Call [caml_callback] to set up the execution context. *)
  let new_start = p.free_pc in
  let blocks =
    let id_arg = Var.fresh () in
    let main = Var.fresh () in
    let args = Var.fresh () in
    let res = Var.fresh () in
    Addr.Map.add
      new_start
      { params = []
      ; body =
          [ Let (ident_fn, Closure ([ id_arg ], (id_pc, [ id_arg ])))
          ; Let (main, Closure ([], (p.start, [])))
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
  let r = f p in
  if Debug.find "times" () then Format.eprintf "  effects: %a@." Timer.print t;
  r
