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
*)
open! Stdlib
open Code

let debug = Debug.find "effects"

let debug_print fmt =
  if debug () then Format.(eprintf (fmt ^^ "%!")) else Format.(ifprintf err_formatter fmt)

let get_edges g src = try Hashtbl.find g src with Not_found -> Addr.Set.empty

let add_edge g src dst = Hashtbl.replace g src (Addr.Set.add dst (get_edges g src))

let reverse_graph g =
  let g' = Hashtbl.create 16 in
  Hashtbl.iter
    (fun child parents -> Addr.Set.iter (fun parent -> add_edge g' parent child) parents)
    g;
  g'

type control_flow_graph =
  { succs : (Addr.t, Addr.Set.t) Hashtbl.t
  ; preds : (Addr.t, Addr.Set.t) Hashtbl.t
  ; reverse_post_order : Addr.t list
  ; block_order : (Addr.t, int) Hashtbl.t
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
      Hashtbl.add succs pc successors;
      Addr.Set.iter traverse successors;
      l := pc :: !l)
  in
  traverse pc;
  let block_order = Hashtbl.create 16 in
  List.iteri !l ~f:(fun i pc -> Hashtbl.add block_order pc i);
  let preds = reverse_graph succs in
  { succs; preds; reverse_post_order = !l; block_order }

let dominator_tree g =
  (* A Simple, Fast Dominance Algorithm
     Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy *)
  let dom = Hashtbl.create 16 in
  let rec inter pc pc' =
    (* Compute closest common ancestor *)
    if pc = pc'
    then pc
    else if Hashtbl.find g.block_order pc < Hashtbl.find g.block_order pc'
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

(* pc dominates pc' *)
let rec dominates g idom pc pc' =
  pc = pc'
  || Hashtbl.find g.block_order pc < Hashtbl.find g.block_order pc'
     && dominates g idom pc (Hashtbl.find idom pc')

(* pc has at least two forward edges moving into it *)
let is_merge_node g pc =
  let s = try Hashtbl.find g.preds pc with Not_found -> assert false in
  let o = Hashtbl.find g.block_order pc in
  let n =
    Addr.Set.fold
      (fun pc' n -> if Hashtbl.find g.block_order pc' < o then n + 1 else n)
      s
      0
  in
  n > 1

let dominance_frontier g idom =
  let frontiers = Hashtbl.create 16 in
  Hashtbl.iter
    (fun pc preds ->
      if Addr.Set.cardinal preds > 1
      then
        let dom = Hashtbl.find idom pc in
        let rec loop runner =
          if runner <> dom
          then (
            add_edge frontiers runner pc;
            loop (Hashtbl.find idom runner))
        in
        Addr.Set.iter loop preds)
    g.preds;
  frontiers

(****)

(*
We establish the list of blocks that needs to be CPS-transformed. We
also mark blocks that correspond to function continuations or
exception handlers. And we keep track of the exception handler
associated to each Poptrap, and possibly Raise.
*)
let compute_needed_transformations ~cfg ~idom ~cps_needed ~blocks ~start =
  let frontiers = dominance_frontier cfg idom in
  let transformation_needed = ref Addr.Set.empty in
  let matching_exn_handler = Hashtbl.create 16 in
  let is_continuation = Hashtbl.create 16 in
  let rec mark_needed pc =
    (* If a block is transformed, all the blocks in its dominance
       frontier needs to be transformed as well. *)
    if not (Addr.Set.mem pc !transformation_needed)
    then (
      transformation_needed := Addr.Set.add pc !transformation_needed;
      Addr.Set.iter mark_needed (get_edges frontiers pc))
  in
  let mark_continuation pc x =
    if not (Hashtbl.mem is_continuation pc)
    then
      Hashtbl.add
        is_continuation
        pc
        (if Addr.Set.mem pc (get_edges frontiers pc) then `Loop else `Param x)
  in
  let rec traverse visited ~englobing_exn_handlers pc =
    if Addr.Set.mem pc visited
    then visited
    else
      let visited = Addr.Set.add pc visited in
      let block = Addr.Map.find pc blocks in
      (match fst block.branch with
      | Branch (dst, _) -> (
          match List.last block.body with
          | Some
              ( Let
                  (x, (Apply _ | Prim (Extern ("%resume" | "%perform" | "%reperform"), _)))
              , _ )
            when Var.Set.mem x cps_needed ->
              (* The block after a function application that needs to
                 be turned to CPS or an effect primitive needs to be
                 transformed. *)
              mark_needed dst;
              (* We need to transform the englobing exception handlers
                 as well *)
              List.iter ~f:mark_needed englobing_exn_handlers;
              mark_continuation dst x
          | _ -> ())
      | Pushtrap (_, x, (handler_pc, _), _) -> mark_continuation handler_pc x
      | Poptrap _ | Raise _ -> (
          match englobing_exn_handlers with
          | handler_pc :: _ -> Hashtbl.add matching_exn_handler pc handler_pc
          | _ -> ())
      | _ -> ());
      Code.fold_children
        blocks
        pc
        (fun pc visited ->
          let englobing_exn_handlers =
            match block.branch with
            | Pushtrap (_, _, (handler_pc, _), _), _ when pc <> handler_pc ->
                handler_pc :: englobing_exn_handlers
            | Poptrap _, _ -> List.tl englobing_exn_handlers
            | _ -> englobing_exn_handlers
          in
          traverse visited ~englobing_exn_handlers pc)
        visited
  in
  ignore @@ traverse Addr.Set.empty ~englobing_exn_handlers:[] start;
  !transformation_needed, matching_exn_handler, is_continuation

(****)

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

let jump_closures blocks_to_transform idom : jump_closures =
  Hashtbl.fold
    (fun node idom_node jc ->
      match Addr.Set.mem node blocks_to_transform with
      | false -> jc
      | true ->
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

type cps_calls = Var.Set.t

type single_version_closures = Var.Set.t

type st =
  { mutable new_blocks : Code.block Addr.Map.t * Code.Addr.t
  ; blocks : Code.block Addr.Map.t
  ; cfg : control_flow_graph
  ; idom : (int, int) Hashtbl.t
  ; jc : jump_closures
  ; cps_needed : Var.Set.t
  ; blocks_to_transform : Addr.Set.t
  ; is_continuation : (Addr.t, [ `Param of Var.t | `Loop ]) Hashtbl.t
  ; matching_exn_handler : (Addr.t, Addr.t) Hashtbl.t
  ; block_order : (Addr.t, int) Hashtbl.t
  ; live_vars : Deadcode.variable_uses
  ; flow_info : Global_flow.info
  ; cps_calls : cps_calls ref
  ; cps_pc_of_direct : (int, int) Hashtbl.t
  ; single_version_closures : single_version_closures ref
  }

let add_block st block =
  let blocks, free_pc = st.new_blocks in
  st.new_blocks <- Addr.Map.add free_pc block blocks, free_pc + 1;
  free_pc

(* Provide the address of the CPS translation of a block *)
let mk_cps_pc_of_direct ~st pc =
  try Hashtbl.find st.cps_pc_of_direct pc
  with Not_found ->
    let new_blocks, free_pc = st.new_blocks in
    st.new_blocks <- new_blocks, free_pc + 1;
    Hashtbl.add st.cps_pc_of_direct pc free_pc;
    free_pc

let cps_cont_of_direct ~st (pc, args) = mk_cps_pc_of_direct ~st pc, args

let closure_of_pc ~st pc =
  try Addr.Map.find pc st.jc.closure_of_jump with Not_found -> assert false

let allocate_closure ~st ~params ~body ~branch loc =
  let block = { params = []; body; branch } in
  let pc = add_block st block in
  let name = Var.fresh () in
  [ Let (name, Closure (params, (pc, []))), loc ], name

let mark_single_version ~st cname =
  st.single_version_closures := Var.Set.add cname !(st.single_version_closures)

let tail_call ~st ?(instrs = []) ~exact ~check ~f args loc =
  assert (exact || check);
  let ret = Var.fresh () in
  if check then st.cps_calls := Var.Set.add ret !(st.cps_calls);
  instrs @ [ Let (ret, Apply { f; args; exact }), loc ], (Return ret, loc)

let cps_branch ~st ~src (pc, args) loc =
  match Addr.Set.mem pc st.blocks_to_transform with
  | false -> [], (Branch (pc, args), loc)
  | true ->
      let args, instrs =
        if List.is_empty args && Hashtbl.mem st.is_continuation pc
        then
          (* We are jumping to a block that is also used as a continuation.
             We pass it a dummy argument. *)
          let x = Var.fresh () in
          [ x ], [ Let (x, Constant (Int 0l)), noloc ]
        else args, []
      in
      (* We check the stack depth only for backward edges (so, at
         least once per loop iteration) *)
      let check = Hashtbl.find st.block_order src >= Hashtbl.find st.block_order pc in
      let f = closure_of_pc ~st pc in
      mark_single_version ~st f;
      tail_call ~st ~instrs ~exact:true ~check ~f args loc

let cps_jump_cont ~st ~src ((pc, _) as cont) loc =
  match Addr.Set.mem pc st.blocks_to_transform with
  | false -> cont
  | true ->
      let call_block =
        let body, branch = cps_branch ~st ~src cont loc in
        add_block st { params = []; body; branch }
      in
      call_block, []

let allocate_continuation
    ~st
    ~alloc_jump_closures
    ~split_closures
    ~direct_pc
    src_pc
    x
    cont
    loc =
  (* We need to allocate an additional closure if [cont]
     does not correspond to a continuation that binds [x].
     This closure binds the return value [x], allocates
     closures for dominated blocks and jumps to the next
     block. When entering a loop, we also have to allocate a
     closure to bind [x] if it is used in the loop body. In
     other cases, we can just pass the closure corresponding
     to the next block. *)
  let _, args = cont in
  if (match args with
     | [] -> true
     | [ x' ] -> Var.equal x x'
     | _ -> false)
     &&
     match Hashtbl.find st.is_continuation direct_pc with
     | `Param _ -> true
     | `Loop -> st.live_vars.(Var.idx x) = List.length args
  then alloc_jump_closures, closure_of_pc ~st direct_pc
  else
    let body, branch = cps_branch ~st ~src:src_pc cont loc in
    let inner_closures, outer_closures =
      (* For [Pushtrap], we need to separate the closures
         corresponding to the exception handler body (that may make
         use of [x]) from the other closures that may be used outside
         of the exception handler. *)
      if not split_closures
      then alloc_jump_closures, []
      else if is_merge_node st.cfg direct_pc
      then [], alloc_jump_closures
      else
        List.partition
          ~f:(fun (i, _) ->
            match i with
            | Let (_, Closure (_, (pc'', []))) -> dominates st.cfg st.idom direct_pc pc''
            | _ -> assert false)
          alloc_jump_closures
    in
    let body, branch =
      allocate_closure ~st ~params:[ x ] ~body:(inner_closures @ body) ~branch loc
    in
    outer_closures @ body, branch

let cps_last ~st ~alloc_jump_closures pc ((last, last_loc) : last * loc) ~k :
    (instr * loc) list * (last * loc) =
  match last with
  | Return x ->
      assert (List.is_empty alloc_jump_closures);
      (* Is the number of successive 'returns' is unbounded is CPS, it
         means that we have an unbounded of calls in direct style
         (even with tail call optimization) *)
      tail_call ~st ~exact:true ~check:false ~f:k [ x ] last_loc
  | Raise (x, rmode) -> (
      assert (List.is_empty alloc_jump_closures);
      match Hashtbl.find_opt st.matching_exn_handler pc with
      | Some pc when not (Addr.Set.mem pc st.blocks_to_transform) ->
          (* We are within a try ... with which is not
             transformed. We should raise an exception normally *)
          [], (last, last_loc)
      | _ ->
          let exn_handler = Var.fresh_n "raise" in
          let x, instrs =
            match rmode with
            | `Notrace -> x, []
            | (`Normal | `Reraise) as m ->
                let x' = Var.fork x in
                let force =
                  match m with
                  | `Normal -> true
                  | `Reraise -> false
                in
                let i =
                  [ ( Let
                        ( x'
                        , Prim
                            ( Extern "caml_maybe_attach_backtrace"
                            , [ Pv x; Pc (Int (if force then 1l else 0l)) ] ) )
                    , noloc )
                  ]
                in
                x', i
          in
          tail_call
            ~st
            ~instrs:
              ((Let (exn_handler, Prim (Extern "caml_pop_trap", [])), noloc) :: instrs)
            ~exact:true
            ~check:false
            ~f:exn_handler
            [ x ]
            last_loc)
  | Stop ->
      assert (List.is_empty alloc_jump_closures);
      [], (Stop, last_loc)
  | Branch cont ->
      let body, branch = cps_branch ~st ~src:pc cont last_loc in
      alloc_jump_closures @ body, branch
  | Cond (x, cont1, cont2) ->
      ( alloc_jump_closures
      , ( Cond
            ( x
            , cps_jump_cont ~st ~src:pc cont1 last_loc
            , cps_jump_cont ~st ~src:pc cont2 last_loc )
        , last_loc ) )
  | Switch (x, c1, c2) ->
      (* To avoid code duplication during JavaScript generation, we need
         to create a single block per continuation *)
      let cps_jump_cont = Fun.memoize (fun x -> cps_jump_cont ~st ~src:pc x last_loc) in
      ( alloc_jump_closures
      , ( Switch (x, Array.map c1 ~f:cps_jump_cont, Array.map c2 ~f:cps_jump_cont)
        , last_loc ) )
  | Pushtrap (body_cont, exn, ((handler_pc, _) as handler_cont), _) -> (
      assert (Hashtbl.mem st.is_continuation handler_pc);
      match Addr.Set.mem handler_pc st.blocks_to_transform with
      | false -> alloc_jump_closures, (last, last_loc)
      | true ->
          let handler_cps_cont = cps_cont_of_direct ~st handler_cont in
          let constr_cont, exn_handler =
            allocate_continuation
              ~st
              ~alloc_jump_closures
              ~split_closures:true
              ~direct_pc:handler_pc
              pc
              exn
              handler_cps_cont
              last_loc
          in
          mark_single_version ~st exn_handler;
          let push_trap =
            Let (Var.fresh (), Prim (Extern "caml_push_trap", [ Pv exn_handler ])), noloc
          in
          let body, branch = cps_branch ~st ~src:pc body_cont last_loc in
          constr_cont @ (push_trap :: body), branch)
  | Poptrap cont -> (
      match
        Addr.Set.mem (Hashtbl.find st.matching_exn_handler pc) st.blocks_to_transform
      with
      | false ->
          ( alloc_jump_closures
          , (Poptrap (cps_jump_cont ~st ~src:pc cont last_loc), last_loc) )
      | true ->
          let exn_handler = Var.fresh () in
          let body, branch = cps_branch ~st ~src:pc cont last_loc in
          ( alloc_jump_closures
            @ ((Let (exn_handler, Prim (Extern "caml_pop_trap", [])), noloc) :: body)
          , branch ))

let cps_instr ~st (instr : instr) : instr =
  match instr with
  | Let (_, Closure _) ->
      (* Due to the preliminary lambda lifting, all functions should be created
         at toplevel. And toplevel code does not need to be CPS-transformed.
         Therefore, there can never be a closure creation in code that needs to
         be CPS-transformed. *)
      assert false
  (* FIXME remove
     | Let (x, Closure (params, (pc, _))) when Var.Set.mem x st.cps_needed ->
         (* Add the continuation parameter, and change the initial block if
            needed *)
         let k, cont = Hashtbl.find st.closure_info pc in
         Let (x, Closure (params @ [ k ], cont))
  *)
  | Let (x, Prim (Extern "caml_alloc_dummy_function", [ size; arity ])) -> (
      match arity with
      | Pc (Int a) ->
          Let
            ( x
            , Prim (Extern "caml_alloc_dummy_function", [ size; Pc (Int (Int32.succ a)) ])
            )
      | _ -> assert false)
  | Let (x, Apply { f; args; _ }) when not (Var.Set.mem x st.cps_needed) ->
      (* At the moment, we turn into CPS any function not called with
         the right number of parameter *)
      assert (Global_flow.exact_call st.flow_info f (List.length args));
      Let (x, Apply { f; args; exact = true })
  | Let (_, (Apply _ | Prim (Extern ("%resume" | "%perform" | "%reperform"), _))) ->
      assert false
  | _ -> instr

let cps_block ~st ~k ~lifter_functions ~orig_pc block =
  debug_print "cps_block %d\n" orig_pc;
  let alloc_jump_closures =
    match Addr.Map.find orig_pc st.jc.closures_of_alloc_site with
    | to_allocate ->
        List.map to_allocate ~f:(fun (cname, jump_pc) ->
            let params =
              let jump_block = Addr.Map.find jump_pc st.blocks in
              (* For a function to be used as a continuation, it needs
                 exactly one parameter. So, we add a parameter if
                 needed. *)
              if List.is_empty jump_block.params && Hashtbl.mem st.is_continuation jump_pc
              then
                (* We reuse the name of the value of the tail call of
                   one a the previous blocks. When there is a single
                   previous block, this is exactly what we want. For a
                   merge node, the variable is not used so we can just
                   as well use it. For a loop, we don't want the
                   return value of a call right before entering the
                   loop to be overriden by the value returned by the
                   last call in the loop. So, we may need to use an
                   additional closure to bind it, and we have to use a
                   fresh variable here *)
                let x =
                  match Hashtbl.find st.is_continuation jump_pc with
                  | `Param x -> x
                  | `Loop -> Var.fresh ()
                in
                [ x ]
              else jump_block.params
            in
            mark_single_version ~st cname;
            let cps_jump_pc = mk_cps_pc_of_direct ~st jump_pc in
            Let (cname, Closure (params, (cps_jump_pc, []))), noloc)
    | exception Not_found -> []
  in

  let rewrite_instr x e loc =
    let perform_effect ~effect ~continuation loc =
      Some
        (fun ~k ->
          let e =
            Prim (Extern "caml_perform_effect", [ Pv effect; continuation; Pv k ])
          in
          let x = Var.fresh () in
          [ Let (x, e), loc ], (Return x, loc))
    in
    match e with
    | Apply { f; args; exact } when Var.Set.mem x st.cps_needed ->
        Some
          (fun ~k ->
            let exact =
              exact || Global_flow.exact_call st.flow_info f (List.length args)
            in
            tail_call ~st ~exact ~check:true ~f (args @ [ k ]) loc)
    | Prim (Extern "%resume", [ Pv stack; Pv f; Pv arg ]) ->
        Some
          (fun ~k ->
            let k' = Var.fresh_n "cont" in
            tail_call
              ~st
              ~instrs:
                [ Let (k', Prim (Extern "caml_resume_stack", [ Pv stack; Pv k ])), noloc ]
              ~exact:(Global_flow.exact_call st.flow_info f 1)
              ~check:true
              ~f
              [ arg; k' ]
              loc)
    | Prim (Extern "%perform", [ Pv effect ]) ->
        perform_effect ~effect ~continuation:(Pc (Int 0l)) loc
    | Prim (Extern "%reperform", [ Pv effect; continuation ]) ->
        perform_effect ~effect ~continuation loc
    | _ -> None
  in

  let rewritten_block =
    match List.split_last block.body, block.branch with
    | Some (_, (Let (_, Apply { f; args = _; exact = _ }), _)), ((Return _ | Branch _), _)
      when Var.Set.mem f lifter_functions ->
        (* No need to construct a continuation as no effect can be performed from a
           lifter function *)
        None
    | Some (body_prefix, (Let (x, e), loc)), (Return ret, _loc_ret) ->
        Option.map (rewrite_instr x e loc) ~f:(fun f ->
            assert (List.is_empty alloc_jump_closures);
            assert (Var.equal x ret);
            let instrs, branch = f ~k in
            body_prefix, instrs, branch)
    | Some (body_prefix, (Let (x, e), loc)), (Branch (direct_pc, _ as cont), loc_ret) ->
        let cps_cont = cps_cont_of_direct ~st cont in
        Option.map (rewrite_instr x e loc) ~f:(fun f ->
            let constr_cont, k' =
              allocate_continuation
                ~st
                ~alloc_jump_closures
                ~split_closures:false
                ~direct_pc
                orig_pc
                x
                cps_cont
                loc_ret
            in
            let instrs, branch = f ~k:k' in
            body_prefix, constr_cont @ instrs, branch)
    | Some (_, ((Set_field _ | Offset_ref _ | Array_set _ | Assign _), _)), _
    | Some _, ((Raise _ | Stop | Cond _ | Switch _ | Pushtrap _ | Poptrap _), _)
    | None, _ -> None
  in

  let body, last =
    match rewritten_block with
    | Some (body_prefix, last_instrs, last) ->
        List.map body_prefix ~f:(fun (i, loc) -> cps_instr ~st i, loc) @ last_instrs, last
    | None ->
        let last_instrs, last =
          cps_last ~st ~alloc_jump_closures orig_pc block.branch ~k
        in
        let body =
          List.map block.body ~f:(fun (i, loc) -> cps_instr ~st i, loc) @ last_instrs
        in
        body, last
  in

  { params = (if Addr.Set.mem orig_pc st.blocks_to_transform then [] else block.params)
  ; body
  ; branch = last
  }

let concat_union : ('a list * 'b Var.Map.t) list -> 'a list * 'b Var.Map.t =
  List.fold_left
    ~f:(fun (instrs, subst) (is, s) ->
      instrs @ is, Var.Map.union (fun _ _ -> assert false) subst s)
    ~init:([], Var.Map.empty)

(* Modify all function applications and closure creations to take into account
   the fact that closures are turned (direct style, CPS) closure pairs. Also
   rewrite the effect primitives to switch to the CPS version of functions (for
   resume) or fail (for perform).
   For each closure created in the original code, two closures are now created.
   The parameters of the CPS closure are duplicated from the original one.
   However, we need to maintain the invariant that all variables are bound
   exactly once. This is done by creating fresh arguments for each CPS closure
   and returning a substitution from the original parameters to the new ones,
   that must be applied to all code that might use the original parameters. *)
let rewrite_direct_block
    ~cps_needed
    ~closure_info
    ~ident_fn
    ~pc
    ~lifter_functions
    block =
  debug_print "@[<v>rewrite_direct_block %d@,@]" pc;
  let rewrite_instr = function
    | Let (x, Closure (params, ((pc, _) as cont)))
      when Var.Set.mem x cps_needed && not (Var.Set.mem x lifter_functions) ->
        let direct_c = Var.fork x in
        let cps_c = Var.fork x in
        let params' = List.map ~f:Var.fork params in
        let subst =
          List.fold_left2
            ~f:(fun m p p' -> Var.Map.add p p' m)
            ~init:Var.Map.empty
            params
            params'
        in
        let k, cps_cont = Hashtbl.find closure_info pc in
        ( [ Let (direct_c, Closure (params, cont))
          ; Let (cps_c, Closure (params' @ [ k ], cps_cont))
          ; Let (x, Prim (Extern "caml_cps_closure", [ Pv direct_c; Pv cps_c ]))
          ]
        , subst )
    | Let (x, Prim (Extern "%resume", [ Pv stack; Pv f; Pv arg ])) ->
        (* Pass the identity as a continuation and pass to
           [caml_trampoline_cps], which will 1. install a trampoline, 2. call
           the CPS version of [f] and 3. handle exceptions. *)
        let k = Var.fresh_n "cont" in
        let args = Var.fresh_n "args" in
        ( [ Let (k, Prim (Extern "caml_resume_stack", [ Pv stack; Pv ident_fn ]))
          ; Let (args, Prim (Extern "%js_array", [ Pv arg; Pv k ]))
          ; Let (x, Prim (Extern "caml_trampoline_cps", [ Pv f; Pv args ]))
          ]
        , Var.Map.empty )
    | Let (x, Prim (Extern "%perform", [ Pv effect ])) ->
        (* Perform the effect, which should call the "Unhandled effect" handler. *)
        let k = Int 0l in
        (* Dummy continuation *)
        ( [ Let (x, Prim (Extern "caml_perform_effect", [ Pv effect; Pc (Int 0l); Pc k ]))
          ]
        , Var.Map.empty )
    | Let (x, Prim (Extern "%reperform", [ Pv effect; Pv continuation ])) ->
        (* Similar to previous case *)
        let k = Int 0l in
        ( [ Let
              ( x
              , Prim (Extern "caml_perform_effect", [ Pv effect; Pv continuation; Pc k ])
              )
          ]
        , Var.Map.empty )
    | (Let _ | Assign _ | Set_field _ | Offset_ref _ | Array_set _) as instr ->
        [ instr ], Var.Map.empty
  in
  let body, subst =
    (* For each instruction... *)
    List.map block.body ~f:(fun (i, loc) ->
        (* ... apply [rewrite_instr] ... *)
        let instrs, subst = rewrite_instr i in
        (* ... and decorate all resulting instructions with [loc] *)
        List.map ~f:(fun i -> i, loc) instrs, subst)
    |> concat_union (* Merge the resulting variable substitutions into one *)
  in
  { block with body }, subst

(* Apply a substitution in a *)
let subst_blocks blocks s =
  Addr.Map.mapi
    (fun pc block ->
      if debug ()
      then (
        debug_print "@[<v>block before first subst: @,";
        Code.Print.block (fun _ _ -> "") pc block;
        debug_print "@]");
      let res = Subst.Bound.block s block in
      if debug ()
      then (
        debug_print "@[<v>block after first subst: @,";
        Code.Print.block (fun _ _ -> "") pc res;
        debug_print "@]");
      res)
    blocks

let cps_transform ~lifter_functions ~live_vars ~flow_info ~cps_needed p =
  (* Define an identity function, needed for the boilerplate around "resume" *)
  let ident_fn = Var.fresh_n "identity" in
  let id_pc, p =
    let blocks =
      let id_arg = Var.fresh_n "x" in
      Addr.Map.add
        p.free_pc
        { params = [ id_arg ]; body = []; branch = Return id_arg, noloc }
        p.blocks
    in
    p.free_pc, { start = p.start; blocks; free_pc = p.free_pc + 1 }
  in
  let p =
    let id_arg = Var.fresh_n "x" in
    let blocks =
      Addr.Map.add
        p.free_pc
        { params = []
        ; body = [ Let (ident_fn, Closure ([ id_arg ], (id_pc, [ id_arg ]))), noloc ]
        ; branch = Branch (p.start, []), noloc
        }
        p.blocks
    in
    { start = p.free_pc; blocks; free_pc = p.free_pc + 1 }
  in
  let closure_info = Hashtbl.create 16 in
  let cps_calls = ref Var.Set.empty in
  let single_version_closures = ref lifter_functions in
  let cps_pc_of_direct = Hashtbl.create 512 in
  let p =
    Code.fold_closures_innermost_first
      p
      (fun name_opt _ (start, args) ({ blocks; free_pc; _ } as p) ->
        Option.iter name_opt ~f:(fun v -> debug_print "cname = %s" @@ Var.to_string v);
        (* We speculatively add a block at the beginning of the
           function. In case of tail-recursion optimization, the
           function implementing the loop body may have to be placed
           there. *)
        let initial_start = start in
        let start', blocks' =
          ( free_pc
          , Addr.Map.add
              free_pc
              { params = []; body = []; branch = Branch (start, args), noloc }
              blocks )
        in
        let cfg = build_graph blocks' start' in
        let idom = dominator_tree cfg in
        let should_compute_needed_transformations =
          match name_opt with
          | Some name -> Var.Set.mem name cps_needed
          | None ->
              (* We are handling the toplevel code. There may remain
                 some CPS calls at toplevel. *)
              true
        in
        let blocks_to_transform, matching_exn_handler, is_continuation =
          if should_compute_needed_transformations
          then
            compute_needed_transformations
              ~cfg
              ~idom
              ~cps_needed
              ~blocks:blocks'
              ~start:start'
          else Addr.Set.empty, Hashtbl.create 1, Hashtbl.create 1
        in
        let closure_jc = jump_closures blocks_to_transform idom in
        let start, args, blocks, free_pc =
          (* Insert an initial block if needed. *)
          if Addr.Map.mem start' closure_jc.closures_of_alloc_site
          then start', [], blocks', free_pc + 1
          else start, args, blocks, free_pc
        in
        let st =
          { new_blocks = Addr.Map.empty, free_pc
          ; blocks
          ; cfg
          ; idom
          ; jc = closure_jc
          ; cps_needed
          ; blocks_to_transform
          ; is_continuation
          ; matching_exn_handler
          ; block_order = cfg.block_order
          ; flow_info
          ; live_vars
          ; cps_calls
          ; cps_pc_of_direct
          ; single_version_closures
          }
        in
        let function_needs_cps =
          match name_opt with
          | Some name ->
              should_compute_needed_transformations
              && not (Var.Set.mem name lifter_functions)
          | None ->
              (* We are handling the toplevel code. If it performs no
                 CPS call, we can leave it in direct style and we
                 don't need to wrap it within a [caml_callback]. *)
              not (Addr.Set.is_empty blocks_to_transform)
        in
        if debug ()
        then (
          Format.eprintf "======== %b@." function_needs_cps;
          Code.preorder_traverse
            { fold = Code.fold_children }
            (fun pc _ ->
              if Addr.Set.mem pc blocks_to_transform then Format.eprintf "CPS@.";
              let block = Addr.Map.find pc blocks in
              Code.Print.block
                (fun _ xi -> Partial_cps_analysis.annot cps_needed xi)
                pc
                block)
            start
            blocks
            ());
        let blocks =
          (* For every block in the closure,
             1. add its CPS translation to the block map at a fresh address, if
               needed
             2. keep the direct-style block but modify all function applications
                to take into account the fact that some closure are turned into
                (direct style closure, CPS closure) pairs, and modify uses of the
                %resume and %perform primitives. *)
          let transform_block =
            if function_needs_cps
            then (
              let k = Var.fresh_n "cont" in
              let cps_start = mk_cps_pc_of_direct ~st start in
              Hashtbl.add closure_info initial_start (k, (cps_start, args));
              fun pc block ->
                let cps_block = cps_block ~st ~lifter_functions ~k ~orig_pc:pc block in
                ( rewrite_direct_block
                    ~cps_needed
                    ~closure_info
                    ~ident_fn
                    ~pc
                    ~lifter_functions
                    block
                , Some cps_block ))
            else
              fun pc block ->
              ( rewrite_direct_block
                  ~cps_needed
                  ~closure_info
                  ~ident_fn
                  ~pc
                  ~lifter_functions
                  block
              , None )
          in
          let blocks, direct_subst =
            Code.traverse
              { fold = Code.fold_children }
              (fun pc (blocks, direct_subst) ->
                let (block, s), cps_block_opt =
                  transform_block pc (Addr.Map.find pc blocks)
                in
                let s = Var.Map.union (fun _ _ -> assert false) direct_subst s in
                let blocks = Addr.Map.add pc block blocks in
                match cps_block_opt with
                | None -> blocks, s
                | Some b ->
                    let cps_pc = mk_cps_pc_of_direct ~st pc in
                    Addr.Map.add cps_pc b blocks, s)
              start
              st.blocks
              (st.blocks, Var.Map.empty)
          in
          let cps_blocks, _ = st.new_blocks in
          (* Substitute all variables bound in the CPS version with fresh
             variables to avoid clashing with the definitions in the original
             blocks. *)
          let bound =
            Addr.Map.fold
              (fun _ block bound ->
                Var.Set.union bound (Freevars.block_bound_vars ~closure_params:true block))
              cps_blocks
              Var.Set.empty
          in
          let s =
            Var.Set.fold (fun v m -> Var.Map.add v (Var.fork v) m) bound Var.Map.empty
            |> Subst.from_map
          in
          let cps_blocks = subst_blocks cps_blocks s in
          (* Also apply susbstitution to set of CPS calls and lifter functions *)
          st.cps_calls := Var.Set.map s !(st.cps_calls);
          st.single_version_closures := Var.Set.map s !(st.single_version_closures);
          (* All variables that were a closure parameter in a direct-style block must be
             substituted by the CPS version of that parameter in CPS blocks (generated by
             [rewrite_direct], because CPS closures are only ever defined in (toplevel)
             direct-style blocks). *)
          let direct_subst = Subst.from_map direct_subst in
          let cps_blocks = subst_blocks cps_blocks direct_subst in
          (* Also apply susbstitution to set of CPS calls and lifter functions *)
          st.cps_calls := Var.Set.map direct_subst !(st.cps_calls);
          st.single_version_closures :=
            Var.Set.map direct_subst !(st.single_version_closures);
          let blocks = Addr.Map.fold Addr.Map.add cps_blocks blocks in
          blocks
        in
        { p with blocks; free_pc })
      p
  in
  let p =
    match Hashtbl.find_opt closure_info p.start with
    | None -> p
    | Some (k, _) ->
        (* Call [caml_callback] to set up the execution context. *)
        let new_start = p.free_pc in
        let blocks =
          let main = Var.fresh () in
          let args = Var.fresh () in
          let res = Var.fresh () in
          Addr.Map.add
            new_start
            { params = []
            ; body =
                [ Let (main, Closure ([ k ], (p.start, []))), noloc
                ; Let (args, Prim (Extern "%js_array", [])), noloc
                ; Let (res, Prim (Extern "caml_callback", [ Pv main; Pv args ])), noloc
                ]
            ; branch = Return res, noloc
            }
            p.blocks
        in
        { start = new_start; blocks; free_pc = new_start + 1 }
  in
  let p =
    (* Initialize the global fiber stack and define a global identity function *)
    let new_start = p.free_pc in
    let blocks =
      let id_arg = Var.fresh_n "x" in
      let dummy = Var.fresh_n "dummy" in
      Addr.Map.add
        new_start
        { params = []
        ; body =
            [ Let (ident_fn, Closure ([ id_arg ], (id_pc, [ id_arg ]))), noloc
            ; Let (dummy, Prim (Extern "caml_initialize_fiber_stack", [])), noloc
            ]
        ; branch = Branch (p.start, []), noloc
        }
        p.blocks
    in
    { start = new_start; blocks; free_pc = new_start + 1 }
  in
  p, !cps_calls, !single_version_closures

(****)

let current_loop_header frontiers in_loop pc =
  (* We remain in a loop while the loop header is in the dominance frontier.
     We enter a loop when the block is in its dominance frontier. *)
  let frontier = get_edges frontiers pc in
  match in_loop with
  | Some header when Addr.Set.mem header frontier -> in_loop
  | _ -> if Addr.Set.mem pc frontier then Some pc else None

let wrap_call ~cps_needed p x f args accu loc =
  let arg_array = Var.fresh () in
  ( p
  , Var.Set.remove x cps_needed
  , [ Let (arg_array, Prim (Extern "%js_array", List.map ~f:(fun y -> Pv y) args)), noloc
    ; Let (x, Prim (Extern "caml_callback", [ Pv f; Pv arg_array ])), loc
    ]
    :: accu )

let wrap_primitive ~cps_needed p x e accu loc =
  let f = Var.fresh () in
  let closure_pc = p.free_pc in
  ( { p with
      free_pc = p.free_pc + 1
    ; blocks =
        Addr.Map.add
          closure_pc
          (let y = Var.fresh () in
           { params = []; body = [ Let (y, e), loc ]; branch = Return y, loc })
          p.blocks
    }
  , Var.Set.remove x (Var.Set.add f cps_needed)
  , let args = Var.fresh () in
    [ Let (f, Closure ([], (closure_pc, []))), noloc
    ; Let (args, Prim (Extern "%js_array", [])), noloc
    ; Let (x, Prim (Extern "caml_callback", [ Pv f; Pv args ])), loc
    ]
    :: accu )

let rewrite_toplevel_instr (p, cps_needed, accu) instr =
  match instr with
  | Let (x, Apply { f; args; _ }), loc when Var.Set.mem x cps_needed ->
      wrap_call ~cps_needed p x f args accu loc
  | Let (x, (Prim (Extern ("%resume" | "%perform" | "%reperform"), _) as e)), loc ->
      wrap_primitive ~cps_needed p x e accu loc
  | _ -> p, cps_needed, [ instr ] :: accu

(* FIXME remove? *)
(* Wrap function calls inside [caml_callback] at toplevel to avoid
   unncessary function nestings. This is not done inside loops since
   using repeatedly [caml_callback] can be costly. *)
let[@warning "-32"] rewrite_toplevel ~cps_needed p =
  let { start; blocks; _ } = p in
  let cfg = build_graph blocks start in
  let idom = dominator_tree cfg in
  let frontiers = dominance_frontier cfg idom in
  let rec traverse visited (p : Code.program) cps_needed in_loop pc =
    if Addr.Set.mem pc visited
    then visited, p, cps_needed
    else
      let visited = Addr.Set.add pc visited in
      let in_loop = current_loop_header frontiers in_loop pc in
      let p, cps_needed =
        if Option.is_none in_loop
        then
          let block = Addr.Map.find pc p.blocks in
          let p, cps_needed, body_rev =
            List.fold_left ~f:rewrite_toplevel_instr ~init:(p, cps_needed, []) block.body
          in
          let body = List.concat @@ List.rev body_rev in
          { p with blocks = Addr.Map.add pc { block with body } p.blocks }, cps_needed
        else p, cps_needed
      in
      Code.fold_children
        blocks
        pc
        (fun pc (visited, p, cps_needed) -> traverse visited p cps_needed in_loop pc)
        (visited, p, cps_needed)
  in
  let _, p, cps_needed = traverse Addr.Set.empty p cps_needed None start in
  p, cps_needed

(****)

let split_blocks ~cps_needed (p : Code.program) =
  (* Ensure that function applications and effect primitives are in
     tail position *)
  let split_block pc block p =
    let is_split_point i r branch =
      match i with
      | Let (x, (Apply _ | Prim (Extern ("%resume" | "%perform" | "%reperform"), _))) ->
          ((not (List.is_empty r))
          ||
          match fst branch with
          | Branch _ -> false
          | Return x' -> not (Var.equal x x')
          | _ -> true)
          && Var.Set.mem x cps_needed
      | _ -> false
    in
    let rec split (p : Code.program) pc block accu l branch =
      match l with
      | [] ->
          let block = { block with body = List.rev accu } in
          { p with blocks = Addr.Map.add pc block p.blocks }
      | ((Let (x, e) as i), loc) :: r when is_split_point i r branch ->
          let pc' = p.free_pc in
          let block' = { params = []; body = []; branch = block.branch } in
          let block =
            { block with
              body = List.rev ((Let (x, e), loc) :: accu)
            ; branch = Branch (pc', []), noloc
            }
          in
          let p = { p with blocks = Addr.Map.add pc block p.blocks; free_pc = pc' + 1 } in
          split p pc' block' [] r branch
      | i :: r -> split p pc block (i :: accu) r branch
    in
    let rec should_split l branch =
      match l with
      | [] -> false
      | (i, _) :: r -> is_split_point i r branch || should_split r branch
    in
    if should_split block.body block.branch
    then split p pc block [] block.body block.branch
    else p
  in
  Addr.Map.fold split_block p.blocks p

(****)

let remove_empty_blocks ~live_vars (p : Code.program) : Code.program =
  let shortcuts = Hashtbl.create 16 in
  let rec resolve_rec visited ((pc, args) as cont) =
    if Addr.Set.mem pc visited
    then cont
    else
      match Hashtbl.find_opt shortcuts pc with
      | Some (params, cont) ->
          let pc', args' = resolve_rec (Addr.Set.add pc visited) cont in
          let s = Subst.from_map (Subst.build_mapping params args) in
          pc', List.map ~f:s args'
      | None -> cont
  in
  let resolve cont = resolve_rec Addr.Set.empty cont in
  Addr.Map.iter
    (fun pc block ->
      match block with
      | { params; body = []; branch = Branch cont, _; _ } ->
          let args =
            List.fold_left
              ~f:(fun args x -> Var.Set.add x args)
              ~init:Var.Set.empty
              (snd cont)
          in
          (* We can skip an empty block if its parameters are only
             used as argument to the continuation *)
          if List.for_all
               ~f:(fun x -> live_vars.(Var.idx x) = 1 && Var.Set.mem x args)
               params
          then Hashtbl.add shortcuts pc (params, cont)
      | _ -> ())
    p.blocks;
  let blocks =
    Addr.Map.map
      (fun block ->
        { block with
          branch =
            (let branch, loc = block.branch in
             let branch =
               match branch with
               | Branch cont -> Branch (resolve cont)
               | Cond (x, cont1, cont2) -> Cond (x, resolve cont1, resolve cont2)
               | Switch (x, a1, a2) ->
                   Switch (x, Array.map ~f:resolve a1, Array.map ~f:resolve a2)
               | Pushtrap (cont1, x, cont2, s) ->
                   Pushtrap (resolve cont1, x, resolve cont2, s)
               | Poptrap cont -> Poptrap (resolve cont)
               | Return _ | Raise _ | Stop -> branch
             in
             branch, loc)
        })
      p.blocks
  in
  { p with blocks }

(****)

let f (p, live_vars) =
  let t = Timer.make () in
  let p, lifter_functions = Lambda_lifting_simple.f p in
  if debug ()
  then (
    debug_print "@[<v>Lifting closures:@,";
    lifter_functions |> Var.Set.iter (fun v -> debug_print "%s,@ " (Var.to_string v));
    debug_print "@]";
    debug_print "@[<v>After lambda lifting...@,";
    Code.Print.program (fun _ _ -> "") p;
    debug_print "@]");
  let p = remove_empty_blocks ~live_vars p in
  let flow_info = Global_flow.f p in
  let cps_needed = Partial_cps_analysis.f p flow_info in
  (* FIXME incompatible with dynamic switching?
     let p, cps_needed = rewrite_toplevel ~cps_needed p in
  *)
  let p = split_blocks ~cps_needed p in
  let p, cps_calls, single_version_closures =
    cps_transform ~lifter_functions ~live_vars ~flow_info ~cps_needed p
  in
  if Debug.find "times" () then Format.eprintf "  effects: %a@." Timer.print t;
  p, cps_calls, single_version_closures
