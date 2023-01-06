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

type cps_calls = Var.Set.t

type st =
  { mutable new_blocks : Code.block Addr.Map.t * Code.Addr.t
  ; blocks : Code.block Addr.Map.t
  ; jc : jump_closures
  ; closure_continuation : Addr.t -> Var.t
  ; cps_pc_of_direct : Addr.t -> Addr.t
  ; ident_fn : Var.t
  ; cps_calls : cps_calls ref
  }

let add_block st block =
  let blocks, free_pc = st.new_blocks in
  st.new_blocks <- Addr.Map.add free_pc block blocks, free_pc + 1;
  Format.eprintf "add_block returns %d\n%!" free_pc;
  free_pc

let closure_of_pc ~st pc =
  Format.eprintf "closure_of_pc %d\n%!" pc;
  try Addr.Map.find pc st.jc.closure_of_jump with Not_found -> assert false

let allocate_closure ~st ~params ~body ~branch =
  let block = { params = []; body; branch } in
  let pc = add_block st block in
  let name = Var.fresh () in
  [ Let (name, Closure (params, (pc, []))) ], name

let tail_call ~st ?(instrs = []) ~exact ~f args =
  let ret = Var.fresh () in
  st.cps_calls := Var.Set.add ret !(st.cps_calls);
  instrs @ [ Let (ret, Apply { f; args; exact }) ], Return ret

let cps_branch ~st (pc, args) = tail_call ~st ~exact:true ~f:(closure_of_pc ~st pc) args

let cps_jump_cont ~st cont =
  let call_block =
    let body, branch = cps_branch ~st cont in
    add_block st { params = []; body; branch }
  in
  call_block, []

let cps_last ~st (last : last) ~k : instr list * last =
  match last with
  | Return x -> tail_call ~st ~exact:true ~f:k [ x ]
  | Raise (x, _) ->
      let exn_handler = Var.fresh_n "raise" in
      tail_call
        ~st
        ~instrs:[ Let (exn_handler, Prim (Extern "caml_pop_trap", [])) ]
        ~exact:true
        ~f:exn_handler
        [ x ]
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
      let body, branch = cps_branch ~st (pc, args) in
      ( constr_handler
        @ (Let (Var.fresh (), Prim (Extern "caml_push_trap", [ Pv exn_handler ])) :: body)
      , branch )
  | Poptrap (pc, args) ->
      let body, branch = cps_branch ~st (pc, args) in
      let exn_handler = Var.fresh () in
      Let (exn_handler, Prim (Extern "caml_pop_trap", [])) :: body, branch

let cps_instr ~st:_ ~depth ~lifter_functions (instr : instr) : instr list * Var.t Var.Map.t =
  match instr with
  | Let (_c, Closure (_params, (_pc, _args))) when depth > 0 ->
      (*
      (* Also add CPS closure and create a pair *)
      let direct_c = Var.fork c in
      let cps_c = Var.fork c in
      let cps_pc = st.cps_pc_of_direct pc in
      let params' = List.map ~f:Var.fork params in
      let subst =
        List.fold_left2
          ~f:(fun m p p' -> Var.Map.add p p' m)
          ~init:Var.Map.empty
          params
          params'
      in
      ( [ Let (cps_c, Closure (params @ [ st.closure_continuation cps_pc ], (cps_pc, args)))
        ; Let (direct_c, Closure (params', (pc, args)))
        ; Let (c, Block (0, [| direct_c; cps_c |], NotArray)) ]
      , subst )
      *)
      assert false
  | Let (x, Prim (Extern "caml_alloc_dummy_function", [ size; arity ])) -> (
      match arity with
      | Pc (Int a) ->
          ( [ Let
                ( x
                , Prim (Extern "caml_alloc_dummy_function", [ size; Pc (Int (Int32.succ a)) ])
                ) ]
          , Var.Map.empty )
      | _ -> assert false)
  | Let (_, Apply { f; args = _; exact = true }) when Var.Set.mem f lifter_functions ->
      [ instr ], Var.Map.empty
  | Let (_, (Apply _ | Prim (Extern ("%resume" | "%perform" | "%reperform"), _))) ->
      assert false
  | _ -> ([ instr ], Var.Map.empty)

let concat_union (l : ('a list * 'b Var.Map.t) list) : 'a list * 'b Var.Map.t =
  List.fold_left
    l
    ~f:(fun (instrs, subst) (is,s) ->
          instrs @ is, Var.Map.union (fun _ _ -> assert false) subst s
        )
    ~init:([], Var.Map.empty)

let cps_block ~st ~k ~depth ~lifter_functions ~orig_pc ~cps_pc block =
  Format.eprintf "cps_block %d mapped to %d\n%!" orig_pc cps_pc;
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
        Some (fun ~k ->
          let f_cps = Var.fresh () in
          tail_call
            ~st
            ~instrs:[ Let (f_cps, Field (f, 1)) ]
            ~exact ~f:f_cps (args @ [ k ]))
    | Prim (Extern "%resume", [ Pv stack; Pv f; Pv arg ]) ->
        Some
          (fun ~k ->
            let k' = Var.fresh_n "cont" in
            tail_call
              ~st
              ~instrs:[ Let (k', Prim (Extern "caml_resume_stack", [ Pv stack; Pv k ])) ]
              ~exact:false
              ~f
              [ arg; k' ])
    | Prim (Extern "%perform", [ Pv effect ]) ->
        Some
          (fun ~k ->
            let x = Var.fresh () in

            ( [ Let
                  ( x
                  , Prim (Extern "caml_perform_effect", [ Pv effect; Pc (Int 0l); Pv k ])
                  )
              ]
            , Return x ))
    | Prim (Extern "%reperform", [ Pv eff; Pv continuation ]) ->
        Some
          (fun ~k ->
            let x = Var.fresh () in
            ( [ Let
                  ( x
                  , Prim (Extern "caml_perform_effect", [ Pv eff; Pv continuation; Pv k ])
                  )
              ]
            , Return x ))
    | _ -> None
  in

  let rewritten_block =
    match List.split_last block.body, block.branch with
    | Some (_, Let (_, Apply { f; args = _; exact = _ })), (Return _ | Branch _) when Var.Set.mem f lifter_functions ->
        (* No need to construct a continuation as no effect can be performed
           from a lifter function *)
        None
    | Some (body_prefix, Let (x, e)), Return ret ->
        Option.map (rewrite_instr e) ~f:(fun f ->
            assert (List.is_empty alloc_jump_closures);
            assert (Var.equal x ret);
            let instrs, branch = f ~k in
            body_prefix, instrs, branch)
    | Some (body_prefix, Let (x, e)), Branch cont ->
        let allocate_continuation f =
          let constr_cont, k' =
            (* Construct continuation: it binds the return value [x],
               allocates closures for dominated blocks and jumps to the
               next block. *)
            let pc, args = cont in
            let f' = closure_of_pc ~st pc in
            let body, branch =
              tail_call ~st ~instrs:alloc_jump_closures ~exact:true ~f:f' args
            in
            allocate_closure ~st ~params:[ x ] ~body ~branch
          in
          let instrs, branch = f ~k:k' in
          body_prefix, constr_cont @ instrs, branch
        in
        Option.map (rewrite_instr e) ~f:allocate_continuation
    | Some (_, (Set_field _ | Offset_ref _ | Array_set _ | Assign _)), _
    | Some _, (Raise _ | Stop | Cond _ | Switch _ | Pushtrap _ | Poptrap _)
    | None, _ -> None
  in

  let body, last, subst =
    match rewritten_block with
    | Some (body_prefix, last_instrs, last) ->
        let instrs, subst =
          concat_union (List.map body_prefix ~f:(fun i -> cps_instr ~st ~depth ~lifter_functions i))
        in
        instrs @ last_instrs, last, subst
    | None ->
        let last_instrs, last = cps_last ~st block.branch ~k in
        let body, subst =
          concat_union (List.map block.body ~f:(fun i -> cps_instr ~st ~depth ~lifter_functions i))
        in
        let body = body @ alloc_jump_closures @ last_instrs in
        body, last, subst
  in

  { params = block.params; body; branch = last }, subst

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
let rewrite_direct_block ~st ~pc ~depth ~lifter_functions block =
  Format.eprintf "@[<v>rewrite_direct %d, depth = %d@,@]%!" pc depth;
  let rewrite_instr = function
    | Let (x, Apply { f; args; exact }) when not (Var.Set.mem f lifter_functions) ->
        let f_direct = Var.fork f in
        ( [ Let (f_direct, Field (f, 0))
          ; Let (x, Apply { f = f_direct; args; exact }) ]
        , Var.Map.empty )
    | Let (x, Closure (params, (pc, args))) when not (Var.Set.mem x lifter_functions) ->
        let direct_c = Var.fork x in
        let cps_c = Var.fork x in
        let cps_pc = st.cps_pc_of_direct pc in
        let params' = List.map ~f:Var.fork params in
        let subst =
          List.fold_left2
            ~f:(fun m p p' -> Var.Map.add p p' m)
            ~init:Var.Map.empty
            params
            params'
        in
        ( [ Let (direct_c, Closure (params, (pc, args)))
          ; Let ( cps_c, Closure (params' @ [ st.closure_continuation cps_pc ]
                , (cps_pc, args)) )
          ; Let (x, Block (0, [| direct_c; cps_c |], NotArray)) ]
        , subst )
    | Let (x, Prim (Extern "%resume", [ Pv stack; Pv f; Pv arg ])) ->
        (* Pass the identity as a continuation and call the CPS version of [f].
           This is actually done by [caml_callback], which also installs the
           trampoline that CPS requires. *)
        let k = Var.fresh_n "cont" in
        let args = Var.fresh_n "args" in
        ( [ Let (k, Prim (Extern "caml_resume_stack", [ Pv stack; Pv st.ident_fn ]))
          ; Let (args, Prim (Extern "%js_array", [ Pv arg ]))
          ; Let (x, Prim (Extern "caml_callback", [ Pv f; Pv args ]))
          ]
        , Var.Map.empty )
    | Let (x, Prim (Extern "%perform", [ Pv effect ])) ->
        (* Perform the effect, which should call the "Unhandled effect"
           handler. *)
        let k = Int 0l in (* Will not be used *)
        ( [ Let (x, Prim (Extern "caml_perform_effect", [ Pv effect; Pc (Int 0l); Pc k ]))
          ]
        , Var.Map.empty )
    | Let (x, Prim (Extern "%reperform", [ Pv effect; Pv continuation ])) ->
        (* Similar to previous case *)
        let k = Int 0l in (* Will not be used *)
        ( [ Let (x, Prim (Extern "caml_perform_effect", [ Pv effect; Pv continuation; Pc k ]))
          ]
        , Var.Map.empty )
    | (Let _ | Assign _ | Set_field _ | Offset_ref _ | Array_set _) as instr ->
        [ instr ], Var.Map.empty
  in
  let body, subst = concat_union (List.map ~f:rewrite_instr block.body) in
  { block with body }, subst

  (*
(* Substitute all bound variables with fresh ones, also substitute as specified
   by [add]; except for variables in [remove], in a subset of
   program blocks. *)
let subst_bound_with_fresh ~block_subset ~add ~remove p =
  (*
  let bound =
    Addr.Map.fold
      (fun _ block bound ->
        Var.Set.union bound (Freevars.block_bound_vars ~closure_params:false block))
      p.Code.blocks
      Var.Set.empty
  in
  *)
  let bound =
    Code.fold_closures_depth
      p
      (fun ~depth _ _ (pc, _) bound ->
        if depth = 0 then bound
        else
          Code.traverse
            { fold = fold_children }
            (fun pc bound ->
              let block = Addr.Map.find pc p.blocks in
              Var.Set.union bound (Freevars.block_bound_vars ~closure_params:false block))
            pc
            p.blocks
            bound
      )
      Var.Set.empty
  in
  let s =
    Var.Set.fold
      (fun var m -> Var.Map.add var (Var.fork var) m)
      (Var.Set.diff bound remove)
      Var.Map.empty
  in
  let s = Var.Map.union (fun _ x _ -> Some x) add s in
  let s = Subst.from_map s in
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
    *)

let f (p : Code.program) =
  let p, lifter_functions = Lambda_lifting_simple.f p in
  Format.eprintf "@[<v>Lifting closures:@,";
  lifter_functions |> Var.Set.iter (fun v -> Format.eprintf "%s,@ " (Var.to_string v));
  Format.eprintf "@]";

  Format.eprintf "@[<v>After lambda lifting...@,";
  Code.Print.program (fun _ _ -> "") p;
  Format.eprintf "@]";

  let p = split_blocks p in

  Format.eprintf "@[<v>After block splitting...@,";
  Code.Print.program (fun _ _ -> "") p;
  Format.eprintf "@]";

  let toplevel_closures =
    Code.fold_closures_depth
      p
      (fun ~depth name _ _ toplevel_closures ->
        Format.(eprintf "@[<v>fold_closures_depth function on %a, depth = %d@,@]" (pp_print_option (fun fmt v -> pp_print_string fmt (Var.to_string v))) name depth);
        let open Var.Set in
        match depth, name with
        | 1, Some f -> add f toplevel_closures
        | _, _ -> toplevel_closures
      )
      Var.Set.empty
  in
  Format.eprintf "@[<hv 2>Toplevel closures:@ ";
  Var.Set.iter (fun v -> Format.eprintf "%s,@ " (Var.to_string v)) toplevel_closures;
  Format.eprintf "@]";

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
  let ident_fn = Var.fresh_n "identity" in
  let id_pc, p =
    let blocks =
      let id_arg = Var.fresh_n "x" in
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
  let cps_calls = ref Var.Set.empty in
  let p, cps_blocks, direct_subst, _cps_subst =
    Code.fold_closures_depth
      p
      (fun ~depth cname _ (start, _) ({ blocks; free_pc; _ } as p, cps_blocks, direct_subst, cps_subst) ->
        Option.iter cname ~f:(fun v -> Format.eprintf "cname = %s" @@ Var.to_string v);
        assert (depth <= 2); (* This should hold due to lambda lifting. *)
        (* If this a lifting closure, we don't CPS-translate it. We also
           don't need to CPS-translate the toplevel code (depth 0). *)
        if depth = 0 || match cname with Some f -> Var.Set.mem f lifter_functions | None -> false then begin
          Format.eprintf "Adapting direct closure starting at %d ;    free_pc = %d" start free_pc;
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
            ; cps_calls
            }
          in
          let blocks, direct_subst =
            Code.traverse
              { fold = Code.fold_children }
              (fun pc (blocks, direct_subst) ->
                let new_direct_block, s =
                  rewrite_direct_block
                    ~st
                    ~pc
                    ~depth
                    ~lifter_functions
                    (Addr.Map.find pc blocks)
                in
                let res = Addr.Map.add
                   pc
                   new_direct_block
                   blocks
                in
                let direct_subst = Var.Map.union (fun _ _ -> assert false) direct_subst s in
                res, direct_subst)
              start
              st.blocks
              (st.blocks, direct_subst)
          in

          let new_blocks, free_pc = st.new_blocks in
          assert (Addr.Map.is_empty new_blocks);

          Format.eprintf "finished adapting direct closure %d ;      free_pc = %d" start free_pc;
          { p with blocks; free_pc }, cps_blocks, direct_subst, cps_subst
        end
        else begin
          Format.eprintf "Translating closure starting at %d ;    " start;
          Format.eprintf "free_pc = %d\n%!" free_pc;
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
          let add_cps_translation direct_addr (mk_block : Addr.t -> block * Var.t Var.Map.t)
                : Var.t Var.Map.t =
              (* Add the block as a side effect, and return the variable
                 substitution created by the block-making function *)
              let cps_pc = st.cps_pc_of_direct direct_addr in
              let new_block, subst = mk_block cps_pc in
              let new_blocks, free_pc = st.new_blocks in
              st.new_blocks <- Addr.Map.add cps_pc new_block new_blocks, free_pc;
              subst
          in
          let k = closure_continuation start_cps in
          (* For every block in the closure,
             1. add its CPS translation to the block map at a fresh address
             2. keep the direct-style block but modify all function applications
                to take into account the fact that closure are turned into
                (direct style closure, CPS closure) pairs, and modify uses of the
                %resume and %perform primitives. *)
          let blocks, direct_subst, cps_subst =
            Code.traverse
              { fold = Code.fold_children }
              (fun pc (blocks, direct_subst, cps_subst) ->
                Format.eprintf "running block translation function ;     ";
                Format.eprintf "free_pc = %d\n%!" @@ snd @@ st.new_blocks;
                let s =
                  add_cps_translation
                    pc
                    (fun cps_pc ->
                      Format.eprintf "inner block translation function ;      ";
                      Format.eprintf "free_pc = %d\n%!" @@ snd @@ st.new_blocks;
                      Format.eprintf "Translating block %d mapped to %d, depth = %d\n%!" pc (st.cps_pc_of_direct pc) depth;
                      let res = cps_block ~st ~k ~lifter_functions ~orig_pc:pc ~cps_pc ~depth (Addr.Map.find pc blocks) in
                      Format.eprintf "end of inner block translation function ;      ";
                      Format.eprintf "free_pc = %d\n%!" @@ snd @@ st.new_blocks;
                      res
                    )
                in
                let cps_subst = Var.Map.union (fun _ _ -> assert false) cps_subst s in
                let new_direct_block, s =
                  rewrite_direct_block
                    ~st
                    ~pc
                    ~depth
                    ~lifter_functions
                    (Addr.Map.find pc blocks)
                in
                let res = Addr.Map.add
                   pc
                   new_direct_block
                   blocks
                in
                let direct_subst = Var.Map.union (fun _ _ -> assert false) direct_subst s in
                Format.eprintf "finished translating block %d ;      " pc;
                Format.eprintf "free_pc = %d\n%!" @@ snd @@ st.new_blocks;
                res, direct_subst, cps_subst)
              start
              st.blocks
              (st.blocks, direct_subst, cps_subst)
          in
          let new_blocks, free_pc = st.new_blocks in
          let cps_blocks =
            Addr.Map.fold (fun pc _ acc -> Addr.Set.add pc acc) new_blocks cps_blocks
          in

          (* Substitute all variables bound in the CPS version with fresh
             variables to avoid clashing with the definitions in the original
             blocks. *)
          let bound =
            Addr.Map.fold
              (fun _ block bound ->
                Var.Set.union bound (Freevars.block_bound_vars ~closure_params:true block)
              )
              new_blocks
              Var.Set.empty
          in
          let s =
            Var.Set.fold (fun v m -> Var.Map.add v (Var.fork v) m) bound Var.Map.empty
          in
          let new_blocks =
            Addr.Map.mapi
              (fun pc block ->
                Format.eprintf "@[<v>block before first subst: @,";
                Code.Print.block (fun _ _ -> "") pc block;
                Format.eprintf "@]";
                let res = Subst.Bound.block (Subst.from_map s) block in
                Format.eprintf "@[<v>block after first subst: @,";
                Code.Print.block (fun _ _ -> "") pc res;
                Format.eprintf "@]";
                res
              )
              new_blocks
          in

          let blocks = Addr.Map.fold Addr.Map.add new_blocks blocks in
          Format.eprintf "finished translating closure %d ;      " start;
          Format.eprintf "free_pc = %d\n%!" free_pc;
          { p with blocks; free_pc }, cps_blocks, direct_subst, cps_subst
        end)
      (p, Addr.Set.empty, Var.Map.empty, Var.Map.empty)
  in

  (* All variables that were a closure parameter in a direct-style block must
     be substituted by the CPS version of that parameter in CPS blocks
     (generated by [rewrite_direct], because CPS closures are only ever defined
     in (toplevel) direct-style blocks). *)
  let direct_subst = Subst.from_map direct_subst in
  let blocks =
    Addr.Map.mapi
      (fun pc block ->
        if Addr.Set.mem pc cps_blocks then (
          Format.eprintf "@[<v>block before second subst: @,";
          Code.Print.block (fun _ _ -> "") pc block;
          Format.eprintf "@]";
          let res = Subst.Bound.block direct_subst block in
          Format.eprintf "@[<v>block after second subst: @,";
          Code.Print.block (fun _ _ -> "") pc res;
          Format.eprintf "@]";
          res
        ) else block
      )
      p.blocks
  in
  let p = { p with blocks } in

  (*
  let all_blocks = Addr.Map.fold (fun a _ s -> Addr.Set.add a s) p.blocks Addr.Set.empty in
  let direct_blocks = Addr.Set.diff all_blocks cps_blocks in*)

  (* FIXME wrong Call [caml_callback] to set up the execution context. *)
  (* Define a global identity function. *)
  let new_start = p.free_pc in
  let blocks =
    let id_arg = Var.fresh_n "x" in
    (*
    let main = Var.fresh_n "main" in
    let args = Var.fresh_n "args" in
    let res = Var.fresh_n "res" in
    *)
    Addr.Map.add
      new_start
      { params = []
      ; body =
          [ Let (ident_fn, Closure ([ id_arg ], (id_pc, [ id_arg ])))
          (*
          ; Let (main, Closure ([], (p.start, [])))
          ; Let (args, Prim (Extern "%js_array", []))
          ; Let (res, Prim (Extern "caml_callback", [ Pv main; Pv args ]))
          *)
          ]
      ; branch = Branch (p.start, [])
      }
      p.blocks
  in
  { start = new_start; blocks; free_pc = new_start + 1 }, !cps_calls

let f p =
  let t = Timer.make () in
  let r = f p in
  if Debug.find "times" () then Format.eprintf "  effects: %a@." Timer.print t;
  r
