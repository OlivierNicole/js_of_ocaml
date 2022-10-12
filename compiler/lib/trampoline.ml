open! Stdlib
open Code

let direct_call_block block ~x ~f ~args =
  let return = Code.Var.fork x in
  { block with
    params = []
  ; body = [ Let (return, Apply (f, args, true)) ]
  ; branch = Return return
  }

let bounce_call_block block ~x ~f ~args =
  let return = Code.Var.fork x in
  let new_args = Code.Var.fresh () in
  { block with
    params = []
  ; body =
      [ Let (new_args, Prim (Extern "%js_array", List.map args ~f:(fun x -> Pv x)))
      ; Let (return, Prim (Extern "caml_trampoline_return", [ Pv f; Pv new_args ]))
      ]
  ; branch = Return return
  }

let trampoline_block ~program ~pc ~block =
  match block.branch with
  | Return ret -> (
      match List.split_last block.body with
      | Some (body_prefix, Let (x, Apply (f, args, true))) when Var.equal x ret ->
          let { free_pc; blocks; _ } = program in
          let direct_call_pc = free_pc in
          let bounce_call_pc = free_pc + 1 in
          let free_pc = free_pc + 2 in
          let blocks =
            Addr.Map.add direct_call_pc (direct_call_block block ~x ~f ~args) blocks
          in
          let blocks =
            Addr.Map.add bounce_call_pc (bounce_call_block block ~x ~f ~args) blocks
          in

          let direct = Code.Var.fresh () in
          let branch = Cond (direct, (direct_call_pc, []), (bounce_call_pc, [])) in
          let last = Let (direct, Prim (Extern "caml_stack_check_depth", [])) in
          let blocks =
            Addr.Map.add pc { block with body = body_prefix @ [ last ]; branch } blocks
          in

          { program with free_pc; blocks }
      | _ -> program)
  | Stop | Branch _ | Cond (_, _, _) | Switch (_, _, _) | Raise (_, _) -> program
  | Poptrap (_, _)
  | Pushtrap (_, _, _, _)
  | Resume (_, _, _)
  | Perform (_, _, _)
  | Reperform (_, _) -> assert false

let f program =
  Addr.Map.fold
    (fun pc block program -> trampoline_block ~program ~pc ~block)
    program.blocks
    program
