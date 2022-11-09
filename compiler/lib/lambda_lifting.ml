(*
level of all variables
===> level 0 are not touched; free variable if less than function level


lift functions that are too deep and not in mutual recursion

traverse function to find free variables
return function + substitution


g = function (freevars) { function f (params) { body }}

function f (params) {body} -->
    apply g (freevars)
*)
open Code

let threshold = 40

let rec traverse var_depth program pc depth limit =
  Code.traverse
    { fold = Code.fold_children }
    (fun pc (program, functions) ->
      let block = Code.Addr.Map.find pc program.blocks in
      Freevars.iter_block_bound_vars (fun x -> var_depth.(Var.idx x) <- depth) block;

      let rec rewrite_body first (program, functions) l =
        match l with
        | (Let (_, Closure (_, (pc', _))) as i) :: rem
          when first
               && depth >= limit
               &&
               match rem with
               | Let (_, Closure _) :: _ -> false
               | _ -> true ->
            let program, functions =
              traverse var_depth program pc' (depth + 1) (depth + threshold)
            in
            Format.eprintf "LIFT %d@." depth;
            (*
              let program =
                (* Compute free variables *)
                let s = Var.Map.empty in
                Subst.cont (Subst.from_map s) pc' program
              in
*)
            let rem', program, functions' = rewrite_body false (program, functions) rem in
            i :: rem', program, functions @ functions'
        | (Let (_, Closure (_, (pc', _))) as i) :: rem ->
            let program, functions = traverse var_depth program pc' (depth + 1) limit in
            let rem', program, functions' = rewrite_body false (program, functions) rem in
            if depth = 0
            then functions @ (i :: rem), program, []
            else i :: rem', program, functions @ functions'
        | i :: rem ->
            let rem', program, functions = rewrite_body true (program, functions) rem in
            i :: rem', program, functions
        | [] -> [], program, functions
      in
      let body, program, functions = rewrite_body true (program, functions) block.body in
      ( { program with blocks = Addr.Map.add pc { block with body } program.blocks }
      , functions ))
    pc
    program.blocks
    (program, [])

let f program =
  let nv = Var.count () in
  let var_depth = Array.make nv (-1) in
  let program, functions = traverse var_depth program program.start 0 threshold in
  assert (functions = []);
  program
