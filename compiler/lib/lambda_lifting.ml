(*
- clean-up
- timer
*)
open Code

let baseline = 1

let threshold = 50

let collect_free_vars program var_depth depth pc =
  let vars = ref Var.Set.empty in
  let rec traverse pc =
    Code.preorder_traverse
      { fold = Code.fold_children }
      (fun pc () ->
        let block = Code.Addr.Map.find pc program.blocks in
        Freevars.iter_block_free_vars
          (fun x ->
            let idx = Var.idx x in
            if idx < Array.length var_depth
            then (
              let d = var_depth.(idx) in
              if d < 0 then Format.eprintf "ZZZ v%d %s@." idx (Code.Var.to_string x);
              if d < depth then vars := Var.Set.add x !vars))
          block;
        List.iter
          (fun i ->
            match i with
            | Let (_, Closure (_, (pc', _))) -> traverse pc'
            | _ -> ())
          block.body)
      pc
      program.blocks
      ()
  in
  traverse pc;
  !vars

let rec traverse var_depth program pc depth limit =
  Code.preorder_traverse
    { fold = Code.fold_children }
    (fun pc (program, functions) ->
      let block = Code.Addr.Map.find pc program.blocks in
      Freevars.iter_block_bound_vars (fun x -> var_depth.(Var.idx x) <- depth) block;
      List.iter
        (fun i ->
          match i with
          | Let (_, Closure (params, _)) ->
              List.iter (fun x -> var_depth.(Var.idx x) <- depth + 1) params
          | _ -> ())
        block.body;

      let rec rewrite_body first (program, functions) l =
        match l with
        | Let (f, (Closure (_, (pc', _)) as cl)) :: rem
          when first
               && depth >= limit
               &&
               match rem with
               | Let (_, Closure _) :: _ -> false
               | _ -> true ->
            let program, functions' =
              traverse var_depth program pc' (depth + 1) (depth + threshold)
            in
            let free_vars = collect_free_vars program var_depth (depth + 1) pc' in
            let s =
              Var.Set.fold
                (fun x m -> Var.Map.add x (Var.fork x) m)
                free_vars
                Var.Map.empty
            in
            let program = Subst.cont (Subst.from_map s) pc' program in
            let f' = try Var.Map.find f s with Not_found -> Var.fork f in
            let s = Var.Map.bindings (Var.Map.remove f s) in
            let f'' = Var.fork f in
            Format.eprintf
              "LIFT %d %d %b v%d@."
              depth
              pc'
              (Var.Set.mem f free_vars)
              (Var.idx f'');

            let pc'' = program.free_pc in
            let bl =
              { params = []; body = [ Let (f', cl) ]; branch = Return f'; handler = None }
            in
            let program =
              { program with
                free_pc = pc'' + 1
              ; blocks = Addr.Map.add pc'' bl program.blocks
              }
            in

            let functions =
              (Let (f'', Closure (List.map snd s, (pc'', []))) :: functions') @ functions
            in

            let rem', program, functions = rewrite_body false (program, functions) rem in
            Let (f, Apply (f'', List.map fst s, true)) :: rem', program, functions
        | (Let (_, Closure (_, (pc', _))) as i) :: rem ->
            let program, functions' = traverse var_depth program pc' (depth + 1) limit in
            let rem', program, functions =
              rewrite_body false (program, functions' @ functions) rem
            in
            if depth = baseline && functions' <> []
            then (
              prerr_endline "-----";
              List.iter
                (fun i ->
                  match i with
                  | Let (x, _) -> Format.eprintf "ADDED (%d) v%d@." pc' (Code.Var.idx x)
                  | _ -> ())
                functions');
            if depth = baseline
            then functions' @ (i :: rem), program, []
            else i :: rem', program, functions
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
  let program, functions =
    traverse var_depth program program.start 0 (baseline + threshold)
  in
  assert (functions = []);
  prerr_endline "AAAAAAAAAAAAAAA";
  Code.Print.program (fun _ _ -> "") program;
  program
