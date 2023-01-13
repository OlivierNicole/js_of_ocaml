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

open! Stdlib
open Code

let debug = Debug.find "lifting_simple"

let baseline = 0 (* Depth to which the functions are lifted *)

let rec compute_depth program pc =
  Code.preorder_traverse
    { fold = Code.fold_children }
    (fun pc d ->
      let block = Code.Addr.Map.find pc program.blocks in
      List.fold_left block.body ~init:d ~f:(fun d i ->
          match i with
          | Let (_, Closure (_, (pc', _))) ->
              let d' = compute_depth program pc' in
              max d (d' + 1)
          | _ -> d))
    pc
    program.blocks
    0

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
              assert (d >= 0);
              if d > baseline && d < depth then vars := Var.Set.add x !vars))
          block;
        List.iter block.body ~f:(fun i ->
            match i with
            | Let (_, Closure (_, (pc', _))) -> traverse pc'
            | _ -> ()))
      pc
      program.blocks
      ()
  in
  traverse pc;
  !vars

let mark_bound_variables var_depth block depth =
  Freevars.iter_block_bound_vars (fun x -> var_depth.(Var.idx x) <- depth) block;
  List.iter block.body ~f:(fun i ->
      match i with
      | Let (_, Closure (params, _)) ->
          List.iter params ~f:(fun x -> var_depth.(Var.idx x) <- depth + 1)
      | _ -> ())

let rec traverse var_depth (program, functions) pc depth =
  Code.preorder_traverse
    { fold = Code.fold_children }
    (fun pc (program, functions) ->
      let block = Code.Addr.Map.find pc program.blocks in
      mark_bound_variables var_depth block depth;
      if depth = 0
      then (
        assert (List.is_empty functions);
        let program, body =
          List.fold_right block.body ~init:(program, []) ~f:(fun i (program, rem) ->
              match i with
              | Let (_, Closure (_, (pc', _))) as i ->
                  let program, functions =
                    traverse var_depth (program, []) pc' (depth + 1)
                  in
                  program, List.rev_append functions (i :: rem)
              | i -> program, i :: rem)
        in
        { program with blocks = Addr.Map.add pc { block with body } program.blocks }, [])
      else
        (* We lift possibly mutually recursive closures (that are created by
           contiguous statements) together. Isolated closures are lambda-lifted
           normally. *)
        let does_not_start_with_closure l =
          match l with
          | Let (_, Closure _) :: _ -> false
          | _ -> true
        in
        let rec rewrite_body current_contiguous st l =
          match l with
          | Let (f, (Closure (_, (pc', _)) as cl)) :: rem
            when List.is_empty current_contiguous && does_not_start_with_closure rem ->
              (* We lift an isolated closure *)
              let program, functions =
                traverse var_depth st pc' (depth + 1)
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
              if debug ()
              then
                Format.eprintf
                  "LIFT %s (depth:%d free_vars:%d inner_depth:%d)@."
                  (Code.Var.to_string f'')
                  depth
                  (Var.Set.cardinal free_vars)
                  (compute_depth program pc');
              let pc'' = program.free_pc in
              let bl = { params = []; body = [ Let (f', cl) ]; branch = Return f' } in
              let program =
                { program with
                  free_pc = pc'' + 1
                ; blocks = Addr.Map.add pc'' bl program.blocks
                }
              in
              let functions =
                Let (f'', Closure (List.map s ~f:snd, (pc'', []))) :: functions
              in
              let rem', st = rewrite_body [] (program, functions) rem in
              assert (
                (not (List.is_empty rem'))
                ||
                match block.branch with
                | Return _ -> false
                | _ -> true);
              ( Let (f, Apply { f = f''; args = List.map ~f:fst s; exact = true })
                :: rem'
              , st )
          | (Let (cname, Closure (params, (pc', args)))) :: rem ->
              let st = traverse var_depth st pc' (depth + 1) in
              rewrite_body ((cname, params, pc', args) :: current_contiguous) st rem
          | i :: rem ->
              assert (List.length current_contiguous <> 1);
              begin match current_contiguous with
              | [] ->
                  let rem', st = rewrite_body [] st rem in
                  i :: rem', st
              | _ ->
                  let free_vars =
                    List.fold_left
                      current_contiguous
                      ~f:(fun acc (_,_,pc,_) ->
                            Var.Set.union acc
                            @@ collect_free_vars program var_depth (depth + 1) pc)
                      ~init:Var.Set.empty
                  in
                  let s =
                    Var.Set.fold
                      (fun x m -> Var.Map.add x (Var.fork x) m)
                      free_vars
                      Var.Map.empty
                  in
                  let program =
                    List.fold_left
                      current_contiguous
                      ~f:(fun program (_,_,pc,_) ->
                            Subst.cont (Subst.from_map s) pc program)
                      ~init:program
                  in
                  let f's =
                    List.map
                      current_contiguous
                      ~f:(fun (f,_,_,_) ->
                            Var.(try Map.find f s with Not_found -> fork f))
                  in
                  let s =
                    List.fold_left
                      current_contiguous
                      ~f:(fun s (f,_,_,_) -> Var.Map.remove f s)
                      ~init:s
                    |> Var.Map.bindings
                  in
                  let f_tuple = Var.fresh_n "recfuncs" in
                  if debug ()
                  then
                    Format.(eprintf
                      "LIFT %a in tuple %s (depth:%d free_vars:%d)@,"
                      (pp_print_list ~pp_sep:pp_print_space pp_print_string)
                      (List.map ~f:Code.Var.to_string f's)
                      (Code.Var.to_string f_tuple)
                      depth
                      (Var.Set.cardinal free_vars));
                  let pc_tuple = program.free_pc in
                  let lifted_block =
                    let tuple = Var.fresh_n "tuple" in
                    { params = []
                    ; body =
                        List.map2
                          f's
                          current_contiguous
                          ~f:(fun f' (_, params, pc, args) ->
                                Let (f', Closure (params, (pc, args))))
                        @ [ Let (tuple, Block (0, Array.of_list f's, NotArray)) ]
                    ; branch = Return tuple }
                  in
                  let program =
                    { program with
                      free_pc = pc_tuple + 1
                    ; blocks = Addr.Map.add pc_tuple lifted_block program.blocks
                    }
                  in
                  let functions =
                    Let (f_tuple, Closure (List.map s ~f:snd, (pc_tuple, [])))
                    :: functions
                  in
                  let rem', st = rewrite_body [] (program, functions) rem in
                  assert (
                    not (List.is_empty rem')
                    || match block.branch with | Return _ -> false | _ -> true);
                  ( let tuple = Var.fresh_n "tuple" in
                    Let
                      ( tuple
                      , Apply { f = f_tuple; args = List.map ~f:fst s; exact = true } )
                    :: List.mapi
                         current_contiguous
                         ~f:(fun i (f,_,_,_) ->
                               Let (f, Field (tuple, i)))
                    @ i
                    :: rem'
                  , st )
              end
          | [] -> [], st
        in
        let body, (program, functions) =
          rewrite_body [] (program, functions) block.body
        in
        ( { program with blocks = Addr.Map.add pc { block with body } program.blocks }
        , functions ))
    pc
    program.blocks
    (program, functions)

let f program =
  let t = Timer.make () in
  let nv = Var.count () in
  let var_depth = Array.make nv (-1) in
  let program, functions =
    traverse var_depth (program, []) program.start 0
  in
  assert (List.is_empty functions);
  if Debug.find "times" () then Format.eprintf "  lambda lifting: %a@." Timer.print t;
  program
