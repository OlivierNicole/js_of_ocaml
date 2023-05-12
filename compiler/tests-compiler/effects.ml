(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2019 Hugo Heuzard
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

open Util

let%expect_test "test-compiler/lib-effects/test1.ml" =
  let program =
    compile_and_parse
      ~effects:true
      {|

open Effect
open Effect.Deep

type _ t += E : unit t

let fff () =
  Printf.printf "%d\n%!" @@
    try_with (fun x -> x) 10
    { effc = (fun (type a) (e : a t) ->
        match e with
        | E -> Some (fun k -> 11)
        | e -> None) }
|}
  in
  (*ignore @@ Js_of_ocaml_compiler.(Js_output.program (Pretty_print.to_out_channel stdout) program);*)
  print_fun_decl program (Some "fff$0");
  print_fun_decl program (Some "fff$1");
  print_var_decl program "fff";
  [%expect
    {|
    function fff$0(param){
     var
      _p_ = [0, _d_()],
      _q_ = _f_(),
      _r_ = caml_call3(Stdlib_Effect[3][5], _q_, 10, _p_);
     return caml_call1(caml_call1(Stdlib_Printf[2], _h_), _r_);
    }
    //end
    function fff$1(param, cont){
     var _i_ = [0, _d_()], _k_ = _f_(), _j_ = 10, _l_ = Stdlib_Effect[3][5];
     return caml_cps_call4
             (_l_,
              _k_,
              _j_,
              _i_,
              function(_m_){
               var _n_ = Stdlib_Printf[2];
               return caml_cps_call2
                       (_n_,
                        _h_,
                        function(_o_){return caml_cps_call2(_o_, _m_, cont);});
              });
    }
    //end
    var fff = caml_cps_closure(fff$0, fff$1);
    //end |}]
