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
  let code =
    compile_and_parse
      ~effects:true
      {|
         let exceptions s =
           (* Compiled using 'try ... catch',
              and 'throw' within the try block *)
           let n = try int_of_string s with Failure _ -> 0 in
           let m =
             try if s = "" then raise Not_found else 7 with Not_found -> 0 in
           (* Uses caml_{push,pop}_trap. *)
           try
             if s = "" then raise Not_found;
             Some (open_in "toto", n, m)
            with Not_found ->
             None

         let handler_is_loop f g l =
           try f ()
           with exn ->
             let rec loop l =
               match g l with
               | `Fallback l' -> loop l'
               | `Raise exn -> raise exn
             in
             loop l

         let handler_is_merge_node g =
           let s = try g () with _ -> "" in
           s ^ "aaa"
       |}
  in
  print_fun_decl code (Some "exceptions");
  [%expect
    {|

    function exceptions(s, cont){
     try{var _s_ = runtime.caml_int_of_string(s), n = _s_;}
     catch(_w_){
      var _l_ = caml_wrap_exception(_w_);
      if(_l_[1] !== Stdlib[7]){
       var raise$1 = caml_pop_trap();
       return raise$1(caml_maybe_attach_backtrace(_l_, 0));
      }
      var n = 0, _m_ = 0;
     }
     try{
      if(caml_string_equal(s, cst$0))
       throw caml_maybe_attach_backtrace(Stdlib[8], 1);
      var _r_ = 7, m = _r_;
     }
     catch(_v_){
      var _n_ = caml_wrap_exception(_v_);
      if(_n_ !== Stdlib[8]){
       var raise$0 = caml_pop_trap();
       return raise$0(caml_maybe_attach_backtrace(_n_, 0));
      }
      var m = 0, _o_ = 0;
     }
     caml_push_trap
      (function(_u_){
        if(_u_ === Stdlib[8]) return cont(0);
        var raise = caml_pop_trap();
        return raise(caml_maybe_attach_backtrace(_u_, 0));
       });
     if(caml_string_equal(s, cst)){
      var _p_ = Stdlib[8], raise = caml_pop_trap();
      return raise(caml_maybe_attach_backtrace(_p_, 1));
     }
     var _q_ = Stdlib[79];
     return caml_cps_call2
             (_q_,
              cst_toto,
              function(_t_){caml_pop_trap(); return cont([0, [0, _t_, n, m]]);});
    }
    //end |}];
  print_fun_decl code (Some "handler_is_loop");
  [%expect
    {|
    function handler_is_loop(f, g, l, cont){
     caml_push_trap
      (function(_j_){
        function _k_(l){
         return caml_cps_call2
                 (g,
                  l,
                  function(match){
                   if(72330306 <= match[1]){
                    var l = match[2];
                    return caml_cps_exact_call1(_k_, l);
                   }
                   var
                    exn = match[2],
                    raise = caml_pop_trap(),
                    exn$0 = caml_maybe_attach_backtrace(exn, 1);
                   return raise(exn$0);
                  });
        }
        return _k_(l);
       });
     var _h_ = 0;
     return caml_cps_call2
             (f, _h_, function(_i_){caml_pop_trap(); return cont(_i_);});
    }
    //end |}];
  print_fun_decl code (Some "handler_is_merge_node");
  [%expect
    {|
    function handler_is_merge_node(g, cont){
     function _e_(s){return caml_cps_call3(Stdlib[28], s, cst_aaa, cont);}
     caml_push_trap(function(_g_){return _e_(cst$1);});
     var _d_ = 0;
     return caml_cps_call2
             (g, _d_, function(_f_){caml_pop_trap(); return _e_(_f_);});
    }
    //end |}]
