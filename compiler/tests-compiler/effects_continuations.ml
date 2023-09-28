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

         let list_rev = List.rev
         (* Avoid to expose the offset of stdlib modules *)
         let () = ignore (list_rev [])

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

         (* Conditional whose result is used *)
         let cond1 b =
           let ic = if b then open_in "toto" else open_in "titi" in
           (ic , 7)

         (* Conditional whose result is not used *)
         let cond2 b =
           if b then Printf.eprintf "toto" else Printf.eprintf "toto";
           7

         (* A dummy argument is used to call the continuation in the
            [then] clause *)
         let cond3 b =
           let x= ref 0 in if b then x := 1 else Printf.eprintf "toto";
           !x

         (* Two continuation functions are created. One to bind [ic] before
            entering the loop, and one for the loop. We use a dummy argument
            to go back to the begining of the loop if [b] is false *)
         let loop1 b =
           let all = ref [] in
           let ic = open_in "/static/examples.ml" in
           while true do
             let line = input_line ic in
             all := line :: !all;
             if b then prerr_endline line
           done

         (* There is a single continuation for the loop since the result of
            [Printf.eprintf] is ignored. *)
         let loop2 () =
           let all = ref [] in
           let ic = open_in "/static/examples.ml" in
           Printf.eprintf "titi";
           while true do
             let line = input_line ic in
             all := line :: !all;
             prerr_endline line
           done

         let loop3 () =
           let l = list_rev [1;2;3] in
           let rec f x =
             match x with
             | [] -> l
             | _ :: r -> f r
           in
           f l
       |}
  in
  print_fun_decl code (Some "exceptions");
  print_fun_decl code (Some "cond1");
  print_fun_decl code (Some "cond2");
  print_fun_decl code (Some "cond3");
  print_fun_decl code (Some "loop1");
  print_fun_decl code (Some "loop2");
  print_fun_decl code (Some "loop3");
  [%expect
    {|

    function exceptions(s, cont){
     try{var _I_ = runtime.caml_int_of_string(s), n = _I_;}
     catch(_M_){
      var _B_ = caml_wrap_exception(_M_);
      if(_B_[1] !== Stdlib[7]){
       var raise$1 = caml_pop_trap();
       return raise$1(caml_maybe_attach_backtrace(_B_, 0));
      }
      var n = 0, _C_ = 0;
     }
     try{
      if(caml_string_equal(s, cst$0))
       throw caml_maybe_attach_backtrace(Stdlib[8], 1);
      var _H_ = 7, m = _H_;
     }
     catch(_L_){
      var _D_ = caml_wrap_exception(_L_);
      if(_D_ !== Stdlib[8]){
       var raise$0 = caml_pop_trap();
       return raise$0(caml_maybe_attach_backtrace(_D_, 0));
      }
      var m = 0, _E_ = 0;
     }
     runtime.caml_push_trap
      (function(_K_){
        if(_K_ === Stdlib[8]) return cont(0);
        var raise = caml_pop_trap();
        return raise(caml_maybe_attach_backtrace(_K_, 0));
       });
     if(caml_string_equal(s, cst)){
      var _F_ = Stdlib[8], raise = caml_pop_trap();
      return raise(caml_maybe_attach_backtrace(_F_, 1));
     }
     var _G_ = Stdlib[79];
     return caml_cps_call2
             (_G_,
              cst_toto,
              function(_J_){caml_pop_trap(); return cont([0, [0, _J_, n, m]]);});
    }
    //end
    function cond1(b, cont){
     function _A_(ic){return cont([0, ic, 7]);}
     return b
             ? caml_cps_call2(Stdlib[79], cst_toto$0, _A_)
             : caml_cps_call2(Stdlib[79], cst_titi, _A_);
    }
    //end
    function cond2(b, cont){
     function _y_(_z_){return cont(7);}
     return b
             ? caml_cps_call2(Stdlib_Printf[3], _h_, _y_)
             : caml_cps_call2(Stdlib_Printf[3], _i_, _y_);
    }
    //end
    function cond3(b, cont){
     var x = [0, 0];
     function _w_(_x_){return cont(x[1]);}
     return b ? (x[1] = 1, _w_(0)) : caml_cps_call2(Stdlib_Printf[3], _j_, _w_);
    }
    //end
    function loop1(b, cont){
     var _s_ = Stdlib[79];
     return caml_cps_call2
             (_s_,
              cst_static_examples_ml,
              function(ic){
               function _t_(_v_){
                var _u_ = Stdlib[83];
                return caml_cps_call2
                        (_u_,
                         ic,
                         function(line){
                          return b
                                  ? caml_cps_call2(Stdlib[53], line, _t_)
                                  : caml_cps_exact_call1(_t_, 0);
                         });
               }
               return _t_(0);
              });
    }
    //end
    function loop2(param, cont){
     var _n_ = Stdlib[79];
     return caml_cps_call2
             (_n_,
              cst_static_examples_ml$0,
              function(ic){
               var _o_ = Stdlib_Printf[3];
               function _p_(_r_){
                var _q_ = Stdlib[83];
                return caml_cps_call2
                        (_q_,
                         ic,
                         function(line){
                          return caml_cps_call2(Stdlib[53], line, _p_);
                         });
               }
               return caml_cps_call2(_o_, _k_, _p_);
              });
    }
    //end
    function loop3(param, cont){
     return caml_cps_call2
             (list_rev,
              _l_,
              function(l){
               function _m_(x){
                if(! x) return cont(l);
                var r = x[2];
                return caml_cps_exact_call1(_m_, r);
               }
               return _m_(l);
              });
    }
    //end |}]
