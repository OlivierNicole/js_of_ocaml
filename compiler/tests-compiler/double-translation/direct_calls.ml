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

open Util

let%expect_test "direct calls with --enable effects,doubletranslate" =
  let code =
    compile_and_parse
      ~effects:true
      ~doubletranslate:true
      {|
         (* Arity of the argument of a function / direct call *)
         let test1 () =
           let f g x = try g x with e -> raise e in
           ignore (f (fun x -> x + 1) 7);
           ignore (f (fun x -> x *. 2.) 4.)

         (* Arity of the argument of a function / CPS call *)
         let test2 () =
           let f g x = try g x with e -> raise e in
           ignore (f (fun x -> x + 1) 7);
           ignore (f (fun x -> x ^ "a") "a")

         (* Arity of functions in a functor / direct call *)
         let test3 x =
           let module F(_ : sig end) = struct let f x = x + 1 end in
           let module M1 = F (struct end) in
           let module M2 = F (struct end) in
           (M1.f 1, M2.f 2)

         (* Arity of functions in a functor / CPS call *)
         let test4 x =
           let module F(_ : sig end) =
             struct let f x = Printf.printf "%d" x end in
           let module M1 = F (struct end) in
           let module M2 = F (struct end) in
           M1.f 1; M2.f 2
|}
  in
  print_program code;
  [%expect
    {|
    (function(globalThis){
       "use strict";
       var
        runtime = globalThis.jsoo_runtime,
        caml_cps_closure = runtime.caml_cps_closure,
        caml_maybe_attach_backtrace = runtime.caml_maybe_attach_backtrace,
        caml_pop_trap = runtime.caml_pop_trap,
        caml_string_of_jsbytes = runtime.caml_string_of_jsbytes,
        caml_wrap_exception = runtime.caml_wrap_exception;
       function caml_call1(f, a0){
        return (f.l >= 0 ? f.l : f.l = f.length) === 1
                ? f(a0)
                : runtime.caml_call_gen(f, [a0]);
       }
       function caml_call2(f, a0, a1){
        return (f.l >= 0 ? f.l : f.l = f.length) === 2
                ? f(a0, a1)
                : runtime.caml_call_gen(f, [a0, a1]);
       }
       function caml_exact_trampoline_cps_call(f, a0, a1){
        return runtime.caml_stack_check_depth()
                ? f.cps.call(null, a0, a1)
                : runtime.caml_trampoline_return(f, [a0, a1]);
       }
       function caml_trampoline_cps_call3(f, a0, a1, a2){
        return runtime.caml_stack_check_depth()
                ? (f.cps.l
                    >= 0
                    ? f.cps.l
                    : f.cps.l = f.cps.length)
                  === 3
                  ? f.cps.call(null, a0, a1, a2)
                  : runtime.caml_call_gen_cps(f, [a0, a1, a2])
                : runtime.caml_trampoline_return(f, [a0, a1, a2]);
       }
       function caml_exact_trampoline_cps_call$0(f, a0, a1, a2){
        return runtime.caml_stack_check_depth()
                ? f.cps.call(null, a0, a1, a2)
                : runtime.caml_trampoline_return(f, [a0, a1, a2]);
       }
       runtime.caml_initialize_fiber_stack();
       var
        dummy = 0,
        global_data = runtime.caml_get_global_data(),
        _s_ = [0, [4, 0, 0, 0, 0], caml_string_of_jsbytes("%d")],
        cst_a$0 = caml_string_of_jsbytes("a"),
        cst_a = caml_string_of_jsbytes("a"),
        Stdlib_Printf = global_data.Stdlib__Printf,
        Stdlib = global_data.Stdlib;
       function test1$0(param){
        function f(g, x){
         try{caml_call1(g, dummy); return;}
         catch(e$0){
          var e = caml_wrap_exception(e$0);
          throw caml_maybe_attach_backtrace(e, 0);
         }
        }
        f(function(x){});
        f(function(x){});
        return 0;
       }
       function test1$1(param, cont){
        function f(g, x){
         try{caml_call1(g, dummy); return;}
         catch(e$0){
          var e = caml_wrap_exception(e$0);
          throw caml_maybe_attach_backtrace(e, 0);
         }
        }
        f(function(x){});
        f(function(x){});
        return cont(0);
       }
       var test1 = caml_cps_closure(test1$0, test1$1);
       function f$0(){
        function f$0(g, x){
         try{caml_call1(g, x); return;}
         catch(e$0){
          var e = caml_wrap_exception(e$0);
          throw caml_maybe_attach_backtrace(e, 0);
         }
        }
        function f$1(g, x, cont){
         runtime.caml_push_trap
          (function(e){
            var raise = caml_pop_trap(), e$0 = caml_maybe_attach_backtrace(e, 0);
            return raise(e$0);
           });
         return caml_exact_trampoline_cps_call
                 (g, x, function(_y_){caml_pop_trap(); return cont();});
        }
        var f = caml_cps_closure(f$0, f$1);
        return f;
       }
       function _h_(){
        return caml_cps_closure(function(x){}, function(x, cont){return cont();});
       }
       function _j_(){
        return caml_cps_closure
                (function(x){return caml_call2(Stdlib[28], x, cst_a$0);},
                 function(x, cont){
                  return caml_trampoline_cps_call3(Stdlib[28], x, cst_a$0, cont);
                 });
       }
       function test2$0(param){
        var f = f$0();
        f(_h_(), 7);
        f(_j_(), cst_a);
        return 0;
       }
       function test2$1(param, cont){
        var f = f$0();
        return caml_exact_trampoline_cps_call$0
                (f,
                 _h_(),
                 7,
                 function(_w_){
                  return caml_exact_trampoline_cps_call$0
                          (f, _j_(), cst_a, function(_x_){return cont(0);});
                 });
       }
       var test2 = caml_cps_closure(test2$0, test2$1);
       function test3$0(x){
        function F(symbol){function f(x){return x + 1 | 0;} return [0, f];}
        var M1 = F(), M2 = F(), _v_ = caml_call1(M2[1], 2);
        return [0, caml_call1(M1[1], 1), _v_];
       }
       function test3$1(x, cont){
        function F(symbol){function f(x){return x + 1 | 0;} return [0, f];}
        var M1 = F(), M2 = F(), _u_ = M2[1].call(null, 2);
        return cont([0, M1[1].call(null, 1), _u_]);
       }
       var test3 = caml_cps_closure(test3$0, test3$1);
       function f(){
        function f$0(x){return caml_call2(Stdlib_Printf[2], _s_, x);}
        function f$1(x, cont){
         return caml_trampoline_cps_call3(Stdlib_Printf[2], _s_, x, cont);
        }
        var f = caml_cps_closure(f$0, f$1);
        return f;
       }
       function test4$0(x){
        function F(symbol){var f$0 = f(); return [0, f$0];}
        var M1 = F(), M2 = F();
        caml_call1(M1[1], 1);
        return caml_call1(M2[1], 2);
       }
       function test4$1(x, cont){
        function F(symbol){var f$0 = f(); return [0, f$0];}
        var M1 = F(), M2 = F();
        return caml_exact_trampoline_cps_call
                (M1[1],
                 1,
                 function(_t_){
                  return caml_exact_trampoline_cps_call(M2[1], 2, cont);
                 });
       }
       var
        test4 = caml_cps_closure(test4$0, test4$1),
        Test = [0, test1, test2, test3, test4];
       runtime.caml_register_global(7, Test, "Test");
       return;
      }
      (globalThis));
    //end
    |}]