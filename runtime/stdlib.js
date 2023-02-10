// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: caml_call_gen (const, shallow)
//If: !effects
//Weakdef
function caml_call_gen(f, args) {
  if(f.fun)
    return caml_call_gen(f.fun, args);
  //FIXME, can happen with too many arguments
  if(typeof f !== "function") return f;
  var n = f.length | 0;
  if(n === 0) return f.apply(null,args);
  var argsLen = args.length | 0;
  var d = n - argsLen | 0;
  if (d == 0)
    return f.apply(null, args);
  else if (d < 0) {
    return caml_call_gen(f.apply(null,args.slice(0,n)),args.slice(n));
  }
  else {
    return function (){
      var extra_args = (arguments.length == 0)?1:arguments.length;
      var nargs = new Array(args.length+extra_args);
      for(var i = 0; i < args.length; i++ ) nargs[i] = args[i];
      for(var i = 0; i < arguments.length; i++ ) nargs[args.length+i] = arguments[i];
      return caml_call_gen(f, nargs)
    }
  }
}

//Provides: caml_call_gen_tuple (const, shallow)
//Requires: caml_fiber_stack
//If: effects
//Weakdef
var caml_call_gen_tuple = (
  function() {
    function caml_call_gen_direct(f, args) {
      if(f.fun)
        return caml_call_gen_direct(f.fun, args);
      var fdir = f[1];
      //FIXME, can happen with too many arguments
      if(typeof fdir !== "function") return fdir;
      var n = fdir.length | 0;
      if(n === 0) return fdir.apply(null,args);
      var argsLen = args.length | 0;
      var d = n - argsLen | 0;
      if (d == 0)
        return fdir.apply(null, args);
      else if (d < 0) {
        return caml_call_gen_direct(fdir.apply(null,args.slice(0,n)),args.slice(n));
      }
      else {
        return [
          0,
          function (){
            var extra_args = (arguments.length == 0)?1:arguments.length;
            var nargs = new Array(args.length+extra_args);
            for(var i = 0; i < args.length; i++ ) nargs[i] = args[i];
            for(var i = 0; i < arguments.length; i++ ) nargs[args.length+i] = arguments[i];
            return caml_call_gen_direct(f, nargs)
          },
          function () {
            var extra_args = (arguments.length == 0)?1:arguments.length;
            var nargs = new Array(argsLen + extra_args);
            for(var i = 0; i < argsLen; i++ ) nargs[i] = args[i];
            for(var i = 0; i < arguments.length; i++ ) nargs[argsLen+i] = arguments[i];
            var cont = nargs[argsLen + extra_args - 1];
            return caml_call_gen_cps(f, nargs);
          }
        ];
      }
    }
    function caml_call_gen_cps(f, args) {
      if (f.fun)
        return caml_call_gen_cps(f.fun, args);
      var fcps = f[2];
      if (typeof fcps !== "function") return args[args.length-1](f);
      var n = fcps.length | 0;
      if (n === 0) return fcps.apply(null, args);
      var argsLen = args.length | 0;
      var d = n - argsLen | 0;
      if (d == 0) {
        return fcps.apply(null, args);
      } else if (d < 0) {
        var rest = args.slice(n - 1);
        var k = args [argsLen - 1];
        args = args.slice(0, n);
        args[n - 1] = function (g) {
          var args = rest.slice();
          args[args.length - 1] = k;
          return caml_call_gen_cps(g, args); };
        return fcps.apply(null, args);
      } else {
        argsLen--;
        var k = args [argsLen];
        return k (
          [ 0,
            function (){
              var extra_args = (arguments.length == 0)?1:arguments.length;
              var nargs = new Array(args.length+extra_args);
              for(var i = 0; i < args.length; i++ ) nargs[i] = args[i];
              for(var i = 0; i < arguments.length; i++ ) nargs[args.length+i] = arguments[i];
              return caml_call_gen_direct(f, nargs)
            },
            function () {
              var extra_args = (arguments.length == 0)?1:arguments.length;
              var nargs = new Array(argsLen + extra_args);
              for(var i = 0; i < argsLen; i++ ) nargs[i] = args[i];
              for(var i = 0; i < arguments.length; i++ ) nargs[argsLen+i] = arguments[i];
              return caml_call_gen_cps(f, nargs)
            } ]);
      }
    }
    return [caml_call_gen_direct, caml_call_gen_cps]
  })()

//Provides: caml_call_gen
//Requires: caml_call_gen_tuple
//If: effects
var caml_call_gen = caml_call_gen_tuple[0];

//Provides: caml_call_gen_cps
//Requires: caml_call_gen_tuple
//If: effects
var caml_call_gen_cps = caml_call_gen_tuple[1];


//Provides: caml_named_values
var caml_named_values = {};

//Provides: caml_register_named_value (const,const)
//Requires: caml_named_values, caml_jsbytes_of_string
function caml_register_named_value(nm,v) {
  caml_named_values[caml_jsbytes_of_string(nm)] = v;
  return 0;
}

//Provides: caml_named_value
//Requires: caml_named_values
function caml_named_value(nm) {
  return caml_named_values[nm]
}

//Provides: caml_global_data
var caml_global_data = [0];

//Provides: caml_register_global (const, shallow, const)
//Requires: caml_global_data, caml_callback
function caml_register_global (n, v, name_opt) {
  if(name_opt && globalThis.toplevelReloc)
    n = caml_callback(globalThis.toplevelReloc, [name_opt]);
  caml_global_data[n + 1] = v;
  if(name_opt) caml_global_data[name_opt] = v;
}

//Provides: caml_get_global_data mutable
//Requires: caml_global_data
function caml_get_global_data () { return caml_global_data; }

//Provides: caml_is_printable const (const)
function caml_is_printable(c) { return +(c > 31 && c < 127); }

//Provides: caml_maybe_print_stats
function caml_maybe_print_stats(unit) { return 0 }
