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
  var n = (f.l >= 0)?f.l:(f.l = f.length);
  var argsLen = args.length;
  var d = n - argsLen;
  if (d == 0)
    return f.apply(null, args);
  else if (d < 0) {
    var g = f.apply(null,args.slice(0,n));
    if(typeof g !== "function") return g;
    return caml_call_gen(g,args.slice(n));
  }
  else {
    switch (d) {
    case 1: {
      var g = function (x){
        var nargs = new Array(argsLen + 1);
        for(var i = 0; i < argsLen; i++ ) nargs[i] = args[i];
        nargs[argsLen] = x;
        return f.apply(null, nargs)
      };
      break;
    }
    case 2: {
      var g = function (x, y){
        var nargs = new Array(argsLen + 2);
        for(var i = 0; i < argsLen; i++ ) nargs[i] = args[i];
        nargs[argsLen] = x;
        nargs[argsLen + 1] = y;
        return f.apply(null, nargs)
      };
      break;
    }
    default: {
      var g = function (){
        var extra_args = (arguments.length == 0)?1:arguments.length;
        var nargs = new Array(args.length+extra_args);
        for(var i = 0; i < args.length; i++ ) nargs[i] = args[i];
        for(var i = 0; i < arguments.length; i++ ) nargs[args.length+i] = arguments[i];
        return caml_call_gen(f, nargs)
      };
    }}
    g.l = d;
    return g;
  }
}

//Provides: caml_call_gen_tuple (const, shallow)
//Requires: caml_fiber_stack, caml_cps_closure
//If: effects
//Weakdef
var caml_call_gen_tuple = (
  function() {
    function caml_call_gen_direct(f, args) {
      var n = (f.l >= 0)?f.l:(f.l = f.length);
      var argsLen = args.length;
      var d = n - argsLen;
      if (d == 0) {
        return f.apply(null, args);
      } else if (d < 0) {
        return caml_call_gen_direct(f.apply(null, args.slice(0,n)), args.slice(n));
      } else {
        // FIXME: Restore the optimization of handling specially d = 1 or 2
        var ret = caml_cps_closure(
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
        );
        ret.l = d;
        ret.cps.l = d + 1;
        return ret;
      }
    }
    function caml_call_gen_cps(f, args) {
      var n = (f.cps.l >= 0)?f.cps.l:(f.cps.l = f.cps.length);
      if (n === 0) return f.cps.apply(null, args);
      var argsLen = args.length;
      var d = n - argsLen;
      if (d == 0) {
        return f.cps.apply(null, args);
      }
      else if (d < 0) {
        var rest = args.slice(n - 1);
        var k = args[argsLen - 1];
        args = args.slice(0, n);
        args[n - 1] = function(g) {
          var args = rest.slice();
          args[args.length - 1] = k;
          return caml_call_gen_cps(g, args);
        };
        return f.cps.apply(null, args);
      } else {
        argsLen--;
        var k = args[argsLen];
        var cont =
          caml_cps_closure(
            function (){
              var extra_args = (arguments.length == 0)?1:arguments.length;
              var nargs = new Array(argsLen+extra_args);
              for(var i = 0; i < argsLen; i++ ) nargs[i] = args[i];
              for(var i = 0; i < arguments.length; i++ ) nargs[argsLen+i] = arguments[i];
              return caml_call_gen_direct(f, nargs)
            },
            function () {
              var extra_args = (arguments.length == 0)?1:arguments.length;
              var nargs = new Array(argsLen + extra_args);
              for(var i = 0; i < argsLen; i++ ) nargs[i] = args[i];
              for(var i = 0; i < arguments.length; i++ ) nargs[argsLen+i] = arguments[i];
              return caml_call_gen_cps(f, nargs)
            } );
        cont.l = d;
        cont.cps.l = d + 1;
        return k(cont);
      }
    }
    return [caml_call_gen_direct, caml_call_gen_cps]
  }
)()


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

//Provides: caml_register_named_value (const,mutable)
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

//Provides: caml_build_symbols
//Requires: caml_jsstring_of_string
function caml_build_symbols(toc) {
  var symb;
  while(toc) {
    if(caml_jsstring_of_string(toc[1][1]) == "SYJS") {
      symb = toc[1][2];
      break;
    }
    else toc = toc[2]
  }
  var r = {};
  if(symb) {
    for(var i = 1; i < symb.length; i++){
      r[caml_jsstring_of_string(symb[i][1])] = symb[i][2]
    }
  }
  return r;
}

//Provides: caml_register_global (const, shallow, const)
//Requires: caml_global_data, caml_callback, caml_build_symbols
//Requires: caml_failwith
function caml_register_global (n, v, name_opt) {
  if (name_opt) {
    var name = name_opt;
    if(globalThis.toplevelReloc) {
      n = caml_callback(globalThis.toplevelReloc, [name]);
    }
    else if (caml_global_data.toc) {
      if(!caml_global_data.symbols) {
        caml_global_data.symbols = caml_build_symbols(caml_global_data.toc)
      }
      var nid = caml_global_data.symbols[name]
      if(nid >= 0)
        n = nid
      else {
        caml_failwith("caml_register_global: cannot locate " + name);
      }
    }
  }
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
