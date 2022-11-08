(*
level of all variables
===> level 0 are not touched; free variable if less than function level


lift functions that are too deep and not in mutual recursion

traverse function to find free variables
return function + substitution


g = function (freevars) { function f (params) { body }}

function f (params) {body} -->
    apply g (freevars)

  let nv = Var.count () in
  let depth = Array.make nv 0 in
*)
