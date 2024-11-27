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

val closure :
     Code.program
  -> bound_vars:Code.Var.Set.t
  -> f:Code.Var.t
  -> params:Code.Var.t list
  -> cont:int * Code.Var.t list
  -> Code.program * Code.Var.t * Code.Var.t list * (int * Code.Var.t list)
(** Given a program and a closure [f] -- defined by its name, parameters, and its
    continuation --, return a program in which the body of [f] has been updated with fresh
    variable names to replace elements of [bound_vars]. Also returns the new name of [f]
    (fresh if [f] is in [bound_vars]), and the similarly substituted parameter list and
    continuation.
  *)
