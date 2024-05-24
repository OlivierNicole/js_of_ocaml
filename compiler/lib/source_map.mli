(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2013 Hugo Heuzard
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

type map =
  | Gen of
      { gen_line : int
      ; gen_col : int
      }
  | Gen_Ori of
      { gen_line : int
      ; gen_col : int
      ; ori_source : int
      ; ori_line : int
      ; ori_col : int
      }
  | Gen_Ori_Name of
      { gen_line : int
      ; gen_col : int
      ; ori_source : int
      ; ori_line : int
      ; ori_col : int
      ; ori_name : int
      }

module Line_edits : sig
  type action =
    | Keep
    | Drop
    | Add of { count : int }

  val pp_action : Format.formatter -> action -> unit

  type t = action list

  val pp : Format.formatter -> t -> unit
end

module Mappings : sig
  type t

  val empty : t
  (** Represents the empty mapping. *)

  val of_string : string -> t
  (** By default, mappings are left uninterpreted, since many operations can be
      performed efficiently directly on the encoded form. It is guaranteed that
      {!val:of_string} and {!val:to_string} are inverse functions. *)

  val decode : t -> map list

  val encode : map list -> t

  val to_string : t -> string
  (** Returns the mappings as a string in the Source map v3 format. *)

  val edit : strict:bool -> t -> Line_edits.t -> t
  (** Apply line edits in order. If the number of {!const:Line_edits.Keep} and
      {!const:Line_edits.Drop} actions does not match the number of lines in
      the domain of the input mapping, only the lines affected by an edit are
      included in the result. *)
end

module Source_text : sig
  type t

  val of_json_string : string -> t
  (** By default, sources contents are left uninterpreted as decoding this field can be
      costly if the amount of code is large, and is seldom required. It is guaranteed that
      {!val:of_json_string} and {!val:to_json_string} are inverse functions.  *)

  val decode : t -> string option

  val encode : string option -> t

  val to_json_string : t -> string
  (** Returns a valid JSON object (in this instance, a string literal, double quotes
      included) representing the source text. *)
end

type t =
  { version : int
  ; file : string
  ; sourceroot : string option
  ; sources : string list
  ; sources_contents : Source_text.t list option
        (** Left uninterpreted by default, since decoding it requires to handle special
          characters, which can be costly for huge codebases. *)
  ; names : string list
  ; mappings : Mappings.t
        (** Left uninterpreted, since most useful operations can be performed efficiently
          directly on the encoded form, and a full decoding can be costly for big
          sourcemaps. *)
  }

val empty : filename:string -> t

val concat : file:string -> sourceroot:string option -> t -> t -> t
(** If [s1] encodes a mapping for a generated file [f1], and [s2] for a
    generated file [f2], then [concat ~file ~sourceroot s1 s2] encodes the
    union of these mappings for the concatenation of [f1] and [f2], with name
    [file] and source root [sourceroot). *)

module Index : sig
  type offset =
    { gen_line : int
    ; gen_column : int
    }

  type nonrec t =
    { version : int
    ; file : string
    ; sections : (offset * [ `Map of t ]) list
          (** List of [(offset, map)] pairs. The sourcemap spec allows for [map] to be
            either a sourcemap object or a URL, but we don't need to generate
            composite sourcemaps with URLs for now, and it is therefore not
            implemented. *)
    }
end
