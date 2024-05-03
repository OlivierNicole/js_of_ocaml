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
  (** Left uninterpreted, since many operations can be performed efficiently directly
      on the encoded form. Instances of [t] produced by {!val:encode} are
      guaranteed to be valid JSON string literals (surrounding double quotes
      included). *)
  type t = private Uninterpreted of string [@@unboxed]

  val empty : t
  (** Represents the empty mapping. *)

  external uninterpreted : string -> t = "%identity"
  (** Create a value of type {!type:t} from a string, without attempting to
      decode it. *)

  val decode : t -> map list

  val encode : map list -> t

  val edit : strict:bool -> t -> Line_edits.t -> t
  (** Apply line edits in order. If the number of {!const:Line_edits.Keep} and
      {!const:Line_edits.Drop} actions does not match the number of lines in
      the domain of the input mapping, only the lines affected by an edit are
      included in the result. *)
end

module Sources_contents : sig
  (** Left uninterpreted by default as decoding this field can be costly if the
      amount of code is large, and is seldom required. Instances of [t]
      produced by {!val:encode} are guaranteed to be valid JSON string
      literals (surrounding double quotes included). *)
  type t = private Uninterpreted of string [@@unboxed]

  external uninterpreted : string -> t = "%identity"
  (** Create a value of type {!type:t} from a string, without attempting to
      decode it. *)

  val decode : t -> string option list

  val encode : string option list -> t
end

type t =
  { version : int
  ; file : string
  ; sourceroot : string option
  ; sources : string list
  ; sources_contents : Sources_contents.t option
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
    [file] and source root [sourceroot). Note that at the moment, this function
    can be slow when the [sources_contents] field contains very large
    codebases, as it decodes the whole source text. This may be fixed in the
    future. *)

module Composite : sig
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
