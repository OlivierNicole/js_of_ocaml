(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2017 Hugo Heuzard
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

open Source_map

let rewrite_path path =
  if Filename.is_relative path
  then path
  else
    match Build_path_prefix_map.get_build_path_prefix_map () with
    | Some map -> Build_path_prefix_map.rewrite map path
    | None -> path

(* Escapes special characters and wrap in double quotes *)
let stringlit_of_string s = `Stringlit (Yojson.Basic.to_string (`String s))

let json t =
  let (Source_map.Mappings.Uninterpreted mappings) = t.mappings in
  let fields =
    [ "version", `Intlit (Int.to_string t.version)
    ; "file", stringlit_of_string (rewrite_path t.file)
    ; ( "sourceRoot"
      , stringlit_of_string
          (match t.sourceroot with
          | None -> ""
          | Some s -> rewrite_path s) )
    ; "names", `List (List.map (fun s -> stringlit_of_string s) t.names)
    ; ( "sources"
      , `List (List.map (fun s -> stringlit_of_string (rewrite_path s)) t.sources) )
    ; "mappings", `Stringlit ("\"" ^ mappings ^ "\"") (* Nothing to escape *)
    ]
  in
  match t.sources_contents with
  | None -> `Assoc fields
  | Some (Source_map.Sources_contents.Uninterpreted cs) ->
      `Assoc
        (fields
        @ [ ( "sourcesContent"
              (* It is the job of {!mod:Sources_contents} to enforce that [cs] is
                 already a valid JSON string literal *)
            , `Stringlit cs )
          ])

let invalid () = invalid_arg "Source_map.of_json"

let string_of_stringlit (`Stringlit s) =
  match Yojson.Basic.from_string s with
  | `String s -> s
  | _ -> invalid_arg "Source_map_io.string_of_stringlit: not a JSON string literal"

let string name rest =
  match List.assoc name rest with
  | `Stringlit _ as s -> Some (string_of_stringlit s)
  | `Null -> None
  | _ -> invalid ()
  | exception Not_found -> None

let list_string name rest =
  try
    match List.assoc name rest with
    | `List l ->
        Some
          (List.map
             (function
               | `Stringlit _ as lit -> string_of_stringlit lit
               | _ -> invalid ())
             l)
    | _ -> invalid ()
  with Not_found -> None

let stringlit_opt name assoc =
  match List.assoc name assoc with
  | `Stringlit s -> Some s
  | _ | (exception Not_found) -> None

let of_json json =
  match json with
  | `Assoc (("version", version) :: rest) ->
      (match version with
      | `Floatlit version when Float.equal (Float.of_string version) 3.0 -> ()
      | `Intlit version when Int.equal (int_of_string version) 3 -> ()
      | `Floatlit _ | `Intlit _ -> invalid_arg "Source_map_io.of_json: version != 3"
      | _ -> invalid_arg "Source_map_io.of_json: version field is not a number");
      let file = string "file" rest in
      let sourceroot = string "sourceRoot" rest in
      let names = list_string "names" rest in
      let sources = list_string "sources" rest in
      let sources_contents = stringlit_opt "sourcesContent" rest in
      let mappings = stringlit_opt "mappings" rest in
      let mappings =
        Option.map
          (fun mappings ->
            assert (
              String.length mappings > 2
              && Char.equal mappings.[0] '"'
              && Char.equal mappings.[String.length mappings - 1] '"');
            let mappings = String.sub mappings 1 (String.length mappings - 2) in
            Mappings.uninterpreted mappings)
          mappings
      in
      { version = 3
      ; file = Option.value file ~default:""
      ; sourceroot
      ; names = Option.value names ~default:[]
      ; sources_contents = Option.map Sources_contents.uninterpreted sources_contents
      ; sources = Option.value sources ~default:[]
      ; mappings = Option.value mappings ~default:Mappings.empty
      }
  | _ -> invalid ()

let of_string s = of_json (Yojson.Raw.from_string s)

let to_string m = Yojson.Raw.to_string (json m)

let to_file m file = Yojson.Raw.to_file file (json m)

let enabled = true

module Composite = struct
  let json t =
    `Assoc
      [ "version", `Intlit (Int.to_string t.Composite.version)
      ; "file", stringlit_of_string (rewrite_path t.file)
      ; ( "sections"
        , `List
            (List.map
               (fun ({ Composite.gen_line; gen_column }, `Map sm) ->
                 `Assoc
                   [ ( "offset"
                     , `Assoc
                         [ "line", `Intlit (Int.to_string gen_line)
                         ; "column", `Intlit (Int.to_string gen_column)
                         ] )
                   ; "map", json sm
                   ])
               t.sections) )
      ]

  let to_string m = Yojson.Raw.to_string (json m)

  let to_file m file = Yojson.Raw.to_file file (json m)
end
