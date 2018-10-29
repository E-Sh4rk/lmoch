
open Translation

open Asttypes
open Typed_ast
open Ident

type check_result = True | False | Unknown | Error of string

let get_node ft name =
  List.find (fun (n:t_node) -> n.tn_name.name = name) ft

let check ft main_node_name =
  try (
    let main_node = get_node ft main_node_name in
    (* TODO *)
    Unknown
  ) with _ -> Error "An unhandled exception has been raised."
