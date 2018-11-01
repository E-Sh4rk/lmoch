
open Translation

open Asttypes
open Typed_ast
open Ident

type check_result = True | False | Unknown | Error of string

let get_node_by_name ft name =
  List.find (fun (n:t_node) -> n.tn_name.name = name) ft

let check_k_induction ft main_node k =
  (*let delta n =
    formulas_of_node ft n main_node
  in
  let ok local_ctx n =
    let ok_var (id,t) =
      assert (t = Tbool);
      formula_of_term (term_of_ident local_ctx n id)
    in
    List.map ok_var main_node.tn_output
  in*)
  (* TODO (with system of local contexts reuse) *)
  false

let check ft main_node_name =
  try (
    let main_node = get_node_by_name ft main_node_name in
    (* TODO *)
    Unknown
  ) with _ -> Error "An unhandled exception has been raised."
