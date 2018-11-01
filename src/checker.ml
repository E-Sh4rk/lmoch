
open Aez
open Smt

open Translation

open Asttypes
open Typed_ast
open Ident

module BMC_solver = Smt.Make(struct end)

type check_result = True | False | Unknown | Error of string

let get_node_by_name ft name =
  List.find (fun (n:t_node) -> n.tn_name.name = name) ft

let create_list n =
  let rec aux acc n =
    if n < 0 then acc else aux (n::acc) (n-1)
  in
  aux [] (n-1)

let check_k_induction ft main_node k =
  let local_ctx = ref (main_node, IntMap.empty) in
  let delta n =
    let (lctx, fs) = formulas_of_main_node ft main_node false n in
    local_ctx := lctx ;
    Formula.make Formula.And fs
  in
  let ok n =
    let ok_var (id,t) =
      assert (t = Tbool);
      formula_of_term (term_of_ident (!local_ctx) n id)
    in
    Formula.make Formula.And (List.map ok_var main_node.tn_output)
  in

  (* Base case *)
  for i=0 to k-1 do
    BMC_solver.assume ~id:k (delta (term_of_int i))
  done ;
  let ok_fs = List.map (fun i -> ok (term_of_int i)) (create_list k) in
  let base = BMC_solver.entails ~id:k (Formula.make Formula.And ok_fs) in

  (* Inductive case *)
  let inductive = false in
  (* TODO *)
  
  base && inductive

let check ft main_node_name =
  try (
    let main_node = get_node_by_name ft main_node_name in
    (* TODO *)
    Unknown
  ) with _ -> Error "An unhandled exception has been raised."
