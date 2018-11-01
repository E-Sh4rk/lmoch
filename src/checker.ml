open Aez
open Smt

open Translation

open Asttypes
open Typed_ast
open Ident

module BMC_solver = Smt.Make(struct end)
module IND_solver = Smt.Make(struct end)

type check_result = True | False | Unknown | Error of string

let get_node_by_name ft name =
  List.find (fun (n:t_node) -> n.tn_name.name = name) ft

let create_list n =
  let rec aux acc n =
    if n < 0 then acc else aux (n::acc) (n-1)
  in
  aux [] n

let n = Term.make_app (declare_symbol "n" [] Type.type_int) []
let n_plus k = Term.make_arith Term.Plus n (term_of_int k)
let n_ge_0 = Formula.make_lit Formula.Le [term_of_int 0 ; n]

let debug_formula f =
  Formula.print Format.std_formatter f ;
  Format.print_flush () ; Printf.printf "\n"; flush_all ()

let debug_str str =
  Printf.printf "%s\n" str ; flush_all ()

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
  BMC_solver.clear () ;
  for i=0 to k do
    debug_formula (delta (term_of_int i)) ; (*TMP DEBUG*)
    BMC_solver.assume ~id:i (delta (term_of_int i))
  done ;
  BMC_solver.check () ;
  let ok_fs = List.map (fun i -> ok (term_of_int i)) (create_list k) in
  debug_formula (Formula.make Formula.And ok_fs) ; (*TMP DEBUG*)
  let base = BMC_solver.entails ~id:(k+1) (Formula.make Formula.And ok_fs) in
  debug_str "OK" ; (*TMP DEBUG*)

  (* Inductive case *)
  IND_solver.clear () ;
  IND_solver.assume ~id:0 n_ge_0 ;
  for i=0 to k+1 do
    IND_solver.assume ~id:(i+1) (delta (n_plus i))
  done ;
  for i=0 to k do
    IND_solver.assume ~id:(k+3+i) (ok (n_plus i))
  done ;
  IND_solver.check () ;
  debug_formula (ok (n_plus (k+1))) ; (*TMP DEBUG*)
  let inductive = IND_solver.entails ~id:(k+k+4) (ok (n_plus (k+1))) in
  debug_str "OK" ; (*TMP DEBUG*)
  
  (* Result *)
  if not base then False
  else if not inductive then Unknown
  else True

let check ft main_node_name =
  (*try ( *)
    let main_node = get_node_by_name ft main_node_name in
    let max_k = 3 in
    let rec aux k =
      if k > max_k then Unknown
      else match check_k_induction ft main_node k with
      | True -> True
      | False -> False
      | Unknown -> aux (k+1)
      | Error str -> Error str
    in
    aux 0
  (* )) with _ -> Error "An unhandled exception has been raised."*)
