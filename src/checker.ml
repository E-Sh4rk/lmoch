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

let path_compressed_formula ns =
  let rec couples ns =
    match ns with
    | [] -> []
    | h::ns -> (List.map (fun n -> (h,n)) ns)@(couples ns)
  in
  let eqs = List.map (fun (n1,n2) -> states_equal_formula n1 n2) (couples ns) in
  let eqs = List.map (fun eq -> Formula.make Formula.Not [eq]) eqs in
  conjunction eqs

let check_k_induction ft main_node k =
  debug_str (Printf.sprintf "Checking %i-induction..." k);
  let local_ctx = ref (main_node, IntMap.empty, ref IntroducedSymbolMap.empty) in
  let delta n =
    let (lctx, fs) = formulas_of_main_node ft main_node false n in
    local_ctx := lctx ;
    conjunction fs
  in
  let ok n =
    let ok_var (id,t) =
      assert (t = Tbool);
      formula_of_term (term_of_ident (!local_ctx) n id)
    in
    conjunction (List.map ok_var main_node.tn_output)
  in

  (* Base case *)
  BMC_solver.clear () ;
  for i=0 to k do
    BMC_solver.assume ~id:(i+1) (delta (term_of_int i))
  done ;
  BMC_solver.check () ;
 
  let ok_fs = List.map (fun i -> ok (term_of_int i)) (create_list k) in
  let base = BMC_solver.entails ~id:(k+2) (conjunction ok_fs) in
  if not base then False
  else begin
   (* End condition based on path compression (http://homepage.cs.uiowa.edu/~tinelli/papers/HagTin-FMCAD-08.pdf) *)
    let ns = List.map (fun i -> term_of_int i) (create_list k) in
    let complete = BMC_solver.entails ~id:(k+2) (Formula.make Formula.Not [path_compressed_formula ns]) in
    if complete
    then begin
      debug_str "All compressed paths have been explored.";
      True
    end else begin
      (* Inductive case *)
      IND_solver.clear () ;
      IND_solver.assume ~id:1 n_ge_0 ;
      for i=0 to k+1 do
        IND_solver.assume ~id:(i+2) (delta (n_plus i))
      done ;
      for i=0 to k do
        IND_solver.assume ~id:(k+4+i) (ok (n_plus i))
      done ;
      let ns = List.map (fun i -> n_plus i) (create_list k) in
      IND_solver.assume ~id:(k+k+5) (path_compressed_formula ns) ;
      IND_solver.check () ;
      let inductive = IND_solver.entails ~id:(k+k+6) (ok (n_plus (k+1))) in
      
      if inductive then True
      else Unknown
    end
  end

let check ft main_node_name =
  Printexc.record_backtrace false ; (* Turn to true for debug *)
  try (
    let main_node = get_node_by_name ft main_node_name in
    let max_k = 10 in
    let rec aux k =
      if k > max_k then Unknown
      else match check_k_induction ft main_node k with
      | True -> True
      | False -> False
      | Unknown -> aux (k+1)
      | Error str -> Error str
    in
    aux 0
  ) with e ->
    let msg = Printexc.to_string e
    and stack = Printexc.get_backtrace () in
    Printf.eprintf "\nThere was an error: %s\n%s\n" msg stack;
    Error "An unhandled exception has been raised."
