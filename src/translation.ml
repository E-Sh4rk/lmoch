open Aez
open Smt

open Asttypes
open Typed_ast
open Ident

let real_precision = 1000

module IntMap = Map.Make(struct type t = int let compare = compare end)

(*
let unique_nonce =
  let last = ref 0 in
  fun _ -> last := (!last)+1 ; (!last)

let unique_name name =
  Printf.sprintf "%s__%i" name (unique_nonce ())
*)

let declare_symbol name t_in t_out =
  (*let name = unique_name name in*)
  let x = Hstring.make name in
  Symbol.declare x t_in t_out;
  x

let base_type_to_smt_type t =
  match t with
  | Asttypes.Tbool -> Type.type_bool
  | Asttypes.Tint -> Type.type_int
  | Asttypes.Treal -> Type.type_real

let const_to_smt_term c =
  match c with
  | Asttypes.Cbool b -> if b then Term.t_true else Term.t_false
  | Asttypes.Cint i -> Term.make_int (Num.Int i)
  | Asttypes.Creal f ->
    let numerator = (Num.Int (truncate (f*.(float_of_int real_precision)))) in
    let denominator = Num.Int real_precision in
    Term.make_real (Num.div_num numerator denominator)

let declare_symbols_of_node (node:t_node) symbols =
  let add_local symbols ((ident:Ident.t), (t:base_ty)) =
    let name = Printf.sprintf "%s__%i" ident.name ident.id in
    let t_out = base_type_to_smt_type t in
    let symbol = declare_symbol name [ Type.type_int ] t_out in
    IntMap.add ident.id symbol symbols
  in
  let all_locals = node.tn_input @ node.tn_output @ node.tn_local in
  List.fold_left add_local symbols all_locals

type local_environment = t_node * (Hstring.t IntMap.t)
type environment = local_environment list

let term_of_int i =
  Term.make_int (Num.Int i)

let term_of_ident local_env n ident =
  Term.make_app (IntMap.find ident.id local_env) [n]

let terms_of_pattern local_env n pattern =
  List.map (term_of_ident local_env n) pattern.tpatt_desc

let rec terms_of_expr env local_env n expr =
  (* TODO *)
  match expr.texpr_desc with
  | TE_const c -> [const_to_smt_term c]
  | TE_ident ident -> [term_of_ident local_env n ident]
  | TE_arrow (expr1, expr2) ->
    let cond = Formula.make_lit Formula.Eq [n ; term_of_int 0] in
    let if_ts = terms_of_expr env local_env (term_of_int 0) expr1 in
    let else_ts = terms_of_expr env local_env n expr2 in
    List.map2 (Term.make_ite cond) if_ts else_ts
  | TE_pre expr ->
    let n_minus_one = Term.make_arith Term.Minus n (term_of_int 1) in
    terms_of_expr env local_env n_minus_one expr
  | TE_tuple exprs -> List.flatten (List.map (terms_of_expr env local_env n) exprs)
  | _ -> failwith "TMP"

let formulas_of_eq env local_env n (eq:t_equation) =
  let pat_terms = terms_of_pattern local_env n eq.teq_patt in
  let expr_terms = terms_of_expr env local_env n eq.teq_expr in
  List.map2 (fun pt et -> Formula.make_lit Formula.Eq [pt ; et]) pat_terms expr_terms
  
    