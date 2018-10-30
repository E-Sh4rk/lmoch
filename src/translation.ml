open Aez
open Smt

open Asttypes
open Typed_ast
open Ident

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

let term_of_pattern local_env pattern n =
  (* TODO *)
  Term.make_int (Num.Int 0)

let term_of_expr env local_env expr n =
  (* TODO *)
  Term.make_int (Num.Int 0)

let formula_of_eq env local_env (eq:t_equation) n =
  Formula.make_lit Formula.Eq
    [ term_of_pattern local_env eq.teq_patt n ; term_of_expr env local_env eq.teq_expr n ]
    