open Aez
open Smt

open Asttypes
open Typed_ast
open Ident

let real_denominator = 1000

module IntMap = Map.Make(struct type t = int let compare = compare end)

let unique_nonce =
  let last = ref 0 in
  fun _ -> last := (!last)+1 ; (!last)

let unique_name name =
  Printf.sprintf "%s__%i" name (unique_nonce ())

let declare_symbol name t_in t_out =
  let name = unique_name name in
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
    let numerator = (Num.Int (truncate (f*.(float_of_int real_denominator)))) in
    let denominator = Num.Int real_denominator in
    Term.make_real (Num.div_num numerator denominator)

let declare_symbols_of_node (node:t_node) symbols =
  let add_local symbols ((ident:Ident.t), (t:base_ty)) =
    if IntMap.mem ident.id symbols then symbols
    else
      let name = Printf.sprintf "%s__%i" ident.name ident.id in
      let t_out = base_type_to_smt_type t in
      let symbol = declare_symbol name [ Type.type_int ] t_out in
      IntMap.add ident.id symbol symbols
  in
  let all_locals = node.tn_input @ node.tn_output @ node.tn_local in
  List.fold_left add_local symbols all_locals

type local_context = t_node * (Hstring.t IntMap.t)
type context = t_node list

let formula_of_term t =
  Formula.make_lit Formula.Eq [t ; Term.t_true]

let term_of_formula f =
  Term.make_ite f Term.t_true Term.t_false

let term_of_int i =
  Term.make_int (Num.Int i)

let term_of_ident local_ctx n ident =
  let (_, ctx_symbols) = local_ctx in
  Term.make_app (IntMap.find ident.id ctx_symbols) [n]

let terms_of_pattern local_ctx n pattern =
  List.map (term_of_ident local_ctx n) pattern.tpatt_desc

(* Returns a tuple (eqs,terms) where eqs are some additional required equations *)
let rec terms_of_operator ctx local_ctx n op exprs =
  let (eqs, ts) = List.split (List.map (terms_of_expr ctx local_ctx n) exprs) in
  let eqs = List.flatten eqs in
  let unique_term ts =
    (* Operators are not defined on tuples (at least for now) *)
    assert (List.length ts = 1) ;
    List.hd ts
  in
  let ts = List.map unique_term ts in
  let res =
    match op with
    | Op_not ->
      assert (List.length ts = 1) ;
      let t = List.hd ts in
      [term_of_formula (Formula.make Formula.Not [formula_of_term t])]
    | Op_if ->
      assert (List.length ts = 3) ;
      let tcond = List.hd ts in
      let tif = List.hd (List.tl ts) in
      let telse = List.hd (List.tl (List.tl ts)) in
      [Term.make_ite (formula_of_term tcond) tif telse]
    | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge
    | Op_add | Op_sub | Op_mul | Op_div | Op_mod
    | Op_add_f | Op_sub_f | Op_mul_f | Op_div_f
    | Op_and | Op_or | Op_impl ->
      assert (List.length ts = 2) ;
      let t1 = List.hd ts in
      let t2 = List.hd (List.tl ts) in
      begin match op with
        | Op_eq -> [term_of_formula (Formula.make_lit Formula.Eq [t1 ; t2])]
        | Op_neq -> [term_of_formula (Formula.make_lit Formula.Neq [t1 ; t2])]
        | Op_lt -> [term_of_formula (Formula.make_lit Formula.Lt [t1 ; t2])]
        | Op_le -> [term_of_formula (Formula.make_lit Formula.Le [t1 ; t2])]
        | Op_gt -> [term_of_formula (Formula.make Formula.Not [Formula.make_lit Formula.Le [t1 ; t2]])]
        | Op_ge -> [term_of_formula (Formula.make Formula.Not [Formula.make_lit Formula.Lt [t1 ; t2]])]
        | Op_add | Op_add_f -> [Term.make_arith Term.Plus t1 t2]
        | Op_sub | Op_sub_f -> [Term.make_arith Term.Minus t1 t2]
        | Op_mul | Op_mul_f -> [Term.make_arith Term.Mult t1 t2]
        | Op_div | Op_div_f -> [Term.make_arith Term.Div t1 t2]
        | Op_mod -> [Term.make_arith Term.Modulo t1 t2]
        | Op_and -> [term_of_formula (Formula.make Formula.And [formula_of_term t1 ; formula_of_term t2])]
        | Op_or -> [term_of_formula (Formula.make Formula.Or [formula_of_term t1 ; formula_of_term t2])]
        | Op_impl -> [term_of_formula (Formula.make Formula.Imp [formula_of_term t1 ; formula_of_term t2])]
        | _ -> assert false
      end
  in
  (eqs, res)

(* Returns a tuple (eqs,terms) where eqs are some additional required equations *)
and terms_of_expr ctx local_ctx n expr =
  match expr.texpr_desc with
  | TE_const c -> ([],[const_to_smt_term c])
  | TE_ident ident -> ([],[term_of_ident local_ctx n ident])
  | TE_op (op, exprs) -> terms_of_operator ctx local_ctx n op exprs
  | TE_app (id, exprs) ->
    (* TODO *)
    failwith "todo"
  | TE_prim _ ->
    (*
    -- typing.ml --
    let prims = [
    "int_of_real", (int_of_real, ([Treal] , [Tint])) ;
    "real_of_int", (real_of_int, ([Tint] , [Treal])) ; ]
    *)
    (* TODO *)
    failwith "Prime applications are not supported yet."
  | TE_arrow (expr1, expr2) ->
    let cond = Formula.make_lit Formula.Eq [n ; term_of_int 0] in
    let (if_eqs,if_ts) = terms_of_expr ctx local_ctx (term_of_int 0) expr1 in
    let (else_eqs,else_ts) = terms_of_expr ctx local_ctx n expr2 in
    (if_eqs@else_eqs, List.map2 (Term.make_ite cond) if_ts else_ts)
  | TE_pre expr ->
    let n_minus_one = Term.make_arith Term.Minus n (term_of_int 1) in
    terms_of_expr ctx local_ctx n_minus_one expr
  | TE_tuple exprs ->
    let (eqs, ts) = List.split (List.map (terms_of_expr ctx local_ctx n) exprs) in
    (List.flatten eqs, List.flatten ts)

and formulas_of_eq ctx local_ctx n (eq:t_equation) =
  let pat_terms = terms_of_pattern local_ctx n eq.teq_patt in
  let (eqs,expr_terms) = terms_of_expr ctx local_ctx n eq.teq_expr in
  let new_eqs = List.map2 (fun pt et -> Formula.make_lit Formula.Eq [pt ; et]) pat_terms expr_terms in
  eqs@new_eqs

and formulas_of_node ctx n id =
  (* TODO *)
  failwith "todo"
    