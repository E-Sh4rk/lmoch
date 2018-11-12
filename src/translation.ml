open Aez
open Smt

open Asttypes
open Typed_ast
open Ident

let max_denominator = Num.power_num (Num.Int 2) (Num.Int 64)
let num_frac_base = (Num.Int 2)

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

let float_to_num f =
  let rec update_frac_until_exact f num den =
    if f = 0. then (f, num, den)
    else if Num.gt_num (Num.mult_num den num_frac_base) max_denominator
    then begin
      Printf.printf "Warning: float number has been approximed.\n" ;
      (f, num, den)
    end else begin
      let den = Num.mult_num den num_frac_base in
      let num = Num.mult_num num num_frac_base in
      let f = f *. (Num.float_of_num num_frac_base) in
      let int_f = int_of_float f in
      let f = f -. (float_of_int int_f) in
      let num = Num.add_num num (Num.Int int_f) in
      update_frac_until_exact f num den
    end
  in
  let int_f = int_of_float f in
  let f = f -. (float_of_int int_f) in
  let (_, num, den) = update_frac_until_exact f (Num.Int int_f) (Num.Int 1) in
  Num.div_num num den

let const_to_smt_term c =
  match c with
  | Asttypes.Cbool b -> if b then Term.t_true else Term.t_false
  | Asttypes.Cint i -> Term.make_int (Num.Int i)
  | Asttypes.Creal f -> Term.make_real (float_to_num f)

let declare_symbols_of_node (node:t_node) =
  let add_local symbols ((ident:Ident.t), (t:base_ty)) =
    assert (not (IntMap.mem ident.id symbols)) ;
    let name = Printf.sprintf "%s__%i" ident.name ident.id in
    let t_out = base_type_to_smt_type t in
    let symbol = declare_symbol name [ Type.type_int ] t_out in
    IntMap.add ident.id symbol symbols
  in
  let all_locals = node.tn_input @ node.tn_output @ node.tn_local in
  List.fold_left add_local IntMap.empty all_locals

type local_context = t_node * (Hstring.t IntMap.t)

let get_node_by_id nodes id =
  List.find (fun (n:t_node) -> n.tn_name.id = id) nodes

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
let rec terms_of_operator nodes local_ctx n op exprs =
  let (eqs, ts) = terms_of_exprs nodes local_ctx n exprs in
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
        | Op_gt -> [term_of_formula (Formula.make_lit Formula.Lt [t2 ; t1])]
        | Op_ge -> [term_of_formula (Formula.make_lit Formula.Le [t2 ; t1])]
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
and terms_of_exprs nodes local_ctx n exprs =
  let (eqs, ts) = List.split (List.map (terms_of_expr nodes local_ctx n) exprs) in
  (List.flatten eqs, List.flatten ts)

(* Returns a tuple (eqs,terms) where eqs are some additional required equations *)
and terms_of_expr nodes local_ctx n expr =
  match expr.texpr_desc with
  | TE_const c -> ([],[const_to_smt_term c])
  | TE_ident ident -> ([],[term_of_ident local_ctx n ident])
  | TE_op (op, exprs) -> terms_of_operator nodes local_ctx n op exprs
  | TE_app (id, exprs) ->
    let (eqs, ts) = terms_of_exprs nodes local_ctx n exprs in
    let node = get_node_by_id nodes id.id in
    assert (List.length ts = List.length node.tn_input) ;
    let (node_ctx, node_eqs) = formulas_of_internal_node nodes n node in
    let res = List.map (fun (id,_) -> term_of_ident node_ctx n id) node.tn_output in
    let eq_for_arg (id,_) t =
      let arg_t = term_of_ident node_ctx n id in
      Formula.make_lit Formula.Eq [arg_t ; t]
    in
    let args_eqs = List.map2 eq_for_arg node.tn_input ts in
    (eqs@args_eqs@node_eqs, res)
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
    let (if_eqs,if_ts) = terms_of_expr nodes local_ctx (term_of_int 0) expr1 in
    let (else_eqs,else_ts) = terms_of_expr nodes local_ctx n expr2 in
    (if_eqs@else_eqs, List.map2 (Term.make_ite cond) if_ts else_ts)
  | TE_pre expr ->
    let n_minus_one = Term.make_arith Term.Minus n (term_of_int 1) in
    terms_of_expr nodes local_ctx n_minus_one expr
  | TE_tuple exprs ->
    terms_of_exprs nodes local_ctx n exprs

and formulas_of_eq nodes local_ctx n (eq:t_equation) =
  let pat_terms = terms_of_pattern local_ctx n eq.teq_patt in
  let (eqs,expr_terms) = terms_of_expr nodes local_ctx n eq.teq_expr in
  let new_eqs = List.map2 (fun pt et -> Formula.make_lit Formula.Eq [pt ; et]) pat_terms expr_terms in
  eqs@new_eqs

(* Returns a tuple (local_ctx,formulas) where ctx represents the local contexts of the node *)
and remaining_ctxs = ref []
and created_ctxs = ref []
and formulas_of_internal_node nodes n node =
  let local_ctx =
    match (!remaining_ctxs) with
    | [] ->
      let local_ctx = (node, declare_symbols_of_node node) in
      local_ctx
    | local_ctx::ctxs ->
      remaining_ctxs := ctxs ;
      local_ctx
  in
  created_ctxs := local_ctx::(!created_ctxs);
  let eqs = List.map (formulas_of_eq nodes local_ctx n) node.tn_equs in
  (local_ctx, List.flatten eqs)

(* Returns a tuple (ctx,formulas) where ctx represents the local contexts of the node *)
(* If called on a different main node than last time, 'reinit_ctxs' must be set to true *)
let formulas_of_main_node nodes main_node reinit_ctxs n =
  if reinit_ctxs
  then begin
    remaining_ctxs := [] ;
    created_ctxs := []
  end
  ;
  let (local_ctx, eqs) = formulas_of_internal_node nodes n main_node in
  remaining_ctxs := List.rev (!created_ctxs) ;
  created_ctxs := [] ;
  (local_ctx, eqs)
  