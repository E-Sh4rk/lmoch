open Aez
open Smt

open Asttypes
open Typed_ast
open Ident

let max_denominator = Num.power_num (Num.Int 2) (Num.Int 64)
let num_frac_base = (Num.Int 2)

module IntMap = Map.Make(struct type t = int let compare = compare end)
module IntroducedSymbolMap = Map.Make(struct type t = string * int * Typed_ast.t_expr_desc let compare = compare end)

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

let type_of_term t =
  if Term.is_int t then Type.type_int
  else if Term.is_real t then Type.type_real
  else Type.type_bool

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

(* Local context : Node * Map from local var to its corresponding Hstring * Map from expressions to its corresponding HString (for other variables that must be introduced) *)
type local_context = t_node * (Hstring.t IntMap.t) * ((Hstring.t IntroducedSymbolMap.t) ref)

let get_node_by_id nodes id =
  List.find (fun (n:t_node) -> n.tn_name.id = id) nodes

let formula_of_term t =
  Formula.make_lit Formula.Eq [t ; Term.t_true]

let term_of_formula f =
  Term.make_ite f Term.t_true Term.t_false

let term_of_int i =
  Term.make_int (Num.Int i)

let term_of_ident local_ctx n ident =
  let (_, ctx_symbols, _) = local_ctx in
  Term.make_app (IntMap.find ident.id ctx_symbols) [n]

let terms_of_pattern local_ctx n pattern =
  List.map (term_of_ident local_ctx n) pattern.tpatt_desc

let introduce_variable local_ctx group id expr t_in t_out =
  let (_,_,m) = local_ctx in
  match IntroducedSymbolMap.find_opt (group, id, expr) (!m) with
  | None ->
    let hstr = declare_symbol (Printf.sprintf "__%s%i" group id) t_in t_out in
    m := IntroducedSymbolMap.add (group, id, expr) hstr (!m) ;
    hstr
  | Some hstr -> hstr

let convert_term_to_int local_ctx origin_expr t =
  let int_var = introduce_variable local_ctx "ri_conversion" 0 origin_expr [] Type.type_int in
  let int_term = Term.make_app int_var [] in
  let eq1 = Formula.make_lit Formula.Le [int_term ; t] in
  let eq2 = Formula.make_lit Formula.Lt [t ; Term.make_arith Term.Plus int_term (term_of_int 1)] in
  ([eq1;eq2], int_term)

let convert_term_to_float local_ctx origin_expr t =
  let float_var = introduce_variable local_ctx "ir_conversion" 0 origin_expr [] Type.type_real in
  let float_term = Term.make_app float_var [] in
  let eq = Formula.make_lit Formula.Eq [float_term ; t] in
  ([eq], float_term)

(* Returns a tuple (eqs,terms) where eqs are some additional required equations *)
let rec terms_of_operator nodes local_ctx n op exprs =
  let (eqs, ts) = terms_of_exprs nodes local_ctx n exprs in
  let (eqs',res) =
    match op with
    | Op_not ->
      assert (List.length ts = 1) ;
      let t = List.hd ts in
      ([],[term_of_formula (Formula.make Formula.Not [formula_of_term t])])
    | Op_if ->
      assert (List.length ts = 3) ;
      let tcond = List.hd ts in
      let tif = List.hd (List.tl ts) in
      let telse = List.hd (List.tl (List.tl ts)) in
      ([],[Term.make_ite (formula_of_term tcond) tif telse])
    (* For arithmetic operators, we assume arguments to be homogeneous (int * int or float * float) *)
    (* In other words, conversions must be explicitly stated using real_of_int and int_of_real *)
    (* We don't do conversions automatically because it seems to make things undecidable for AEZ most of time *)
    | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge
    | Op_add | Op_sub | Op_mul | Op_div | Op_mod
    | Op_add_f | Op_sub_f | Op_mul_f | Op_div_f
    | Op_and | Op_or | Op_impl ->
      assert (List.length ts = 2) ;
      let t1 = List.hd ts in
      let t2 = List.hd (List.tl ts) in
      begin match op with
        | Op_eq -> ([],[term_of_formula (Formula.make_lit Formula.Eq [t1 ; t2])])
        | Op_neq -> ([],[term_of_formula (Formula.make_lit Formula.Neq [t1 ; t2])])
        | Op_lt -> ([],[term_of_formula (Formula.make_lit Formula.Lt [t1 ; t2])])
        | Op_le -> ([],[term_of_formula (Formula.make_lit Formula.Le [t1 ; t2])])
        | Op_gt -> ([],[term_of_formula (Formula.make_lit Formula.Lt [t2 ; t1])])
        | Op_ge -> ([],[term_of_formula (Formula.make_lit Formula.Le [t2 ; t1])])
        | Op_add | Op_add_f -> ([],[Term.make_arith Term.Plus t1 t2])
        | Op_sub | Op_sub_f -> ([],[Term.make_arith Term.Minus t1 t2])
        | Op_mul | Op_mul_f -> ([],[Term.make_arith Term.Mult t1 t2])
        (* AEZ does integer divison when operands are integers, but the semantic is not exactly the same... (t1 is assumed to be a multiple of t2) *)
        (* However, we use AEZ semantic by default for decidability reasons. *)
        | Op_div | Op_div_f -> ([],[Term.make_arith Term.Div t1 t2])
        | Op_mod -> ([],[Term.make_arith Term.Modulo t1 t2])
        | Op_and -> ([],[term_of_formula (Formula.make Formula.And [formula_of_term t1 ; formula_of_term t2])])
        | Op_or -> ([],[term_of_formula (Formula.make Formula.Or [formula_of_term t1 ; formula_of_term t2])])
        | Op_impl -> ([],[term_of_formula (Formula.make Formula.Imp [formula_of_term t1 ; formula_of_term t2])])
        | _ -> assert false
      end
  in
  (eqs@eqs', res)

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
  | TE_prim (id, exprs) ->
    let (eqs, ts) = terms_of_exprs nodes local_ctx n exprs in
    assert (List.length ts = 1) ;
    let t = List.hd ts in
    begin match id.id with
      | id' when id' = Typing.real_of_int.id ->
        let (eqs', t) = convert_term_to_float local_ctx (TE_tuple exprs) t in
        (eqs@eqs', [t])
      | id' when id' = Typing.int_of_real.id ->
        let (eqs', t) = convert_term_to_int local_ctx (TE_tuple exprs) t in
        (eqs@eqs', [t])
      | _ -> failwith "Not supported TE_prim application."
    end
  | TE_arrow (expr1, expr2) ->
    let cond = Formula.make_lit Formula.Eq [n ; term_of_int 0] in
    let (if_eqs,if_ts) = terms_of_expr nodes local_ctx (term_of_int 0) expr1 in
    let (else_eqs,else_ts) = terms_of_expr nodes local_ctx n expr2 in
    (if_eqs@else_eqs, List.map2 (Term.make_ite cond) if_ts else_ts)
  | TE_pre expr ->
    let n_minus_one = Term.make_arith Term.Minus n (term_of_int 1) in
    let (eqs, ts) = terms_of_expr nodes local_ctx n_minus_one expr in
    (* We must introduce a new state var (so it will be taken into account when comparing states for path compression) *)
    let state_vars = List.mapi (fun i t -> introduce_variable local_ctx "state" i expr.texpr_desc [Type.type_int] (type_of_term t)) ts in
    let sv_terms = List.map (fun hstr -> Term.make_app hstr [n_minus_one]) state_vars in
    let eqs' = List.map2 (fun t1 t2 -> Formula.make_lit Formula.Eq [t1;t2]) ts sv_terms in
    (eqs@eqs', sv_terms)
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
      let local_ctx = (node, declare_symbols_of_node node, ref IntroducedSymbolMap.empty) in
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
  
let get_last_contexts _ =
  !remaining_ctxs

let get_all_local_symbols _ =
  let ctxs = get_last_contexts () in
  let add_symbols acc ctx =
    let (_,m,_) = ctx in
    let (_,s) = List.split (IntMap.bindings m) in
    acc@s
  in
  List.fold_left add_symbols [] ctxs

let get_all_introduced_symbols group =
  let ctxs = get_last_contexts () in
  let add_symbols acc ctx =
    let (_,_,m) = ctx in
    let bindings = List.filter (fun ((str,_,_),_) -> str = group) (IntroducedSymbolMap.bindings (!m)) in
    let (_,s) = List.split bindings in
    acc@s
  in
  List.fold_left add_symbols [] ctxs

let conjunction fs =
  match fs with
  | [] -> Formula.f_true
  | [f] -> f (* Conjunctions of < 2 elts results in a runtime exception... *)
  | fs -> Formula.make Formula.And fs

let states_equal_formula n1 n2 =
  let state_symbols = get_all_introduced_symbols "state" in
  let eq_for_symbol s =
    let t1 = Term.make_app s [n1] in
    let t2 = Term.make_app s [n2] in
    Formula.make_lit Formula.Eq [t1; t2]
  in
  let eqs = List.map eq_for_symbol state_symbols in
  conjunction eqs
