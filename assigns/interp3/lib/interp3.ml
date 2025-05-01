include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | prog -> Some prog
  | exception _ -> None

(* Substitution type *)
type substitution = (string * ty) list

(* Apply a substitution to a type *)
let rec apply_subst (s : substitution) (t : ty) : ty =
  match t with
  | TUnit | TInt | TFloat | TBool -> t
  | TVar x -> 
      (match List.assoc_opt x s with
       | Some t' -> 
          (* Avoid infinite recursion by checking if t' = TVar x *)
          if t' = TVar x then t else apply_subst s t'
       | None -> t)
  | TList t' -> TList (apply_subst s t')
  | TOption t' -> TOption (apply_subst s t')
  | TPair (t1, t2) -> TPair (apply_subst s t1, apply_subst s t2)
  | TFun (t1, t2) -> TFun (apply_subst s t1, apply_subst s t2)

(* Apply a substitution to a list of constraints *)
let apply_subst_to_constraints (s : substitution) (cs : constr list) : constr list =
  List.map (fun (t1, t2) -> (apply_subst s t1, apply_subst s t2)) cs

(* Get free variables in a type *)
let rec free_vars (t : ty) : VarSet.t =
  match t with
  | TUnit | TInt | TFloat | TBool -> VarSet.empty
  | TVar x -> VarSet.singleton x
  | TList t' -> free_vars t'
  | TOption t' -> free_vars t'
  | TPair (t1, t2) -> VarSet.union (free_vars t1) (free_vars t2)
  | TFun (t1, t2) -> VarSet.union (free_vars t1) (free_vars t2)

(* Check if a variable occurs in a type (occurs check) *)
let rec occurs (x : string) (t : ty) : bool =
  match t with
  | TUnit | TInt | TFloat | TBool -> false
  | TVar y -> x = y
  | TList t' -> occurs x t'
  | TOption t' -> occurs x t'
  | TPair (t1, t2) -> occurs x t1 || occurs x t2
  | TFun (t1, t2) -> occurs x t1 || occurs x t2

(* Compose two substitutions *)
let compose_subst (s1 : substitution) (s2 : substitution) : substitution =
  (* Apply s1 to all types in s2 *)
  let s2' = List.map (fun (x, t) -> (x, apply_subst s1 t)) s2 in
  (* Keep s1 bindings and add s2 bindings that don't override s1 *)
  s1 @ List.filter (fun (x, _) -> 
    not (List.exists (fun (y, _) -> x = y) s1)
  ) s2'

(* Unification algorithm *)
let rec unify (cs : constr list) : substitution option =
  match cs with
  | [] -> Some []
  | (t1, t2) :: cs' when t1 = t2 -> 
      (* Types are identical, just continue *)
      unify cs'
  | (TVar x, t) :: cs' ->
      if occurs x t then
        (* Occurs check failure - circular type *)
        None
      else
        let s = [(x, t)] in
        let cs'' = apply_subst_to_constraints s cs' in
        (match unify cs'' with
        | None -> None
        | Some s' -> Some (compose_subst s' s))
  | (t, TVar x) :: cs' ->
      (* Swap and handle the same way *)
      unify ((TVar x, t) :: cs')
  | (TList t1, TList t2) :: cs' ->
      unify ((t1, t2) :: cs')
  | (TOption t1, TOption t2) :: cs' ->
      unify ((t1, t2) :: cs')
  | (TPair (t1a, t1b), TPair (t2a, t2b)) :: cs' ->
      unify ((t1a, t2a) :: (t1b, t2b) :: cs')
  | (TFun (t1a, t1b), TFun (t2a, t2b)) :: cs' ->
      unify ((t1a, t2a) :: (t1b, t2b) :: cs')
  | _ -> None

(* Function to determine the principle type from a type and constraints *)
let principle_type (ty : ty) (cs : constr list) : ty_scheme option =
  match unify cs with
  | None -> None
  | Some s ->
      let substituted_ty = apply_subst s ty in
      (* Get all free type variables in the resulting type *)
      let free_type_vars = free_vars substituted_ty in
      Some (Forall (free_type_vars, substituted_ty))

(* Apply a substitution to a type scheme *)
let apply_subst_to_scheme (s : substitution) (Forall (vars, ty)) : ty_scheme =
  (* Remove bound variables from the substitution *)
  let s' = List.filter (fun (x, _) -> not (VarSet.mem x vars)) s in
  Forall (vars, apply_subst s' ty)

(* Get free variables in a type scheme *)
let free_vars_scheme (Forall (vars, ty)) : VarSet.t =
  VarSet.diff (free_vars ty) vars

(* Get free variables in an environment *)
let free_vars_env (env : stc_env) : VarSet.t =
  Env.fold (fun _ scheme acc -> 
    VarSet.union acc (free_vars_scheme scheme)
  ) env VarSet.empty

(* Apply substitution to an environment *)
let apply_subst_to_env (s : substitution) (env : stc_env) : stc_env =
  Env.map (apply_subst_to_scheme s) env

(* Create a fresh instance of a type scheme *)
let instantiate (Forall (vars, ty)) : ty =
  let subst = VarSet.fold (fun var acc ->
    let fresh_var = gensym () in
    (var, TVar fresh_var) :: acc
  ) vars [] in
  apply_subst subst ty

(* Generalize a type to a type scheme *)
let generalize (env : stc_env) (ty : ty) : ty_scheme =
  let env_vars = free_vars_env env in
  let ty_vars = free_vars ty in
  let generalized_vars = VarSet.diff ty_vars env_vars in
  Forall (generalized_vars, ty)

(* Type inference for expressions *)
let type_of (ctxt : stc_env) (e : expr) : ty_scheme option =
  let rec collect_constraints (current_ctxt : stc_env) (e : expr) : (ty * constr list) =
    match e with
    | Unit -> (TUnit, [])
    | Bool _ -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | Nil ->
      let a = TVar (gensym ()) in
      (TList a, [])
    | ENone ->
      let a = TVar (gensym ()) in
      (TOption a, [])
    | Var x ->
      (match Env.find_opt x current_ctxt with
       | Some scheme -> (instantiate scheme, [])
       | None -> failwith ("Unbound variable: " ^ x))
    | Bop (op, e1, e2) ->
      let (t1, c1) = collect_constraints current_ctxt e1 in
      let (t2, c2) = collect_constraints current_ctxt e2 in
      (match op with
       | Add | Sub | Mul | Div | Mod ->
         (TInt, c1 @ c2 @ [(t1, TInt); (t2, TInt)])
       | AddF | SubF | MulF | DivF | PowF ->
         (TFloat, c1 @ c2 @ [(t1, TFloat); (t2, TFloat)])
       | Lt | Lte | Gt | Gte | Eq | Neq ->
         (* Note: Comparisons are allowed between values of the same type,
            but the result is always boolean. The constraint (t1, t2)
            ensures the operands have the same type. *)
         (TBool, c1 @ c2 @ [(t1, t2)])
       | And | Or ->
         (TBool, c1 @ c2 @ [(t1, TBool); (t2, TBool)])
       | Cons ->
         let element_type = TVar (gensym ()) in
         (TList element_type, c1 @ c2 @ [(t1, element_type); (t2, TList element_type)])
       | Comma -> (TPair (t1, t2), c1 @ c2))
    | If (e1, e2, e3) ->
      let (t1, c1) = collect_constraints current_ctxt e1 in
      let (t2, c2) = collect_constraints current_ctxt e2 in
      let (t3, c3) = collect_constraints current_ctxt e3 in
      (t2, c1 @ c2 @ c3 @ [(t1, TBool); (t2, t3)])
    | Fun (x, t_opt, body) ->
      let arg_type = match t_opt with
        | Some t -> t
        | None -> TVar (gensym ()) in
      let extended_ctxt = Env.add x (Forall (VarSet.empty, arg_type)) current_ctxt in
      let (body_type, body_constraints) = collect_constraints extended_ctxt body in
      (TFun (arg_type, body_type), body_constraints)
    | App (e1, e2) ->
      let (t1, c1) = collect_constraints current_ctxt e1 in
      let (t2, c2) = collect_constraints current_ctxt e2 in
      let result_type = TVar (gensym ()) in
      (result_type, c1 @ c2 @ [(t1, TFun (t2, result_type))])
    | Annot (e, t) ->
      let (inferred_t, cs) = collect_constraints current_ctxt e in
      (t, cs @ [(inferred_t, t)])
    | Let { is_rec = false; name; binding; body } ->
      let (binding_type, binding_constraints) = collect_constraints current_ctxt binding in
      (match unify binding_constraints with
       | None -> failwith "Type error in let binding unification"
       | Some s ->
         let substituted_binding_ty = apply_subst s binding_type in
         (* Generalize based on the *substituted* environment S(Γ) *)
         let substituted_env = apply_subst_to_env s current_ctxt in 
         let generalized_scheme = generalize substituted_env substituted_binding_ty in
         let extended_ctxt = Env.add name generalized_scheme current_ctxt in
         let (body_type, body_constraints) = collect_constraints extended_ctxt body in
         let final_body_constraints = apply_subst_to_constraints s body_constraints in
         (body_type, binding_constraints @ final_body_constraints))
    | Let { is_rec = true; name; binding; body } ->
      let rec_var_type = TVar (gensym ()) in
      let temp_ctxt = Env.add name (Forall (VarSet.empty, rec_var_type)) current_ctxt in
      let (binding_type, binding_constraints) = collect_constraints temp_ctxt binding in
      let full_constraints = binding_constraints @ [(rec_var_type, binding_type)] in
       (match unify full_constraints with
       | None -> failwith "Type error in recursive let binding unification"
       | Some s ->
         let substituted_rec_ty = apply_subst s rec_var_type in
         (* Generalize based on the *substituted* environment S(Γ) *)
         let substituted_env = apply_subst_to_env s current_ctxt in
         let generalized_scheme = generalize substituted_env substituted_rec_ty in 
         let extended_ctxt = Env.add name generalized_scheme current_ctxt in
         let (body_type, body_constraints) = collect_constraints extended_ctxt body in
         let final_body_constraints = apply_subst_to_constraints s body_constraints in
         (body_type, full_constraints @ final_body_constraints))
    | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
      let (matched_type, matched_constraints) = collect_constraints current_ctxt matched in
      let element_type = TVar (gensym ()) in
      let list_type = TList element_type in
      let extended_ctxt_cons = Env.add hd_name (Forall (VarSet.empty, element_type))
                                (Env.add tl_name (Forall (VarSet.empty, list_type)) current_ctxt) in
      let (cons_type, cons_constraints) = collect_constraints extended_ctxt_cons cons_case in
      let (nil_type, nil_constraints) = collect_constraints current_ctxt nil_case in
      (cons_type, matched_constraints @ cons_constraints @ nil_constraints @
                [(matched_type, list_type); (cons_type, nil_type)])
    | OptMatch { matched; some_name; some_case; none_case } ->
      let (matched_type, matched_constraints) = collect_constraints current_ctxt matched in
      let element_type = TVar (gensym ()) in
      let option_type = TOption element_type in
      let extended_ctxt_some = Env.add some_name (Forall (VarSet.empty, element_type)) current_ctxt in
      let (some_type, some_constraints) = collect_constraints extended_ctxt_some some_case in
      let (none_type, none_constraints) = collect_constraints current_ctxt none_case in
      (some_type, matched_constraints @ some_constraints @ none_constraints @
                [(matched_type, option_type); (some_type, none_type)])
    | PairMatch { matched; fst_name; snd_name; case } ->
      let (matched_type, matched_constraints) = collect_constraints current_ctxt matched in
      let fst_type = TVar (gensym ()) in
      let snd_type = TVar (gensym ()) in
      let pair_type = TPair (fst_type, snd_type) in
      let extended_ctxt = Env.add fst_name (Forall (VarSet.empty, fst_type))
                            (Env.add snd_name (Forall (VarSet.empty, snd_type)) current_ctxt) in
      let (case_type, case_constraints) = collect_constraints extended_ctxt case in
      (case_type, matched_constraints @ case_constraints @ [(matched_type, pair_type)])
    | Assert e ->
      let (t, cs) = collect_constraints current_ctxt e in
      (TUnit, cs @ [(t, TBool)])
    | ESome e ->
      let (t, cs) = collect_constraints current_ctxt e in
      (TOption t, cs)
  
  in
  
  try
    let (ty, constraints) = collect_constraints ctxt e in (* Initial call uses the provided ctxt *)
    match unify constraints with
    | None -> None
    | Some s ->
        let final_type = apply_subst s ty in
        (* Generalize based on the *substituted* environment S(Γ) *)
        let final_env = apply_subst_to_env s ctxt in
        let scheme = generalize final_env final_type in
        Some scheme
  with
  | Failure _msg -> 
      (* Print the failure message for debugging *)
      (* print_endline ("Type inference failed: " ^ msg); *)
      None

let is_well_typed (p : prog) : bool =
  let rec check_bindings env = function
    | [] -> true
    | {is_rec; name; binding} :: rest ->
        if is_rec then
          (* For recursive bindings, add the name with a placeholder type first *)
          let placeholder_type = TVar (gensym ()) in
          let temp_env = Env.add name (Forall (VarSet.empty, placeholder_type)) env in
          match type_of temp_env binding with
          | None -> false
          | Some scheme ->
              let new_env = Env.add name scheme env in
              check_bindings new_env rest
        else
          (* For non-recursive bindings, check the binding with the current environment *)
          match type_of env binding with
          | None -> false
          | Some scheme ->
              let new_env = Env.add name scheme env in
              check_bindings new_env rest
  in
  check_bindings Env.empty p

exception AssertFail
exception DivByZero
exception CompareFunVals

let rec eval_expr (env : dyn_env) (e : expr) : value =
  match e with
  | Unit -> VUnit
  | Bool b -> VBool b
  | Int n -> VInt n
  | Float f -> VFloat f
  | Nil -> VList []
  | ENone -> VNone
  | Var x ->
      (match Env.find_opt x env with
       | Some v -> v
       | None -> failwith ("Unbound variable: " ^ x))
  | Bop (op, e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      (match op, v1, v2 with
       | Add, VInt n1, VInt n2 -> VInt (n1 + n2)
       | Sub, VInt n1, VInt n2 -> VInt (n1 - n2)
       | Mul, VInt n1, VInt n2 -> VInt (n1 * n2)
       | Div, VInt n1, VInt n2 ->
           if n2 = 0 then raise DivByZero else VInt (n1 / n2)
       | Mod, VInt n1, VInt n2 ->
           if n2 = 0 then raise DivByZero else VInt (n1 mod n2)
       | AddF, VFloat f1, VFloat f2 -> VFloat (f1 +. f2)
       | SubF, VFloat f1, VFloat f2 -> VFloat (f1 -. f2)
       | MulF, VFloat f1, VFloat f2 -> VFloat (f1 *. f2)
       | DivF, VFloat f1, VFloat f2 -> VFloat (f1 /. f2)
       | PowF, VFloat f1, VFloat f2 -> VFloat (f1 ** f2)
       | Lt, v1, v2 -> VBool (compare_values v1 v2 < 0)
       | Lte, v1, v2 -> VBool (compare_values v1 v2 <= 0)
       | Gt, v1, v2 -> VBool (compare_values v1 v2 > 0)
       | Gte, v1, v2 -> VBool (compare_values v1 v2 >= 0)
       | Eq, v1, v2 -> VBool (compare_values v1 v2 = 0)
       | Neq, v1, v2 -> VBool (compare_values v1 v2 <> 0)
       | And, VBool b1, VBool b2 -> VBool (b1 && b2)
       | Or, VBool b1, VBool b2 -> VBool (b1 || b2)
       | Cons, v, VList vs -> VList (v :: vs)
       | Comma, v1, v2 -> VPair (v1, v2)
       | _ -> failwith "Type error in binary operation")
  | If (cond, then_expr, else_expr) ->
      (match eval_expr env cond with
       | VBool true -> eval_expr env then_expr
       | VBool false -> eval_expr env else_expr
       | _ -> failwith "Type error in if condition")
  | Fun (x, _, body) -> VClos { name = None; arg = x; body; env }
  | App (e1, e2) ->
      let func = eval_expr env e1 in
      let arg = eval_expr env e2 in
      (match func with
       | VClos { name; arg = param; body; env = closure_env } ->
           let extended_env = match name with
             | Some f -> Env.add f func (Env.add param arg closure_env)
             | None -> Env.add param arg closure_env
           in
           eval_expr extended_env body
       | _ -> failwith "Type error: not a function")
  | Annot (e, _) -> eval_expr env e
  | Let { is_rec; name; binding; body } ->
      if is_rec then
        (* Handle let rec (assuming function binding) *)
        (* Create a placeholder environment for evaluating the binding *)
        let placeholder_env = Env.add name VUnit env (* Placeholder value doesn't matter *)
in        (* Evaluate the binding in the placeholder environment *)
        (match eval_expr placeholder_env binding with
         | VClos clos ->
             (* Create the final recursive environment including the closure itself *)
             let rec_env = Env.add name (VClos clos) env in
             (* Create the final closure with the recursive environment *)
             let final_closure = VClos { clos with name = Some name; env = rec_env } in
             (* Evaluate the body in an environment extended with the final recursive closure *)
             eval_expr (Env.add name final_closure env) body
         | _ -> failwith "Runtime error: let rec binding did not evaluate to a function")
      else
        (* Handle non-recursive let *)
        let binding_value = eval_expr env binding in
        let extended_env = Env.add name binding_value env in
        eval_expr extended_env body
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
      (match eval_expr env matched with
       | VList [] -> eval_expr env nil_case
       | VList (hd :: tl) ->
           let extended_env = Env.add hd_name hd (Env.add tl_name (VList tl) env) in
           eval_expr extended_env cons_case
       | _ -> failwith "Type error in list match")
  | OptMatch { matched; some_name; some_case; none_case } ->
      (match eval_expr env matched with
       | VNone -> eval_expr env none_case
       | VSome value ->
           let extended_env = Env.add some_name value env in
           eval_expr extended_env some_case
       | _ -> failwith "Type error in option match")
  | PairMatch { matched; fst_name; snd_name; case } ->
      (match eval_expr env matched with
       | VPair (first, second) ->
           let extended_env = Env.add fst_name first (Env.add snd_name second env) in
           eval_expr extended_env case
       | _ -> failwith "Type error in pair match")
  | Assert e ->
      (match eval_expr env e with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> failwith "Type error in assertion")
  | ESome e -> VSome (eval_expr env e)

(* Compare values - used for comparison operators *)
and compare_values v1 v2 =
  match v1, v2 with
  | VUnit, VUnit -> 0
  | VBool b1, VBool b2 -> compare b1 b2
  | VInt n1, VInt n2 -> compare n1 n2
  | VFloat f1, VFloat f2 -> compare f1 f2
  | VList l1, VList l2 -> compare_lists l1 l2
  | VPair (a1, b1), VPair (a2, b2) ->
      let comp_a = compare_values a1 a2 in
      if comp_a <> 0 then comp_a else compare_values b1 b2
  | VNone, VNone -> 0
  | VNone, VSome _ -> -1
  | VSome _, VNone -> 1
  | VSome v1, VSome v2 -> compare_values v1 v2
  | VClos _, VClos _ -> raise CompareFunVals
  | _ -> failwith "Type error in comparison"

(* Compare lists - helper for compare_values *)
and compare_lists l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | h1 :: t1, h2 :: t2 ->
      let comp_h = compare_values h1 h2 in
      if comp_h <> 0 then comp_h else compare_lists t1 t2

let eval p =
  let rec nest = function
    | [] -> Unit
    | [{is_rec;name;binding}] -> Let {is_rec;name;binding;body = Var name}
    | {is_rec;name;binding} :: ls -> Let {is_rec;name;binding;body = nest ls}
  in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog ->
    if is_well_typed prog
    then Ok (eval prog)
    else Error TypeError
  | None -> Error ParseError
