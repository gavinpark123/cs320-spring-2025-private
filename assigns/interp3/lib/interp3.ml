include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | prog -> Some prog
  | exception _ -> None

  let rec freevars (ty : ty) : VarSet.t =
    match ty with
    | TUnit | TInt | TFloat | TBool -> VarSet.empty
    | TVar v -> VarSet.singleton v
    | TList t | TOption t -> freevars t
    | TPair (t1, t2) | TFun (t1, t2) -> VarSet.union (freevars t1) (freevars t2)
  
  module Subst = Map.Make(String)
  type subst = ty Subst.t
  
  let rec apply_subst (s : subst) (ty : ty) : ty =
    match ty with
    | TUnit | TInt | TFloat | TBool -> ty
    | TVar v -> (match Subst.find_opt v s with Some t -> t | None -> TVar v)
    | TList t -> TList (apply_subst s t)
    | TOption t -> TOption (apply_subst s t)
    | TPair (t1, t2) -> TPair (apply_subst s t1, apply_subst s t2)
    | TFun (t1, t2) -> TFun (apply_subst s t1, apply_subst s t2)
  
  let subst_domain (s : subst) : VarSet.t =
    Subst.fold (fun v _ acc -> VarSet.add v acc) s VarSet.empty
  
  let rec occurs (v : string) (ty : ty) : bool =
    match ty with
    | TVar x -> x = v
    | TList t | TOption t -> occurs v t
    | TPair (t1, t2) | TFun (t1, t2) -> occurs v t1 || occurs v t2
    | _ -> false
  
  let unify (cs : constr list) : subst option =
    let rec unify_aux (s : subst) (cs : constr list) : subst option =
      match cs with
      | [] -> Some s
      | (t1, t2) :: rest ->
          let t1 = apply_subst s t1 in
          let t2 = apply_subst s t2 in
          match (t1, t2) with
          | _ when t1 = t2 -> unify_aux s rest
          | (TVar v, t) | (t, TVar v) ->
              if t = TVar v then unify_aux s rest
              else if occurs v t then None
              else
                let s' = Subst.add v t s in
                unify_aux s' (List.map (fun (a, b) -> (apply_subst s' a, apply_subst s' b)) rest)
          | (TFun (a1, a2), TFun (b1, b2))
          | (TPair (a1, a2), TPair (b1, b2)) ->
              unify_aux s ((a1, b1) :: (a2, b2) :: rest)
          | (TList t1, TList t2) ->
              unify_aux s ((t1, t2) :: rest)
          | (TOption t1, TOption t2) ->
              unify_aux s ((t1, t2) :: rest)
          | _ -> None
    in
    unify_aux Subst.empty cs
  
  let principle_type (ty : ty) (cs : constr list) : ty_scheme option =
    match unify cs with
    | None -> None
    | Some s ->
        let ty' = apply_subst s ty in
        let free = VarSet.diff (freevars ty') (subst_domain s) in
        Some (Forall (free, ty'))

let type_of (_ctxt: stc_env) (_e : expr) : ty_scheme option = assert false

let is_well_typed (_p : prog) : bool = assert false

exception AssertFail
exception DivByZero
exception CompareFunVals

let eval_expr (_env : dyn_env) (_e : expr) : value = assert false

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
