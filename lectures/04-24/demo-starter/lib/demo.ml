include Utils

type constr = ty * ty
type solution = (string * ty) list

let ty_subst (ty : ty) (x : string) : ty -> ty =
  let rec go = function
    | TInt -> TInt
    | TBool -> TBool
    | TFun (t1, t2) -> TFun (go t1, go t2)
    | TVar y -> if x = y then ty else TVar y
  in go

let rec free = function
  | TInt -> VarSet.empty
  | TBool -> VarSet.empty
  | TFun (t1, t2) -> VarSet.union (free t1) (free t2)
  | TVar x -> VarSet.singleton x

let rec unify (s : solution) (cs : constr list) : solution option =
  let rec go = function
    | [] -> Some (List.rev s)
    | (t1, t2) :: cs when t1 = t2 -> go cs
    | (TFun (s1, t1), TFun (s2, t2)) :: cs -> go ((s1, s2) :: (t1, t2) :: cs)
    | (TVar x, ty) :: cs when not (VarSet.mem x (free ty)) ->
      unify
        ((x, ty) :: s)
        (List.map
          (fun (t1, t2) -> (ty_subst ty x t1, ty_subst ty x t2))
          cs)
    | (ty, TVar x) :: cs -> go ((TVar x, ty) :: cs)
    | _ -> None
  in go cs
let unify = unify []

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let rec eval (env : env) (e : expr) : value option =
  let rec go e =
    match e with
    | Let(x, e1, e2) -> (
      match go e1 with
        (* < env, e1 > ==> v1 *)
      | Some v1 ->
        (* < env[x -> v1] , e2 > ==> v2 *)
        eval (Env.add x v1 env) e2
      | _ -> None
    )
    | App (e1, e2) -> (
      match go e1 with
        (* < env, e1 > ==> (fun x -> e, env') *)
      | Some (VClos (x, e, env', None)) -> (
        match go e2 with
          (* < env, e2 > ==> v2 *)
        | Some v2 ->
          (* < env'[x -> v2], e > ==> v *)
          eval (Env.add x v2 env') e
        | _ -> None
      )
      | Some (VClos (x, e, env', Some f)) -> (
        match go e2 with
        | Some v2 ->
          let env' = Env.add x v2 env' in
          let env' = Env.add f (VClos (x, e, env', Some f)) env' in
          eval env' e
        | _ -> None
      )
      | _ -> None
    )
    | Var x -> Env.find_opt x env
    | Num n -> Some (VNum n)
    | Fun (x, e) -> Some (VClos (x, e, env, None))
    | Add (e1, e2) -> (
      match go e1 with
      | Some (VNum m) -> (
        match go e2 with
        | Some (VNum n) -> Some (VNum (m + n))
        | _ -> None
      )
      | _ -> None
    )
    | Eq (e1, e2) -> (
      match go e1 with
      | Some (VNum m) -> (
        match go e2 with
        | Some (VNum n) -> Some (VBool (m = n))
        | _ -> None
      )
      | _ -> None
    )
    | If (e1, e2, e3) -> (
      match go e1 with
      | Some (VBool b) ->
         if b
         then go e2
         else go e3
      | _ -> None
    )
  in go e

let rec desugar = function
  | [] -> assert false
  | (name, binding) :: [] -> Let (name, binding, Var name)
  | (name, binding) :: p ->
    Let (name, binding, desugar p)

let interp (s : string) : value option =
  match parse s with
  | Some p -> eval Env.empty (desugar p)
  | None -> None
