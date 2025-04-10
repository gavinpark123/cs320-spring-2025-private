include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let rec desugar (p : prog) : expr =
  match p with
  | [] -> assert false
  | TLet (name, ty, binding) :: [] ->
    Let (name, ty, binding, Var name)
  | TLetRec (name, arg, arg_ty, ty, binding) :: [] ->
    LetRec (name, arg, arg_ty, ty, binding, Var name)
  | TLet (name, ty, binding) :: p ->
    let body = desugar p in
    Let (name, ty, binding, body)
  | TLetRec (name, arg, arg_ty, ty, binding) :: p ->
    let body = desugar p in
    LetRec (name, arg, arg_ty, ty, binding, body)

type ctxt = ty Env.t

(* ADDED *)
let replace_var y x =
  let rec go = function
    | IntTy -> IntTy
    | BoolTy -> BoolTy
    | TyVar z -> if z = x then TyVar y else TyVar z
    | FunTy (t1, t2) -> FunTy (go t1, go t2)
    | Forall (z, ty') -> Forall (z, if z = x then ty' else go ty')
  in go

let mk_fresh () =
  let count = ref 0 in
  let f () =
    count := !count + 1;
    string_of_int !count
  in f

let fresh = mk_fresh ()

let ty_subst ty x =
  let rec go = function
    | IntTy -> IntTy
    | BoolTy -> BoolTy
    | TyVar y -> if y = x then ty else TyVar y
    | FunTy (t1, t2) -> FunTy (go t1, go t2)
    | Forall (y, ty') ->
      if x = y then Forall(y, ty')
      else
        let new_var = fresh () in
        Forall (new_var, go (replace_var new_var y ty'))
  in go
(* END ADDED *)

let type_of (e : expr) : ty option =
  let rec type_of (ctxt : ctxt) (e : expr) : ty option =
    let rec go e =
      match e with
      (* ADDED *)
      | TyFun(x, e) -> (
        match go e with
        | Some ty -> Some (Forall (x, ty))
        | _ -> None
      )
      | TyApp (e, ty) -> (
        match go e with
        | Some (Forall (x, ty')) -> Some (ty_subst ty x ty')
        | _ -> None
      )
      (* END ADDED *)
      | Var x -> Env.find_opt x ctxt
      | Num _ -> Some IntTy
        (* ctxt, x : ty |- e : ty'               *)
        (* ------------------------------------- *)
        (* ctxt |- fun (x : ty) -> e : ty -> ty' *)
      | Fun (x, ty, e) -> (
        let ctxt = Env.add x ty ctxt in
        match type_of ctxt e with
        | Some ty' -> Some (FunTy (ty, ty'))
        | None -> None (* type error *)
      )
        (* ctxt |- e1 : ty -> ty' ctxt |- e2 : ty *)
        (* -------------------------------------- *)
        (* ctxt |- e1 e2 : ty'                    *)
      | App (e1, e2) -> (
        match go e1 with
        | Some (FunTy(ty, ty')) -> (
          match go e2 with
          | Some ty'' ->
            if ty'' = ty
            then Some ty'
            else None
          | _ -> None
        )
        | _ -> None
      )
      | Add (e1, e2) -> (
        match go e1 with
        | Some IntTy -> (
          match go e2 with
          | Some IntTy -> Some IntTy
          | _ -> None
        )
        | _ -> None
      )
      | Eq (e1, e2) -> (
        match go e1 with
        | Some IntTy -> (
          match go e2 with
          | Some IntTy -> Some BoolTy
          | _ -> None
        )
        | _ -> None
      )
      | If (e1, e2, e3) -> (
        match go e1 with
        | Some BoolTy -> (
          match go e2 with
          | Some t1 -> (
            match go e3 with
            | Some t2 ->
              if t1 = t2
              then Some t1
              else None
            | _ -> None
          )
          | _ -> None
        )
        | _ -> None
      )
      | Let (x, ty_ann, e1, e2) -> (
        match go e1 with
        | Some ty ->
          if ty = ty_ann
          then
            let ctxt = Env.add x ty_ann ctxt in
            type_of ctxt e2
          else None
        | _ -> None
      )
      | LetRec (f, x, x_ty, ty_ann, e1, e2) -> (
        let ctxt = Env.add f (FunTy (x_ty, ty_ann)) ctxt in
        let ctxt' = Env.add x x_ty ctxt in
        match type_of ctxt' e1 with
        | Some ty ->
          if ty = ty_ann
          then type_of ctxt e2
          else None
        | _ -> None
      )
    in go e
  in type_of Env.empty e

let rec eval (env : env) (e : expr) : value option =
  let rec go e =
    match e with
    (* ADDED *)
    | TyFun(_, e) -> go e
    | TyApp(e, _) -> go e
    (* END ADDED *)
    | LetRec(f, x, _, _, e1, e2) ->
      (* < env[f -> (env, fun x -> e1, f)] , e2 > *)
      eval (Env.add f (VClos (x, e1, env, Some f)) env) e2
    | Let(x, _, e1, e2) -> (
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
          (* < env , e2 > ==> v2 *)
        | Some v2 ->
          let env' = Env.add f (VClos (x, e, env', Some f)) env' in
          let env' = Env.add x v2 env' in
          (* < env'[f -> (env', fun x -> e, f)][x -> v2] , e > ==> v *)
          eval env' e
        | None -> None
      )
      | _ -> None
    )
    | Var x -> Env.find_opt x env
    | Num n -> Some (VNum n)
    | Fun (x, _, e) -> Some (VClos (x, e, env, None))
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

let interp (s : string) : value option =
  match parse s with
  | Some prog -> (
    let expr = desugar prog in
    match type_of expr with
    | Some _ -> eval Env.empty expr
    | _ -> None
  )
  | None -> None
