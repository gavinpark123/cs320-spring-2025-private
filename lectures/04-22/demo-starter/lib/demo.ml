include Utils

let parse (s : string) : expr option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let rec eval (env : env) (e : expr) : value option =
  let rec go e =
    match e with
    | LetRec(f, x, e1, e2) ->
      eval (Env.add f (VClos (x, e1, env, Some f)) env) e2
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

let interp (s : string) : value option =
  match parse s with
  | Some expr -> eval Env.empty expr
  | None -> None
