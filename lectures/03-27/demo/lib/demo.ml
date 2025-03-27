include Utils

let parse (s : string) : expr option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let expr_of_value (v : value) : expr =
  match v with
  | VFun (x, e) -> Fun (x, e)

let subst (v : value) (x : string) (e : expr) : expr =
  let rec go e =
    match e with
      (* [v / x]x = v
         [v / y]x = x   (where y <> x)
      *)
    | Var y ->
      if x = y
      then expr_of_value v
      else Var y
      (* [v / x](fun x -> e) = fun x -> e
         [v / x](fun y -> e) = fun y -> [v / x] e   (where y <> x)
      *)
    | Fun (y, e) ->
      if x = y
      then Fun(y, e)
      else Fun(y, go e)
      (* [v / x](e1 e2) = ([v / x] e1) ([v / x] e2) *)
    | App (e1, e2) -> App (go e1, go e2)
  in go e

let eval (e : expr) : value option =
  let rec go e =
    match e with
    | Var _ -> None
      (* fun x -> e ==> fun x -> e *)
    | Fun (x, e) -> Some (VFun (x, e))
      (* e1 ==> fun x -> e        e2 ==> v2       [v2 / x]e ==> v
         --------------------------------------------------------
         e1 e2 ==> v
      *)
    | App (e1, e2) -> (
      match go e1 with
      | Some (VFun (x, e)) -> (
        match go e2 with
        | Some v2 -> go (subst v2 x e)
        | None -> None
      )
      | _ -> None
    )
  in go e

let free_vars (e : expr) : string list =
  let rec go e =
    match e with
    | Var x -> [x]
    | Fun (x, e) -> List.filter ((<>) x) (go e)
    | App (e1, e2) -> go e1 @ go e2
  in go e

let interp (s : string) : value option =
  match parse s with
  | Some e ->
    if List.is_empty (free_vars e)
    then eval e
    else None
  | None -> None
