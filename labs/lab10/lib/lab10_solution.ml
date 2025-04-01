include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let eval_step (env, p) =
  match p with
  | [] -> None
  | Assign (x, Num n) :: p -> Some (Env.add x (VNum n) env, p)
  | Assign (x, Var y) :: p -> (
     match Env.find_opt y env with
     | Some (VNum n) -> Some (Env.add x (VNum n) env, p)
     | _ -> None
  )
  | FunDef (f, q) :: p -> Some (Env.add f (VProg q) env, p)
  | FunCall f :: p -> (
    match Env.find_opt f env with
    | Some (VProg q) -> Some (env, q @ p)
    | _ -> None
  )

let rec eval c =
  match c with
  | (_, []) -> print_endline (string_of_config c ^ " ✓")
  | _ ->
     let _ = print_string (string_of_config c) in
     match eval_step c with
     | Some c -> let _ = print_endline " ⟶"  in eval c
     | None -> print_endline " STUCK!"

let interp s =
  match parse s with
  | Some p -> eval (Env.empty, p)
  | None -> print_endline "parse error"
