include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let eval_step (_c : env * prog) : (env * prog) option = assert false

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
