include Utils

let parse (s : string) : string sexpr option =
  match Parser.sexpr Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None
