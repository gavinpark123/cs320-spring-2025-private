include Utils

let parse (s : string) : expr option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let eval (_ : expr) : value option = assert false
let interp (_ : string) : value option = assert false
