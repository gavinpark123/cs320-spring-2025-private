include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let desugar (_ : prog) : expr = assert false

let type_of (_ : expr) : (ty, error) result = assert false

exception AssertFail
exception DivByZero

let eval (_ : expr) :  value = assert false

let interp (_ : string) : (value, error) result = assert false
