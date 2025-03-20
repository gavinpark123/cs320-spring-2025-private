include Utils

let parse (s : string) : expr option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | e -> Some e
  | exception _ -> None

let subst (_ : value) (_ : string) (_ : expr) : expr =
  Unit (* TODO *)

let eval (_ : expr) : (value, error) result =
  Ok VUnit (* TODO *)

let interp (_ : string) : (value, error) result =
  Ok VUnit (* TODO *)
