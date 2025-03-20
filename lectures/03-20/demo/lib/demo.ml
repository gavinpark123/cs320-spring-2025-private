let parse s =
  try Some (Parser.prog Lexer.read (Lexing.from_string s))
  with _ -> None
