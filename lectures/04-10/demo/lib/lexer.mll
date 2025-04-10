{
open Parser
}

let whitespace = [' ' '\n' '\t' '\r']+
let var = ['a'-'z']+
let ty_var = '\'' ['a'-'z']+
let num = '-'? ['0'-'9']+

rule read =
  parse
  | "." { PERIOD }
  | ":" { COLON }
  | "int" { INTTY }
  | "bool" { BOOLTY }
  | "fun" { FUN }
  | "let" { LET }
  | "rec" { REC }
  | "=" { EQ }
  | "in" { IN }
  | "->" { ARROW }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "+" { PLUS }
  | num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | var { VAR (Lexing.lexeme lexbuf) }
  | ty_var { TYVAR (Lexing.lexeme lexbuf) }
  | whitespace { read lexbuf }
  | eof { EOF }
