{
open Parser
}

let var = ['A'-'Z']
let num = ['0'-'9']

rule read =
  parse
  | "{" { LBRACKET }
  | "}" { RBRACKET }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "=" { EQUALS }
  | ";" { SEMICOLON }
  | "$" { DOLLAR }
  | num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | var { VAR (Lexing.lexeme lexbuf) }
  | eof { EOF }
