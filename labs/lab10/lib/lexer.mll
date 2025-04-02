{
open Parser
}

let var = ['A'-'Z' 'a'-'z']+
let num = ['0'-'9']+
let whitespace = [' ' '\t' '\n' '\r']+

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
  | whitespace { read lexbuf }
  | eof { EOF }
