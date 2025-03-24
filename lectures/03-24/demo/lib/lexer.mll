{
open Parser
}

let whitespace = [' ' '\n' '\t' '\r']+
let var = ['a'-'z']+

rule read =
  parse
  | "fun" { FUN }
  | "->" { ARROW }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | var { VAR (Lexing.lexeme lexbuf) }
  | whitespace { read lexbuf }
  | eof { EOF }
