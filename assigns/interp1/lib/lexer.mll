{
open Parser
}

let whitespace = [' ' '\t' '\n' '\r']+

rule read =
  parse
  | whitespace { read lexbuf }
  | eof { EOF }
