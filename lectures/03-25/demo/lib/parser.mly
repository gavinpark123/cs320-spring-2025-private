%{
open Utils
%}

%token EOF
%token FUN
%token ARROW
%token LPAREN
%token RPAREN
%token <string> VAR

%start <Utils.prog> prog

%%

(* <prog> ::= <expr> *)
prog:
  | EOF { Var "x" }

(* <expr> ::= fun <var> -> <expr>
            | <expr2> { <expr2> }
*)

(* <expr2> ::= <var> | ( <expr> ) *)
