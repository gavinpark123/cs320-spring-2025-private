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

prog:
  | e=expr EOF { e }

expr:
  | FUN; x=VAR; ARROW; e=expr { Fun (x, e) }
  | e=expr2; es=expr2* {
    let rec mk_app e es =
      match es with
      | [] -> e
      | x :: es -> mk_app (App (e, x)) es
    (* challenge: write as single call to fold *)
    in mk_app e es
  }

expr2:
  | x=VAR { Var x }
  | LPAREN; e=expr; RPAREN { e }
