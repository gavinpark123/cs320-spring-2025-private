%{
open Utils
%}

%token LBRACKET
%token RBRACKET
%token LPAREN
%token RPAREN
%token EQUALS
%token SEMICOLON
%token DOLLAR
%token<int> NUM
%token<string> VAR
%token EOF

%start <Utils.prog> prog

%%

prog:
  | lines=lines; EOF { lines }

lines:
  | lines=line* { lines }

line:
  | stmt=stmt; SEMICOLON { stmt }

stmt:
  | x=VAR; EQUALS; e=expr { Assign(x, e) }
  | f=VAR; LPAREN; RPAREN; LBRACKET; p=lines; RBRACKET { FunDef (f, p) }
  | f=VAR; { FunCall(f) }

expr:
  | DOLLAR; x=VAR { Var(x) }
  | n=NUM { Num(n) }
