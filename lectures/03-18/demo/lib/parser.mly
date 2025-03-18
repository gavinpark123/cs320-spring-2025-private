%{
open Utils
%}

%token LET
%token EQ
%token IN
%token ADD
%token SUB
%token MUL
%token DIV
%token LPAREN
%token RPAREN
%token<int> NUM
%token<string> VAR
%token EOF

%left ADD SUB
%left MUL DIV

%start <Utils.prog> prog

%%

prog:
  | e = expr; EOF { e }

expr:
  | LET; x = var; EQ; e1 = expr; IN; e2 = expr
    { Let (x, e1, e2) }
  | e = expr1 { e }

%inline bop:
  | ADD { Add }
  | SUB { Sub }
  | MUL { Mul }
  | DIV { Div }

expr1:
  | e1 = expr1; op = bop; e2 = expr1
    { Bop (op, e1, e2) }
  | n = num { Num n }
  | v = var { Var v }
  | LPAREN; e = expr; RPAREN { e }

num:
  | n = NUM { n }

var:
  | x = VAR { x }
