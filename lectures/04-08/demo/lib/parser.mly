%{
open Utils
%}

%token INTTY
%token BOOLTY
%token COLON
%token EOF
%token FUN
%token ARROW
%token LPAREN
%token RPAREN
%token LET
%token REC
%token EQ
%token IN
%token <string> VAR
%token <int> NUM
%token IF
%token THEN
%token ELSE
%token PLUS

%left EQ
%left PLUS

%start <Utils.prog> prog

%%

prog:
  | ls = toplet+ EOF { ls }

ty:
  | INTTY { IntTy }
  | BOOLTY { BoolTy }
  | t1=ty; ARROW; t2=ty { FunTy(t1, t2) }

toplet:
  | LET; x=VAR; COLON; ty=ty; EQ; e=expr { TLet(x, ty, e) }
  | LET; REC; f=VAR; LPAREN; x=VAR; COLON; t1=ty; RPAREN;
    COLON; t2=ty; EQ; e=expr; { TLetRec(f, x, t1, t2, e) }
expr:
  | LET; x=VAR; COLON; ty=ty; EQ; e1=expr; IN; e2=expr { Let(x, ty, e1, e2) }
  | LET; REC; f=VAR; LPAREN; x=VAR; COLON; t1=ty; RPAREN;
    COLON; t2=ty; EQ; e1=expr; IN; e2=expr { LetRec(f, x, t1, t2, e1, e2) }
  | IF; e1=expr; THEN; e2=expr; ELSE; e3=expr { If (e1, e2, e3) }
  | FUN; LPAREN; x=VAR; COLON; ty=ty; RPAREN; ARROW; e=expr { Fun(x, ty, e) }
  | e = expr2 { e }

expr2:
  | e1 = expr2; PLUS; e2 = expr2 { Add (e1, e2) }
  | e1 = expr2; EQ; e2 = expr2 { Eq (e1, e2) }
  | e = expr3; es = expr3*
    { List.fold_left (fun e1 e2 -> App (e1, e2)) e es }

expr3:
  | x = VAR { Var x }
  | n = NUM { Num n }
  | LPAREN; e=expr; RPAREN { e }
