%{
open Utils

type expr_or_type =
  | Expr of expr
  | Type of ty
%}

%token INTTY
%token BOOLTY
%token COLON
%token PERIOD
%token FUN
%token ARROW
%token LPAREN
%token RPAREN
%token LET
%token REC
%token EQ
%token IN
%token <string> VAR
%token <string> TYVAR
%token <int> NUM
%token IF
%token THEN
%token ELSE
%token PLUS
%token EOF

%left EQ
%left PLUS
%right PERIOD
%right ARROW

%start <Utils.prog> prog

%%

prog:
  | ls = toplet+ EOF { ls }

ty:
  | INTTY { IntTy }
  | BOOLTY { BoolTy }
  | s=TYVAR { TyVar s }
  | s=TYVAR; PERIOD; ty=ty { Forall(s, ty) }
  | t1=ty; ARROW; t2=ty { FunTy(t1, t2) }
  | LPAREN; ty=ty; RPAREN { ty }

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
  | FUN; x=TYVAR; ARROW; e=expr { TyFun(x, e) }
  | e = expr2 { e }

expr3_or_type:
  | e=expr3 { Expr e }
  | ty=ty { Type ty }

expr2:
  | e1=expr2; PLUS; e2=expr2 { Add (e1, e2) }
  | e1=expr2; EQ; e2=expr2 { Eq (e1, e2) }
  | e=expr3; es=expr3_or_type* {
      let combine e = function
        | Expr e' -> App(e, e')
        | Type ty -> TyApp(e, ty)
      in List.fold_left combine e es
    }

expr3:
  | x=VAR { Var x }
  | n=NUM { Num n }
  | LPAREN; e=expr; RPAREN { e }
