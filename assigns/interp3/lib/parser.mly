%{
open Utils

let mk_func ty args body =
  let body =
    match ty with
    | None -> body
    | Some ty -> Annot (body, ty)
  in
  List.fold_right
    (fun (x, ty) acc -> Fun (x, ty, acc))
    args
    body

let mk_list h es =
  let tl = List.fold_right
    (fun x acc -> Bop (Cons, x, acc))
    es
    Nil
  in Bop (Cons, h, tl)
%}

%token EOF
%token <int> INT
%token <float> FLOAT
%token <string> VAR

%token LET
%token REC
%token EQ
%token IN
%token COLON

%token FUN
%token MATCH
%token WITH
%token ALT
%token IF
%token THEN
%token ELSE

%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token SEMICOLON

%token TUNIT
%token TINT
%token TFLOAT
%token TBOOL
%token TLIST
%token TOPTION
%token <string> TVAR
%token ARROW

%token TRUE
%token FALSE

%token ADD
%token SUB
%token STAR
%token DIV
%token MOD
%token ADDF
%token SUBF
%token MULF
%token DIVF
%token POW
%token CONS
%token LT
%token LTE
%token GT
%token GTE
%token NEQ
%token AND
%token OR
%token COMMA

%token SOME
%token NONE
%token ASSERT

%nonassoc TLIST
%nonassoc TOPTION
%right ARROW
%nonassoc COMMA
%right OR
%right AND
%left LT LTE GT GTE EQ NEQ
%right CONS
%left ADD ADDF SUB SUBF
%left STAR MULF DIV DIVF MOD
%left POW

%start <Utils.prog> prog

%%

prog:
  | ls = toplet* EOF { ls }

toplet:
  | LET; rc=REC?; name=VAR; args=arg*; ty=annot?; EQ; binding=expr
    { {
	is_rec = Option.is_some rc;
	name;
	binding = mk_func ty args binding;
      }
    }

annot:
  | COLON; ty=ty { ty }

ty:
  | TUNIT { TUnit }

arg:
  | x=VAR { (x, None) }
  | LPAREN; x=VAR; ty=annot; RPAREN { (x, Some ty) }

expr:
  | LET; rc=REC?; name=VAR; args=arg*; ty=annot?; EQ; binding=expr; IN; body=expr
    { Let
	{
	  is_rec = (Option.is_some rc);
	  name;
	  binding= mk_func ty args binding;
	  body;
	}
    }
  | FUN; args=arg*; ARROW; body=expr { mk_func None args body }
  | e = expr2 { e }

%inline bop:
  | ADD { Add }
  | SUB { Sub }
  | STAR { Mul }
  | DIV { Div }
  | MOD { Mod }
  | ADDF { AddF }
  | SUBF { SubF }
  | MULF { MulF }
  | DIVF { DivF }
  | POW { PowF }
  | CONS { Cons }
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | EQ { Eq }
  | NEQ { Neq }
  | AND { And }
  | OR { Or }
  | COMMA { Comma }

expr2:
  | e1=expr2; op=bop; e2=expr2 { Bop (op, e1, e2) }
  | ASSERT; e=expr3 { Assert e }
  | SOME; e=expr3 { ESome e }
  | es=expr3+
    { List.(fold_left
	      (fun acc x -> App (acc, x))
	      (hd es)
	      (tl es))
    }

list_item:
  | SEMICOLON; e=expr { e }

expr3:
  | LPAREN; RPAREN { Unit }
  | TRUE { Bool true }
  | FALSE { Bool false }
  | NONE { ENone }
  | LBRACKET; RBRACKET { Nil }
  | LBRACKET; e=expr; es=list_item*; RBRACKET
    { mk_list e es }
  | n=INT { Int n }
  | n=FLOAT { Float n }
  | x=VAR { Var x }
