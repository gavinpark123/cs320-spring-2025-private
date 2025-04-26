%{
open Utils

let mk_func ty args body =
  let body =
    match ty with
    | None   -> body
    | Some t -> Annot (body, t)
  in
  List.fold_right
    (fun (x, ty) acc -> Fun (x, ty, acc))
    args
    body

let mk_list h es =
  let tl =
    List.fold_right
      (fun x acc -> Bop (Cons, x, acc))
      es
      Nil
  in
  Bop (Cons, h, tl)
%}

(* Tokens *)
%token EOF
%token <int>    INT
%token <float>  FLOAT
%token <string> VAR
%token <string> TVAR

%token LET REC EQ IN COLON
%token FUN IF THEN ELSE
%token MATCH WITH ALT
%token TRUE FALSE NONE SOME ASSERT

%token LPAREN RPAREN LBRACKET RBRACKET SEMICOLON
%token TUNIT TINT TFLOAT TBOOL TLIST TOPTION ARROW

%token ADD SUB STAR DIV MOD
%token ADDF SUBF MULF DIVF POW CONS
%token LT LTE GT GTE NEQ AND OR COMMA

(* Precedences *)
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

%inline bop

%start <Utils.prog> prog

%%

prog:
  | ls = toplet* EOF
      { ls }

and toplet:
  | LET rc = REC?; name = VAR; args = arg*; ty = annot?; EQ; binding = expr
      { { is_rec  = Option.is_some rc
        ; name    = name
        ; binding = mk_func ty args binding
        }
      }

and annot:
  | COLON; ty = ty
      { ty }

and ty:
  | TUNIT                      { TUnit }
  | TINT                       { TInt }
  | TFLOAT                     { TFloat }
  | TBOOL                      { TBool }
  | TLIST                      { TList }
  | TOPTION                    { TOption }
  | TVAR                       { TParam tvar }
  | LPAREN; ty = ty; RPAREN    { ty }
  | ty1 = ty; ARROW; ty2 = ty  { TFun (ty1, ty2) }

and arg:
  | x = VAR
      { (x, None) }
  | LPAREN; x = VAR; ty = annot; RPAREN
      { (x, Some ty) }

and expr:
  | LET rc = REC?; name = VAR; args = arg*; ty = annot?; EQ; binding = expr; IN; body = expr
      { Let
          { is_rec  = Option.is_some rc
          ; name    = name
          ; binding = mk_func ty args binding
          ; body    = body
          }
      }
  | IF; c = expr; THEN; t = expr; ELSE; e = expr
      { If (c, t, e) }
  | MATCH; e = expr; WITH; cases = case+
      { Match (e, cases) }
  | FUN; args = arg*; ARROW; body = expr
      { mk_func None args body }
  | e = expr2
      { e }

and case:
  | ALT; p = pattern; ARROW; e = expr
      { (p, e) }

and expr2:
  | e1 = expr2; op = bop; e2 = expr2
      { Bop (op, e1, e2) }
  | ASSERT; e = expr3
      { Assert e }
  | SOME; e = expr3
      { ESome e }
  | es = expr3+
      { List.(fold_left (fun acc x -> App (acc, x)) (hd es) (tl es)) }

and expr3:
  | LPAREN; RPAREN
      { Unit }
  | TRUE
      { Bool true }
  | FALSE
      { Bool false }
  | NONE
      { ENone }
  | LBRACKET; RBRACKET
      { Nil }
  | LBRACKET; e = expr; es = list_item*; RBRACKET
      { mk_list e es }
  | n = INT
      { Int n }
  | n = FLOAT
      { Float n }
  | x = VAR
      { Var x }

and list_item:
  | SEMICOLON; e = expr
      { e }

and pattern:
  | p1 = pattern; CONS; p2 = pattern
      { PCons (p1, p2) }
  | atom = pattern_atom
      { atom }

and pattern_atom:
  | LPAREN; p = pattern; RPAREN
      { p }
  | n = INT
      { PInt n }
  | n = FLOAT
      { PFloat n }
  | x = VAR
      { PVar x }
  | TRUE
      { PBool true }
  | FALSE
      { PBool false }
  | NONE
      { PNone }
  | SOME; p = pattern_atom
      { PSome p }
  | LBRACKET; RBRACKET
      { PNil }

and bop:
  | ADD   { Add   }
  | SUB   { Sub   }
  | STAR  { Mul   }
  | DIV   { Div   }
  | MOD   { Mod   }
  | ADDF  { AddF  }
  | SUBF  { SubF  }
  | MULF  { MulF  }
  | DIVF  { DivF  }
  | POW   { PowF  }
  | CONS  { Cons  }
  | LT    { Lt    }
  | LTE   { Lte   }
  | GT    { Gt    }
  | GTE   { Gte   }
  | EQ    { Eq    }
  | NEQ   { Neq   }
  | AND   { And   }
  | OR    { Or    }
  | COMMA { Comma }
