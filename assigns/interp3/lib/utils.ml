type ident = string

module VarSet = Set.Make(String)

type ty =
  | TUnit | TInt | TFloat | TBool
  | TVar of ident
  | TList of ty
  | TOption of ty
  | TPair of ty * ty
  | TFun of ty * ty

type ty_scheme =
  | Forall of VarSet.t * ty

type bop =
  | Add | Sub | Mul | Div | Mod
  | AddF | SubF | MulF | DivF | PowF
  | Lt | Lte | Gt | Gte | Eq | Neq
  | And | Or
  | Comma | Cons

type expr =
  | Unit | Bool of bool | Nil | ENone
  | Int of int | Float of float
  | Var of ident
  | Assert of expr
  | ESome of expr
  | Bop of bop * expr * expr
  | If of expr * expr * expr
  | ListMatch of
    { matched : expr
    ; hd_name : ident
    ; tl_name : ident
    ; cons_case : expr
    ; nil_case : expr
    }
  | OptMatch of
    { matched : expr
    ; some_name : ident
    ; some_case : expr
    ; none_case : expr
    }
  | PairMatch of
    { matched : expr
    ; fst_name : ident
    ; snd_name : ident
    ; case : expr
    }
  | Fun of ident * ty option * expr
  | App of expr * expr
  | Annot of expr * ty
  | Let of
    { is_rec : bool
    ; name : ident
    ; binding : expr
    ; body : expr
    }

type toplet =
  { is_rec : bool
  ; name : ident
  ; binding : expr
  }

type prog = toplet list

type constr = ty * ty

module Env = Map.Make(String)
type stc_env = ty_scheme Env.t
type dyn_env = value Env.t

and value =
  | VUnit
  | VBool of bool
  | VInt of int
  | VFloat of float
  | VList of value list
  | VPair of value * value
  | VNone
  | VSome of value
  | VClos of
    { name : string option
    ; arg : string
    ; body : expr
    ; env : dyn_env
    }

type error =
  | ParseError
  | TypeError

let err_msg = function
  | ParseError -> "parse error"
  | TypeError -> "type error"

let mk_gensym () =
  let count = ref 0 in
  let counter () =
    count := !count + 1;
    "$" ^ string_of_int !count
  in counter

let gensym = mk_gensym ()
