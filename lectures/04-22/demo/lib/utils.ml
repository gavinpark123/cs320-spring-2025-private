
type ty =
  | TInt
  | TBool
  | TFun of ty * ty
  | TVar of string

module VarSet = Set.Make(String)

type ty_scheme = Forall of VarSet.t * ty

let string_of_ty_scheme (Forall (bvs, ty)) =
  let rec go = function
    | TInt -> "int"
    | TBool -> "bool"
    | TVar a -> "\'" ^ a
    | TFun (t1, t2) -> go_paren t1 ^ " -> " ^ go t2
  and go_paren = function
    | TFun (t1, t2) -> "(" ^ go (TFun (t1, t2)) ^ ")"
    | ty -> go ty
  in
  let bnd_vars = String.concat " " (List.map ((^) "\'") (VarSet.to_list bvs)) in
  bnd_vars ^ " . " ^ go ty

type constr = ty * ty
type solution = (string * ty) list

type expr =
  | Var of string
  | Num of int
  | Fun of string * expr
  | Add of expr * expr
  | Eq of expr * expr
  | If of expr * expr * expr
  | App of expr * expr
  | Let of string * expr * expr
  | LetRec of string * string * expr * expr

type prog = expr

module Env = Map.Make(String)

type env = value Env.t
and value =
  | VBool of bool
  | VNum of int
  | VClos of string * expr * env * string option
