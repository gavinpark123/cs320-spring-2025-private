type ty =
  | IntTy
  | BoolTy
  | FunTy of ty * ty

type expr =
  | Var of string
  | Num of int
  | Fun of string * ty * expr
  | Add of expr * expr
  | Eq of expr * expr
  | If of expr * expr * expr
  | App of expr * expr
  | Let of string * ty * expr * expr
  | LetRec of string * string * ty * ty * expr * expr

type toplet =
  | TLet of string * ty * expr
  | TLetRec of string * string * ty * ty * expr

type prog = toplet list

module Env = Map.Make(String)

type env = value Env.t
and value =
  | VBool of bool
  | VNum of int
  | VClos of string * expr * env * string option
