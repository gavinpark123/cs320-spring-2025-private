type expr =
  | Var of string
  | Num of int
  | Fun of string * expr
  | Add of expr * expr
  | Eq of expr * expr
  | If of expr * expr * expr
  | App of expr * expr
  | Let of string * expr * expr
    (* let rec f x = e1 in e2 *)
  | LetRec of string * string * expr * expr

type prog = expr

module Env = Map.Make(String)
(* Env.empty, Env.find_opt, Env.add *)

type env = value Env.t (* Bindings from strings to values *)
and value =
  | VBool of bool
  | VNum of int
  (* | VFun of string * expr *)
  | VClos of string * expr * env * string option




