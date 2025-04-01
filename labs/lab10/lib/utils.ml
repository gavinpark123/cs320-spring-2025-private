type expr =
  | Num of int
  | Var of string

type stmt =
  | Assign of string * expr
  | FunDef of string * stmt list
  | FunCall of string

type prog = stmt list

type value =
  | VNum of int
  | VProg of prog

module Env = Map.Make(String)
type env = value Env.t

let string_of_expr e =
  match e with
  | Num n -> string_of_int n
  | Var x -> "$" ^ x

let rec string_of_stmt s =
  match s with
  | Assign (x, e) -> x ^ "=" ^ string_of_expr e
  | FunDef (f, p) -> f ^ "(){" ^ string_of_prog p ^ "}"
  | FunCall f -> f

and string_of_prog p =
  if List.is_empty p
  then "ϵ"
  else String.concat "" (List.map (fun s -> string_of_stmt s ^ ";") p)

let string_of_value v =
  match v with
  | VNum n -> string_of_int n
  | VProg p -> "\"" ^ string_of_prog p ^ "\""

let string_of_env env =
  let s =
    String.concat " , "
      (List.map
         (fun (x, v) -> x ^ " ↦ " ^ string_of_value v)
         (Env.to_list env))
  in "{" ^ s ^ "}"

let string_of_config (env, p) =
  "⟨ " ^ string_of_env env ^ " , " ^ string_of_prog p ^ " ⟩"
