
type tok =
  | LParen
  | RParen
  | TNum of int
  | TAdd
  | TLt
  | TIf

let is_space = function
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

let is_keyword = function
  | '(' | ')' | '+' | '?' | '<' -> true
  | _ -> false

exception UnknownKeyword

let keyword_of_char = function
  | '(' -> LParen
  | ')' -> RParen
  | '+' -> TAdd
  | '<' -> TLt
  | '?' -> TIf
  | _ -> raise UnknownKeyword

let lex s =
  let rec go out i =
    if i >= String.length s
    then Some (List.rev out)
    else if is_space s.[i]
    then go out (i + 1)
    else if is_keyword s.[i]
    then go (keyword_of_char s.[i] :: out) (i + 1)
    else go' out i (i + 1)
  and go' out i j =
    if j >= String.length s
       || is_space s.[j]
       || is_keyword s.[j]
    then
      match int_of_string_opt (String.sub s i (j - i)) with
      | None -> None
      | Some n -> go ((TNum n) :: out) j
    else go' out i (j + 1)
  in go [] 0

type expr =
  | Num of int
  | Add of expr * expr
  | Lt of expr * expr
  | If of expr * expr * expr

let parse str = None (* TODO *)

type ty =
  | TInt
  | TBool

let type_of e = None (* TODO *)

type value =
  | VNum of int
  | VBool of bool

let eval e = VNum 0 (* TODO *)
