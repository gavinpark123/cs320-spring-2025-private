
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

let parse str =
  let rec go toks =
    match toks with
    | TNum n :: toks -> Some (Num n, toks)
    | LParen :: TAdd :: toks -> (
      match go' toks with
      | Some ([e1; e2], RParen :: toks) -> Some (Add (e1, e2), toks)
      | _ -> None
    )
    | LParen :: TLt :: toks -> (
      match go' toks with
      | Some ([e1; e2], RParen :: toks) -> Some (Lt (e1, e2), toks)
      | _ -> None
    )
    | LParen :: TIf :: toks -> (
      match go' toks with
      | Some ([e1; e2; e3], RParen :: toks) -> Some (If (e1, e2, e3), toks)
      | _ -> None
    )
    | _ -> None
  and go' toks =
    match go toks with
    | Some (n, toks) -> (
       match go' toks with
       | Some (ns, toks) -> Some (n :: ns, toks)
       | _ -> Some ([n], toks)
    )
    | None -> Some ([], toks)
  in
  match lex str with
  | None -> None
  | Some toks ->
    match go toks with
    | Some (t, []) -> Some t
    | _ -> None

type ty =
  | TInt
  | TBool

let rec type_of e =
  match e with
  | Num _ -> Some TInt
  | Add (e1, e2) -> (
    match type_of e1 with
    | Some TInt -> (
      match type_of e2 with
      | Some TInt -> Some TInt
      | _ -> None
    )
    | _ -> None
  )
  | Lt (e1, e2) -> (
    match type_of e1 with
    | Some TInt -> (
      match type_of e2 with
      | Some TInt -> Some TBool
      | _ -> None
    )
    | _ -> None
  )
  | If (e1, e2, e3) -> (
    match type_of e1 with
    | Some TBool -> (
      match type_of e2 with
      | Some t1 -> (
        match type_of e3 with
        | Some t2 ->
           if t1 = t2
           then Some t1
           else None
        | _ -> None
      )
      | _ -> None
    )
    | _ -> None
  )

type value =
  | VNum of int
  | VBool of bool

let rec eval e =
  match e with
  | Num n -> VNum n
  | Add (e1, e2) -> (
     match eval e1, eval e2 with
     | VNum m, VNum n -> VNum (m + n)
     | _ -> assert false
  )
  | Lt (e1, e2) -> (
    match eval e1, eval e2 with
    | VNum m, VNum n -> VBool (m < n)
    | _ -> assert false
  )
  | If (e1, e2, e3) -> (
    match eval e1 with
    | VBool true -> eval e2
    | VBool false -> eval e3
    | _ -> assert false
  )
