
type token =
  | Lparen
  | Rparen
  | Atom of string

let is_space = function
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

let tokenize s =
  let rec go out i =
    if i >= String.length s
    then List.rev out
    else if is_space s.[i]
    then go out (i + 1)
    else if s.[i] = '('
    then go (Lparen :: out) (i + 1)
    else if s.[i] = ')'
    then go (Rparen :: out) (i + 1)
    else go' out i (i + 1)
  and go' out i j =
    if j >= String.length s
       || is_space s.[j]
       || s.[j] = '('
       || s.[j] = ')'
    then go (Atom (String.sub s i (j - i)) :: out) j
    else go' out i (j + 1)
  in go [] 0

let ntree_of_toks toks =
  let rec go toks =
    match toks with
    | Atom s :: toks -> Some (Node (s, []), toks)
    | Lparen :: toks -> (
      match go' toks with
      | Some (Node (s, []) :: ns, Rparen :: toks) -> Some (Node (s, ns), toks)
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
  match go toks with
  | Some (t, []) -> Some t
  | _ -> None

let parse s = s |> tokenize |> ntree_of_toks

let sexpr_of_ntree =
  let rec go i t =
    let indent = String.init i (fun _ -> ' ') in
    match t with
    | Node (v, []) -> indent ^ v
    | Node (v, ts) ->
       indent ^ "(" ^ v ^ "\n"
       ^ String.concat "\n" (List.map (go (i + 1)) ts) ^ ")"
  in go 0
