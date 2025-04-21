type op = Add | Sub | Mul | Div | Pow

type 'a expr =
  {
    expr : 'a _expr;
    meta : 'a
  }
and 'a _expr =
  | Num of int
  | Op of op * 'a expr * 'a expr

type error_kind =
  | DivByZero
  | NegExp

type 'a error =
  {
    error: error_kind;
    meta : 'a;
  }

let int_pow x y =
  let rec go acc y =
    if y = 0
    then acc
    else go (acc * x) (y - 1)
  in go 1 y

let op_fun op =
  match op with
  | Add -> (+)
  | Sub -> (-)
  | Mul -> ( * )
  | Div -> (/)
  | Pow -> int_pow

let guard b error = if b then Error error else Ok ()

let rec eval (e : 'a expr) : (int, 'a error) result =
  let ( let* ) = Result.bind in
  match e.expr with
  | Num n -> Ok n
  | Op (op, e1, e2) ->
     let* v1 = eval e1 in
     let* v2 = eval e2 in
     let* _ = match op with
       | Div -> guard (v2 = 0) {error=DivByZero; meta=e.meta}
       | Pow -> guard (v2 < 0) {error=NegExp; meta=e.meta}
       | _ -> Ok ()
     in
     Ok (op_fun op v1 v2)

exception ListTooShort
exception InvalidArg

let prefix k =
  let rec go acc k l =
    if k = 0
    then List.rev acc
    else
      match l with
      | [] -> raise ListTooShort
      | x :: l -> go (x :: acc) (k - 1) l
  in
  if k < 0
  then raise InvalidArg
  else go [] k

type prefix_error =
  | ListTooShort
  | InvalidArg

let prefix_res k l =
  match prefix k l with
  | l -> Ok l
  | exception ListTooShort -> Error ListTooShort
  | exception InvalidArg -> Error InvalidArg

module type DEQUEUE = sig
  type 'a t
  val empty: 'a t
  val push_front : 'a -> 'a t -> 'a t
  val pop_front : 'a t -> ('a * 'a t) option
  val push_back : 'a -> 'a t -> 'a t
  val pop_back : 'a t -> ('a * 'a t) option
  val to_list : 'a t -> 'a list
end

module ListDequeue = struct
  type 'a t = 'a list

  let empty = []

  let push_front x l = x :: l
  let pop_front l =
    match l with
    | [] -> None
    | x :: xs -> Some (x, xs)

  let push_back x l = l @ [x]
  let rec pop_back l =
    match l with
    | [] -> None
    | [x] -> Some (x, [])
    | x :: l ->
       Option.map
         (fun (y, l) -> y, x :: l)
         (pop_back l)

  let to_list l = l
end

let flip (a, b) = (b, a)

module DoubleListDequeue = struct
  type 'a t = 'a list * 'a list

  let empty = [], []

  let push_front x (front, back) = (x :: front, back)

  let balance l =
    let rec go k acc l =
      match k, l with
      | 0, _ -> (List.rev acc, List.rev l)
      | k, x :: l -> go (k - 1) (x :: acc) l
      | _ -> assert false (* impossible *)
    in go (List.length l / 2) [] l

  let rec pop_front (front, back) =
    match front with
    | x :: xs -> Some (x, (xs, back))
    | [] -> (
      match back with
      | [] -> None
      | _ -> pop_front (flip (balance back))
    )

  let push_back x (front, back) = (front, x :: back)
  let rec pop_back (front, back) =
    match back with
    | x :: xs -> Some (x, (front, xs))
    | [] -> (
      match front with
      | [] -> None
      | _ -> pop_back (balance front)
    )

  let to_list (front, back) = front @ List.rev back
end

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)
module StringSet = Set.Make(String)

let flip_keys_and_values (m : int StringMap.t) : StringSet.t IntMap.t  =
  let add_elem x s =
    match s with
    | None -> Some (StringSet.singleton x)
    | Some s -> Some (StringSet.add x s)
  in
  StringMap.fold
    (fun k v acc -> IntMap.update v (add_elem k) acc)
    m
    IntMap.empty
