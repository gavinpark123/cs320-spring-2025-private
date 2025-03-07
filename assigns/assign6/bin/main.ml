
let read_file filename =
  let chan = open_in filename in
  let rec go acc =
    match input_line chan with
    | exception End_of_file -> acc
    | line -> go (acc ^ "\n" ^ line)
  in go ""

let () =
  let ( let* ) = Option.bind in
  let _ =
    let* input =
      (* check that an argument is given on the command line *)
      if Array.length Sys.argv > 1
      then
        let filename = Sys.argv.(1) in
        match read_file filename with
        | exception _ ->
           let _ = print_endline ("error: could not read \'" ^ filename ^ "\'") in
           None
        | s -> Some s
      else (
        let _ = print_endline "error: no file given" in
        None
      )
    in
    (* run the parser *)
    let _ = print_endline "parsing..." in
    let* expr = Assign6.parse input in
    (* run the type checker *)
    let _ = print_endline "type checking..." in
    let* _ = Assign6.type_of expr in
    (* run the evaluator *)
    let _ = print_endline "evaluating..." in
    let v = Assign6.eval expr in
    let _ = print_endline "DONE." in
    let _ =
      (* print the value *)
      match v with
        | VNum n -> print_endline (string_of_int n)
        | VBool b -> print_endline (string_of_bool b)
    in Some v
  in ()
