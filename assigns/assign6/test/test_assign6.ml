open Assign6
open OUnit2

module ExprExamples = struct
  let a e1 e2 = Add (e1, e2)
  let n m = Num m
  let i e1 e2 e3 = If (e1, e2, e3)
  let l e1 e2 = Lt (e1, e2)
end

let test_parse =
  let open ExprExamples in
  "basic parse test" >:::
    [
      "empty" >:: (fun _ -> assert_equal None (parse ""));
      "(+ 1 2)" >:: (fun _ ->
        assert_equal
          (Some (a (n 1) (n 2)))
          (parse "(+ 1 2)"));
      "(? (< 4 (+ 1 5)) (+ 1 -1) -2)" >:: (fun _ ->
        assert_equal
          (Some (i (l (n 4) (a (n 1) (n 5))) (a (n 1) (n (-1))) (n (-2))))
          (parse "(? (< 4 (+ 1 5)) (+ 1 -1) -2)"));
      "(? (? 0 0 0) 0 (< 0 0))" >:: (fun _ ->
        assert_equal
          (Some (i (i (n 0) (n 0) (n 0)) (n 0) (l (n 0) (n 0))))
          (parse "(? (? 0 0 0) 0 (< 0 0))"));
      "(? (? 0 0 0) 0)" >:: (fun _ ->
        assert_equal
          None
          (parse "(? (? 0 0 0) 0)"));
    ]

let test_type_of =
  "basic type_of_tests" >:::
    [
      "(+ 1 2)" >:: (fun _ ->
        assert_equal
          (Some TInt)
          (Option.bind (parse "(+ 1 2)") type_of));
      "(< 1 2)" >:: (fun _ ->
        assert_equal
          (Some TBool)
          (Option.bind (parse "(< 1 2)") type_of));
      "(? (< 4 (+ 1 5)) (+ 1 -1) -2)" >:: (fun _ ->
        assert_equal
          (Some TInt)
          (Option.bind (parse "(? (< 4 (+ 1 5)) (+ 1 -1) -2)") type_of));
      "(? (? 0 0 0) 0 (< 0 0))" >:: (fun _ ->
        assert_equal
          None
          (Option.bind (parse "(? (? 0 0 0) 0 (< 0 0))") type_of));
      "(? (< 0 0) (< 0 0) (< 0 0))" >:: (fun _ ->
        assert_equal
          (Some TBool)
          (Option.bind (parse "(? (< 0 0) (< 0 0) (< 0 0))") type_of));
    ]

let test_eval =
  "basic eval tests" >:::
    [
      "(+ 1 2)" >:: (fun _ ->
        assert_equal
          (Some (VNum 3))
          (Option.map eval (parse "(+ 1 2)")));
      "(< 1 2)" >:: (fun _ ->
        assert_equal
          (Some (VBool true))
          (Option.map eval (parse "(< 1 2)")));
      "(? (< 4 (+ 1 5)) (+ 1 -1) -2)" >:: (fun _ ->
        assert_equal
          (Some (VNum 0))
          (Option.map eval (parse "(? (< 4 (+ 1 5)) (+ 1 -1) -2)")));
      "(+ 1 (+ 2 (+ 3 (+ 4 5))))" >:: (fun _ ->
        assert_equal
          (Some (VNum 15))
          (Option.map eval (parse "(+ 1 (+ 2 (+ 3 (+ 4 5))))")));
      "15500" >:: (fun _ ->
        assert_equal
          (Some (VNum 15500))
          (Option.map eval (parse "15500")));
    ]

let tests =
  "Assignment 6 test suite" >:::
    [
      test_parse;
      test_type_of;
      test_eval
    ]

let _ = run_test_tt_main tests
