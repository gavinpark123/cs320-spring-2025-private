open Interp1
open OUnit2

let parse_tests =
  "testing parse" >:::
    [
      "basic arithmetic expr" >:: (fun _ ->
        let expected = Some (Bop (Mul, Bop (Add, Num 1, Num 2), Num 3)) in
        let actual = parse "(1 + 2) * 3" in
        assert_equal expected actual);
      (* TODO: write more tests *)
    ]

let subst_tests =
  "testing subst" >:::
    [
      "single variable" >:: (fun _ ->
        let expected = Bop (Add, Var "x", If (Unit, Unit, Unit)) in
        let actual = subst VUnit "y" (Bop (Add, Var "x", If(Var "y", Var "y", Var "y"))) in
        assert_equal expected actual);
      (* TODO: write more tests *)
    ]

let eval_tests =
  "testing eval" >:::
    [
      "application" >:: (fun _ ->
        let expected = Ok (VNum 4) in
        let actual = eval (App (Fun ("x", Bop (Add, Var "x", Num 1)), Num 3)) in
        assert_equal expected actual);
      (* TODO: write more tests *)
    ]

let interp_tests =
  "interp tests" >:::
    [
      "variable" >:: (fun _ ->
        let expected = Ok (VBool true) in
        let actual = interp "let x = true || false in x && true" in
        assert_equal expected actual);
      (* TODO: write more tests *)
    ]

let tests =
  "interp1 test suite" >:::
    [
      parse_tests;
      subst_tests;
      eval_tests;
      interp_tests;
    ]

let _ = run_test_tt_main tests
