open Nbe

let eval_norm source =
  source
  |> Parser.parse_string
  |> run_program StrMap.empty
  |> read_back StrSet.empty
  |> string_of_expr

let parse_and_check source ctx = 
  source
  |> Parser.parse_string
  |> check_program ctx

let%test_module "parsing" = (module struct
  let%test "unit" = 
    0 = compare 
      (eval_norm "();")
      "()"

  let to_church n =
    let rec go n =
      if n = 0 then
        "church_0"
      else
        "church_inc (" ^ (go (n - 1)) ^ ")"
    in "(" ^ (go n) ^ ")"

  let church_globals = 
    {| 
      global church_0 = \f.\x.x;
      global church_inc = \prev.\f.\x. f (prev f x);
      global church_add = \j.\k.\f.\x. j f (k f x);
    |}

  let%test "church numericals" = 
    let lhs = (eval_norm (Printf.sprintf "%s %s;" church_globals (to_church 3)))
    in
    0 = compare lhs {|(\f.(\x.(f (f (f x)))))|}

  let%test "church numericals" = 
    let lhs = (eval_norm (Printf.sprintf "%s church_add %s %s;" church_globals (to_church 3) (to_church 2)))
    in
    (*print_endline lhs;*)
    0 = compare lhs {|(\f.(\x.(f (f (f (f (f x)))))))|}

end)

let%test_module "type checking" = (module struct
  let%test "summing type check" =
    let expected_env = 
      [
        "three", Int;
        "four", Int;
        "seven", Int;
        "fake_sum", Arrow(Int, Arrow(Int, Int));
      ] |> List.to_seq |> StrMap.of_seq
    in
    match parse_and_check {| 
      global three = 3;
      global four = 4;
      global fake_sum = the (Int -> Int -> Int) \x.\y.x;
      global seven = fake_sum three four;
    |}
    StrMap.empty
    with
    | Ok(env) ->
        0 == StrMap.compare compare env expected_env
    | _ -> false

end)
