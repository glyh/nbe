open Nbe

let rec user_input prompt callback =
  match LNoise.linenoise prompt with
  | None -> ()
  | Some v ->
    callback v;
    user_input prompt callback

let all_pipeline source =
  let parsed = 
    source
    |> Parser.parse_string
  in
  let ret = run_program StrMap.empty parsed in
  let ret_reflected = reflect StrSet.empty ret in
  let ret_str = string_of_expr ret_reflected in
  Printf.printf "Final result: %s\n%!" ret_str

let main () = 
  Parser.pp_exceptions ();
  all_pipeline |> user_input "NBE> "
