open CatML
open Lang



(****************)
(*Test Helpers *)
(****************)



let passed = ref 0

(* report the name of a failed test *)

let check name condition =
  if condition then
    incr passed
  else
    failwith ("failed: " ^ name)

(* set a filename so location tests can check it *)

let make_lexbuf source =
  let lexbuf = Lexing.from_string source in
  let pos = {
    lexbuf.Lexing.lex_curr_p with
    Lexing.pos_fname = "extra_credit.catml";
  } in
  lexbuf.Lexing.lex_curr_p <- pos;
  lexbuf.Lexing.lex_start_p <- pos;
  lexbuf

let parse source =
  Parser.prog Lexer.read (make_lexbuf source)

(* check the environment evaluator after type checking *)
(* expected results should contain data rather than closures *)

let check_value name source expected =
  let ast = parse source in
  ignore (type_check (empty_context, ast));
  check name (eval [] ast = expected)

(* compare data results without comparing function closures *)

let rec same_result old_value new_value =
  match old_value, new_value with
  | Located (_, e), v -> same_result e v
  | Int a, VInt b -> a = b
  | Bool a, VBool b -> a = b
  | Pair (a, b), VPair (c, d) ->
      same_result a c && same_result b d
  | _ -> false

(* check that both evaluators agree on a terminating program *)

let check_agreement name source =
  let ast = parse source in
  ignore (type_check (empty_context, ast));
  let old_value = multistep ast in
  let new_value = eval [] ast in
  check name
    (is_val old_value && same_result old_value new_value)

(* compare a concrete inferred type *)

let check_type name source expected =
  check name
    (type_of_expr (empty_context, parse source) = Some expected)

(* check that invalid types are rejected *)

let check_type_error name source =
  check name
    (type_of_expr (empty_context, parse source) = None)

(* check that the same unknown type is used for input and output *)

let check_identity_type () =
  let tp = type_check (empty_context, parse "Fun x -> x") in
  let matches =
    match resolve tp with
    | ARROW (input, output) ->
        begin match resolve input, resolve output with
        | TVAR a, TVAR b -> a == b
        | _ -> false
        end
    | _ -> false
  in
  check "identity shares its input and output type" matches

(* convert a position to a one-based column *)

let column pos =
  pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1

(* check the complete span and a fragment of the error message *)
(* the end column is exclusive *)

let check_type_location name source line start_column end_column fragment =
  let matches =
    try
      ignore (type_check (empty_context, parse source));
      false
    with
    | Located_type_error (loc, message) ->
        let fragment_length = String.length fragment in

        let rec contains i =
          if i + fragment_length > String.length message then false
          else if String.sub message i fragment_length = fragment then true
          else contains (i + 1)
        in

        loc.start_pos.Lexing.pos_fname = "extra_credit.catml"
        && loc.start_pos.Lexing.pos_lnum = line
        && loc.end_pos.Lexing.pos_lnum = line
        && column loc.start_pos = start_column
        && column loc.end_pos = end_column
        && contains 0
  in
  check name matches

(* check where the parser detects invalid syntax *)

let check_syntax_location name source expected_line expected_column =
  let lexbuf = make_lexbuf source in
  let matches =
    try
      ignore (Parser.prog Lexer.read lexbuf);
      false
    with
    | Parser.Error ->
        let pos = lexbuf.Lexing.lex_start_p in
        pos.Lexing.pos_lnum = expected_line
        && column pos = expected_column
  in
  check name matches

(* check where the lexer rejects an unsupported character *)

let check_lexer_location name source expected_line expected_column =
  let lexbuf = make_lexbuf source in
  let matches =
    try
      ignore (Parser.prog Lexer.read lexbuf);
      false
    with
    | Failure _ ->
        let pos = lexbuf.Lexing.lex_start_p in
        pos.Lexing.pos_lnum = expected_line
        && column pos = expected_column
  in
  check name matches



(**********************)
(* Extra Credit Tests *)
(**********************)



let () =
  (* environment evaluation and lexical scope *)

  check_value "closure keeps its defining environment"
    "Let x = 10 In
     Let f = Fun y -> x + y In
     Let x = 100 In
     f 1"
    (VInt 11);

  check_value "parameter shadows an outer binding"
    "Let x = 10 In
     Let f = Fun x -> x + 1 In
     (f 5) + x"
    (VInt 16);

  check_value "returned closure keeps its captured value"
    "Let makeAdder = Fun x -> Fun y -> x + y In
     Let addFive = makeAdder 5 In
     addFive 3"
    (VInt 8);

  check_value "function stored inside a pair"
    "Let p = (Fun x -> x + 1, 9) In
     (First p) (Second p)"
    (VInt 10);

  check_value "recursive function stored inside a pair"
    "Let p = (Fix f . n ->
       If n = 0 Then 1 Else n * (f (n + -1)), 5)
     In (First p) (Second p)"
    (VInt 120);

  check_value "recursive closure captures an outer variable"
    "Let amount = 3 In
     Let sum = Fix f . n ->
       If n = 0 Then 0 Else amount + (f (n + -1))
     In
     Let amount = 100 In sum 4"
    (VInt 12);

  check_value "recursive parameter shadows the function name"
    "(Fix f . f -> f + 1) 4"
    (VInt 5);

  check_value "nested pair values"
    "(1, (True, 3))"
    (VPair (VInt 1, VPair (VBool true, VInt 3)));

  check_value "unused branch does not evaluate an infinite loop"
    "If True Then 7 Else (Fix loop . x -> loop x) 0"
    (VInt 7);

  (* agreement between the original and new evaluators *)

  check_agreement "evaluators agree on arithmetic"
    "(2 + 3) * 4";

  check_agreement "evaluators agree on booleans"
    "True And Not False Or False";

  check_agreement "evaluators agree on nested pairs"
    "Let p = ((1, 2), True) In
     (Second (First p), Second p)";

  check_agreement "evaluators agree on returned functions"
    "Let makeAdder = Fun x -> Fun y -> x + y In
     (makeAdder 5) 3";

  check_agreement "evaluators agree on recursion"
    "Let factorial = Fix f . n ->
       If n = 0 Then 1 Else n * (f (n + -1))
     In factorial 6";

  (* type inference *)

  check_identity_type ();

  check_type "infer integer function"
    "Fun x -> x + 1"
    (ARROW (INT, INT));

  check_type "infer boolean function"
    "Fun x -> Not x"
    (ARROW (BOOL, BOOL));

  check_type "infer pair parameter"
    "Fun p -> (First p) + (Second p)"
    (ARROW (PAIR (INT, INT), INT));

  check_type "infer higher-order function"
    "Fun f -> (f 1) + 2"
    (ARROW (ARROW (INT, INT), INT));

  check_type "infer recursive function"
    "Fix f . n ->
       If n = 0 Then 1 Else n * (f (n + -1))"
    (ARROW (INT, INT));

  check_type_error "reject infinite function type"
    "Fun x -> x x";

  check_type_error "reject inconsistent parameter uses"
    "Fun x -> (x + 1, Not x)";

  check_type_error "let bindings remain monomorphic"
    "Let identity = Fun x -> x In
     (identity 1, identity True)";

  (* exact type-error spans and useful messages *)

  check_type_location "arithmetic operand span"
    "1 + True"
    1 5 9
    "expected Int but found Bool";

  check_type_location "multiline operand span"
    "Let x = 1 In\nx + True"
    2 5 9
    "expected Int but found Bool";

  check_type_location "windows newline span"
    "Let x = 1 In\r\nx + True"
    2 5 9
    "expected Int but found Bool";

  check_type_location "unbound variable span and name"
    "1 + missing"
    1 5 12
    "unbound variable: missing";

  check_type_location "function argument span"
    "(Fun x -> x + 1) True"
    1 18 22
    "expected Int but found Bool";

  check_type_location "projection operand span"
    "First 10"
    1 7 9
    "but found Int";

  check_type_location "nested error keeps the inner location"
    "Let f = Fun x -> x + True In f 1"
    1 22 26
    "expected Int but found Bool";

  (* syntax and lexer error positions *)

  check_syntax_location "unexpected token position"
    "Let x = In x"
    1 9;

  check_syntax_location "unexpected end of file position"
    "Let x = 1 In"
    1 13;

  check_lexer_location "invalid character position"
    "@"
    1 1;

  check_lexer_location "multiline invalid character position"
    "1 +\n@"
    2 1;

  Printf.printf "All %d extra credit tests passed\n" !passed