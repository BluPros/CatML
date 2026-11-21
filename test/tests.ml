open CatML
open Lang

(* remove source locations for structural comparisons *)

let rec strip_locations e =
  let strip = strip_locations in
  match e with
  | Located (_, e) -> strip e
  | Int _ | Bool _ | Var _ -> e
  | And (a, b) -> And (strip a, strip b)
  | Or (a, b) -> Or (strip a, strip b)
  | Not a -> Not (strip a)
  | Plus (a, b) -> Plus (strip a, strip b)
  | Mult (a, b) -> Mult (strip a, strip b)
  | Equal (a, b) -> Equal (strip a, strip b)
  | If (c, a, b) -> If (strip c, strip a, strip b)
  | Let (x, a, b) -> Let (x, strip a, strip b)
  | Pair (a, b) -> Pair (strip a, strip b)
  | First a -> First (strip a)
  | Second a -> Second (strip a)
  | Fun (x, body) -> Fun (x, strip body)
  | Fix (f, x, body) -> Fix (f, x, strip body)
  | App (a, b) -> App (strip a, strip b)

(* parse source text directly *)

let parse source =
  Parser.prog Lexer.read (Lexing.from_string source)

(* report which test failed *)

let check name condition =
  if not condition then
    failwith ("Failed: " ^ name)

(* compare parser results without source metadata *)

let check_parse name source expected =
  check name (strip_locations (parse source) = expected)

(* compare small-step results without source metadata *)

let check_eval name source expected =
  let result = multistep (parse source) in
  check name
    (is_val result && strip_locations result = expected)

(* check a concrete inferred type *)

let check_type name source expected =
  check name
    (type_of_expr (empty_context,parse source) = Some expected)

(* check that an expression is rejected *)

let check_type_error name source =
  check name
    (type_of_expr (empty_context,parse source) = None)

(* check that malformed source is rejected *)

let check_parse_error name source =
  let rejected =
    try
      ignore (parse source);
      false
    with
    | Parser.Error -> true
  in
  check name rejected

(* check that unsupported characters are rejected *)

let check_lexer_error name source =
  let rejected =
    try
      ignore (parse source);
      false
    with
    | Failure _ -> true
  in
  check name rejected

(* test the environment evaluator on integers and booleans *)
(* also supports pairs that contain only data values *)

let check_env_eval name source expected =
  check name (eval [] (parse source) = expected)

(* check the line and column of a reported type error *)

let check_type_error_location name source expected_line expected_column =
  let matches =
    try
      ignore (type_check (empty_context, parse source));
      false
    with
    | Located_type_error (loc, _) ->
        let pos = loc.start_pos in
        let column =
          pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1
        in
        pos.Lexing.pos_lnum = expected_line
        && column = expected_column
  in
  check name matches

let () =
  (* parser tests *)
  check_parse "multiplication precedence"
    "2 + 3 * 4"
    (Plus(Int 2,Mult(Int 3,Int 4)));

  check_parse "application groups left"
    "f x y"
    (App(App(Var "f",Var "x"),Var "y"));

  check_parse "pair syntax"
    "(1, True)"
    (Pair(Int 1,Bool true));

  check_parse "function body"
    "Fun x -> x + 1"
    (Fun("x",Plus(Var "x",Int 1)));

  check_parse_error "missing binding expression"
    "Let x = In x";

  check_lexer_error "unsupported character"
    "@";

  (* evaluator tests *)
  check_eval "arithmetic"
    "2 + 3 * 4"
    (Int 14);

  check_eval "pair projections"
    "Let p = (10, 5) In First p + Second p"
    (Int 15);

  check_eval "function application"
    "(Fun x -> x + 1) 10"
    (Int 11);

  check_eval "variable shadowing"
    "Let x = 10 In Let f = Fun x -> x + 1 In (f 5) + x"
    (Int 16);

  check_eval "lexical scope"
    "Let x = 10 In Let f = Fun y -> x + y In Let x = 100 In f 1"
    (Int 11);

  check_eval "returned function"
    "Let makeAdder = Fun x -> Fun y -> x + y In
     Let addFive = makeAdder 5 In addFive 3"
    (Int 8);

  check_eval "recursive factorial"
    "Let factorial = Fix f . n ->
       If n = 0 Then 1 Else n * (f (n + -1))
     In factorial 5"
    (Int 120);

  check_eval "unused branch is not evaluated"
    "If True Then 7 Else (Fix loop . x -> loop x) 0"
    (Int 7);

  (* type checker tests *)
  check_type "pair type"
    "(1, True)"
    (PAIR(INT,BOOL));

  check_type "function type"
    "Fun x -> x + 1"
    (ARROW(INT,INT));

  check_type_error "projection requires a pair"
    "First 10";

  check_type_error "wrong argument type"
    "(Fun x -> x + 1) True";

  check_type_error "branches disagree"
    "If True Then 1 Else False";

  check_type_error "unbound variable"
    "missingName";

  check_type_error "infinite type"
    "Fun x -> x x";

  (* environment evaluator tests *)
  check_env_eval "environment pair"
    "Let p = (10, 5) In First p + Second p"
    (VInt 15);

  check_env_eval "environment lexical scope"
    "Let x = 10 In Let f = Fun y -> x + y In
     Let x = 100 In f 1"
    (VInt 11);

  check_env_eval "environment returned function"
    "Let makeAdder = Fun x -> Fun y -> x + y In
     Let addFive = makeAdder 5 In addFive 3"
    (VInt 8);

  check_env_eval "environment recursion"
    "Let factorial = Fix f . n ->
       If n = 0 Then 1 Else n * (f (n + -1))
     In factorial 5"
    (VInt 120);

  (* detailed type-error location tests *)
  check_type_error_location "wrong arithmetic operand"
    "1 + True"
    1 5;

  check_type_error_location "multiline operand"
    "Let x = 1 In\nx + True"
    2 5;

  check_type_error_location "unbound variable location"
    "1 + missing"
    1 5;

  check_type_error_location "wrong function argument"
    "(Fun x -> x + 1) True"
    1 18;

  check_type_error_location "wrong projection operand"
    "First 10"
    1 7;

  print_endline "All tests passed"