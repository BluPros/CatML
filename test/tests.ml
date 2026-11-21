open CatML
open Lang

(* Parse source text directly *)

let parse source =
  Parser.prog Lexer.read (Lexing.from_string source)

(* Report which test failed *)

let check name condition =
  if not condition then
    failwith ("Failed: " ^ name)

(* Check the exact AST produced by the parser *)

let check_parse name source expected =
  check name (parse source = expected)

(* Check evaluation separately from type checking *)

let check_eval name source expected =
  let result = multistep (parse source) in
  check name (is_val result && result = expected)

(* Check a concrete inferred type *)

let check_type name source expected =
  check name
    (type_of_expr (empty_context,parse source) = Some expected)

(* Check that an expression is rejected *)

let check_type_error name source =
  check name
    (type_of_expr (empty_context,parse source) = None)

(* Check that malformed source is rejected *)

let check_parse_error name source =
  let rejected =
    try
      ignore (parse source);
      false
    with
    | Parser.Error -> true
  in
  check name rejected

(* Check that unsupported characters are rejected *)

let check_lexer_error name source =
  let rejected =
    try
      ignore (parse source);
      false
    with
    | Failure _ -> true
  in
  check name rejected

let () =
  (* Parser tests *)
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

  (* Evaluator tests *)
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

  (* Type checker tests *)
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

  print_endline "All tests passed"