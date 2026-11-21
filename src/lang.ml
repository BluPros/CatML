(*
   CatML Abstract Syntax
   ----------------------
*)



type var = string

type expr =
  (* boolean expression forms *)
  | Bool of bool
  | And of expr * expr
  | Or of expr * expr
  | Not of expr

  (* arithmetic expression forms *)
  | Int of int
  | Plus of expr * expr
  | Mult of expr * expr
  | Equal of expr * expr

  (* conditional expression form *)
  | If of expr * expr * expr

  (* Variables and let expressions *)
  | Var of var
  | Let of var * expr * expr

  (* Pairs and projections *)
  | Pair of expr * expr
  | First of expr
  | Second of expr

  (* Functions and recursive functions *)
  | Fun of var * expr
  | Fix of var * var * expr

  (* Function application *)
  | App of expr * expr

(*
  is_val : expr -> bool
  in : AST [[e]]
  out : true iff e is a value
*)
let rec is_val e =
  match e with
  | Int _ -> true
  | Bool _ -> true
  (* A pair is a value when both parts are values *)
  | Pair (e1, e2) -> is_val e1 && is_val e2
  (* Function bodies are evaluated only when called *)
  | Fun _ | Fix _ -> true
  | _ -> false



(*************************)
(* Operational Semantics *)
(*************************)



(* Define substitution *)
let rec subst (x, v, e) : expr =
  match e with
  | Var y -> if x = y then v else Var y
  | Let (y, e1, e2) ->
      Let (y, subst (x, v, e1), if x = y then e2 else subst (x, v, e2))
  | Bool _ | Int _ -> e
  | And (e1, e2) -> And (subst (x, v, e1), subst (x, v, e2))
  | Or (e1, e2) -> Or (subst (x, v, e1), subst (x, v, e2))
  | Not e' -> Not (subst (x, v, e'))
  | Plus (e1, e2) -> Plus (subst (x, v, e1), subst (x, v, e2))
  | Mult (e1, e2) -> Mult (subst (x, v, e1), subst (x, v, e2))
  | Equal (e1, e2) -> Equal (subst (x, v, e1), subst (x, v, e2))
  | If (e0, e1, e2) ->
      If (subst (x, v, e0), subst (x, v, e1), subst (x, v, e2))

  (* Substitute into both parts of a pair *)
  | Pair (e1, e2) -> Pair (subst (x, v, e1), subst (x, v, e2))
  | First e1 -> First (subst (x, v, e1))
  | Second e1 -> Second (subst (x, v, e1))

  (* Stop when the parameter shadows x *)
  | Fun (y, body) ->
      if x = y then e
      else Fun (y, subst (x, v, body))

  (* Both the function name and parameter bind variables *)
  | Fix (f, y, body) ->
      if x = f || x = y then e
      else Fix (f, y, subst (x, v, body))

  (* Substitute into the function and its argument *)
  | App (e1, e2) -> App (subst (x, v, e1), subst (x, v, e2))

type step_result = Step of expr | NotReducible

(*
   step : expr -> step_result
   in : An expression [[e]]
   out : An expression [[e']] if e -> e' in the operational semantics;
         if no such [[e']] exists, returns [[NotReducible]]
*)
let rec step (e : expr) : step_result =
  match e with
  | Bool _ | Int _ -> NotReducible

  | Not (Bool b) -> Step (Bool (not b))
  | Not e1 ->
      begin match step e1 with
      | Step e1' -> Step (Not e1')
      | NotReducible -> NotReducible
      end

  | And (Bool b1, Bool b2) -> Step (Bool (b1 && b2))
  | And (e1, e2) ->
      begin match step e1 with
      | Step e1' -> Step (And (e1', e2))
      | NotReducible ->
          begin match step e2 with
          | Step e2' -> Step (And (e1, e2'))
          | NotReducible -> NotReducible
          end
      end

  | Or (Bool b1, Bool b2) -> Step (Bool (b1 || b2))
  | Or (e1, e2) ->
      begin match step e1 with
      | Step e1' -> Step (Or (e1', e2))
      | NotReducible ->
          begin match step e2 with
          | Step e2' -> Step (Or (e1, e2'))
          | NotReducible -> NotReducible
          end
      end

  | Plus (Int n1, Int n2) -> Step (Int (n1 + n2))
  | Plus (e1, e2) ->
      begin match step e1 with
      | Step e1' -> Step (Plus (e1', e2))
      | NotReducible ->
          begin match step e2 with
          | Step e2' -> Step (Plus (e1, e2'))
          | NotReducible -> NotReducible
          end
      end

  | Mult (Int n1, Int n2) -> Step (Int (n1 * n2))
  | Mult (e1, e2) ->
      begin match step e1 with
      | Step e1' -> Step (Mult (e1', e2))
      | NotReducible ->
          begin match step e2 with
          | Step e2' -> Step (Mult (e1, e2'))
          | NotReducible -> NotReducible
          end
      end

  | Equal (Int n1, Int n2) -> Step (Bool (n1 = n2))
  | Equal (e1, e2) ->
      begin match step e1 with
      | Step e1' -> Step (Equal (e1', e2))
      | NotReducible ->
          begin match step e2 with
          | Step e2' -> Step (Equal (e1, e2'))
          | NotReducible -> NotReducible
          end
      end

  | If (Bool true, e1, _) -> Step e1
  | If (Bool false, _, e2) -> Step e2
  | If (e1, e2, e3) ->
      begin match step e1 with
      | Step e1' -> Step (If (e1', e2, e3))
      | NotReducible -> NotReducible
      end

  | Var _ -> NotReducible
  | Let (x, e1, e2) ->
      begin match step e1 with
      | Step e1' -> Step (Let (x, e1', e2))
      | NotReducible ->
          if is_val e1 then Step (subst (x, e1, e2))
          else NotReducible
      end

  (* Function bodies do not reduce until application *)
  | Fun _ | Fix _ -> NotReducible

  (* Reduce the left part before trying the right part *)
  | Pair (e1, e2) ->
      begin match step e1 with
      | Step e1' -> Step (Pair (e1', e2))
      | NotReducible ->
          begin match step e2 with
          | Step e2' -> Step (Pair (e1, e2'))
          | NotReducible -> NotReducible
          end
      end

  (* Select a component only when both parts are values *)
  | First (Pair (v1, v2)) when is_val v1 && is_val v2 ->
      Step v1
  | First e1 ->
      begin match step e1 with
      | Step e1' -> Step (First e1')
      | NotReducible -> NotReducible
      end

  | Second (Pair (v1, v2)) when is_val v1 && is_val v2 ->
      Step v2
  | Second e1 ->
      begin match step e1 with
      | Step e1' -> Step (Second e1')
      | NotReducible -> NotReducible
      end

  (* Replace the parameter with the argument value *)
  | App (Fun (x, body), v) when is_val v ->
      Step (subst (x, v, body))

  (* Replace the recursive name and then the parameter *)
  (* A matching parameter name shadows the recursive name *)
  | App ((Fix (f, x, body) as self), v) when is_val v ->
      let body' =
        if f = x then body
        else subst (f, self, body)
      in
      Step (subst (x, v, body'))

  (* Reduce the function before trying its argument *)
  | App (e1, e2) ->
      begin match step e1 with
      | Step e1' -> Step (App (e1', e2))
      | NotReducible ->
          begin match step e2 with
          | Step e2' -> Step (App (e1, e2'))
          | NotReducible -> NotReducible
          end
      end

(*
   multistep : expr -> expr
   in : AST [[e]]
   out : [[e']] such that e ->* e' -/-> in the operational semantics
*)
let rec multistep e =
  match step e with
  | Step e' -> multistep e'
  | NotReducible -> e



(********************************)
(* Environment-based evaluation *)
(********************************)



(* Runtime values store results rather than expressions *)
(* Closures share their function body with the original AST *)

type value =
  | VInt of int
  | VBool of bool
  | VPair of value * value
  | VClosure of var * expr * environment
  | VRecClosure of var * var * expr * environment

and environment = (var * value) list

(* Report invalid runtime operations *)

exception Eval_error of string

(* Find the most recent binding for a variable *)

let rec lookup_value (env, x) =
  match env with
  | [] ->
      raise (Eval_error ("Unbound variable: " ^ x))
  | (y, v) :: rest ->
      if x = y then v else lookup_value (rest, x)

(* Extract an integer or report a runtime error *)

let expect_int = function
  | VInt n -> n
  | _ -> raise (Eval_error "Expected an integer")

(* Extract a boolean or report a runtime error *)

let expect_bool = function
  | VBool b -> b
  | _ -> raise (Eval_error "Expected a boolean")

(*
   eval : environment -> expr -> value
   Evaluate without substitution or AST copying
*)
let rec eval env e =
  match e with
  | Int n -> VInt n
  | Bool b -> VBool b
  | Var x -> lookup_value (env, x)

  (* Evaluate both operands from left to right *)
  (* Keep And and Or eager to match the original evaluator *)
  | And (e1, e2) ->
      let b1 = expect_bool (eval env e1) in
      let b2 = expect_bool (eval env e2) in
      VBool (b1 && b2)

  | Or (e1, e2) ->
      let b1 = expect_bool (eval env e1) in
      let b2 = expect_bool (eval env e2) in
      VBool (b1 || b2)

  | Not e1 ->
      VBool (not (expect_bool (eval env e1)))

  (* Integer operations *)
  | Plus (e1, e2) ->
      let n1 = expect_int (eval env e1) in
      let n2 = expect_int (eval env e2) in
      VInt (n1 + n2)

  | Mult (e1, e2) ->
      let n1 = expect_int (eval env e1) in
      let n2 = expect_int (eval env e2) in
      VInt (n1 * n2)

  | Equal (e1, e2) ->
      let n1 = expect_int (eval env e1) in
      let n2 = expect_int (eval env e2) in
      VBool (n1 = n2)

  (* Evaluate only the selected branch *)
  | If (e0, e1, e2) ->
      if expect_bool (eval env e0) then eval env e1
      else eval env e2

  (* Add a binding without modifying the AST *)
  | Let (x, e1, e2) ->
      let v = eval env e1 in
      eval ((x, v) :: env) e2

  (* Evaluate both components of a pair *)
  | Pair (e1, e2) ->
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      VPair (v1, v2)

  | First e1 ->
      begin match eval env e1 with
      | VPair (v1, _) -> v1
      | _ -> raise (Eval_error "First expects a pair")
      end

  | Second e1 ->
      begin match eval env e1 with
      | VPair (_, v2) -> v2
      | _ -> raise (Eval_error "Second expects a pair")
      end

  (* Save the environment where the function was defined *)
  | Fun (x, body) ->
      VClosure (x, body, env)

  | Fix (f, x, body) ->
      VRecClosure (f, x, body, env)

  (* Evaluate the function and its argument before calling *)
  | App (e1, e2) ->
      let fn = eval env e1 in
      let arg = eval env e2 in
      begin match fn with
      | VClosure (x, body, saved_env) ->
          eval ((x, arg) :: saved_env) body

      (* Bind the recursive name to the same closure *)
      (* Put the parameter first so it can shadow the name *)
      | VRecClosure (f, x, body, saved_env) ->
          eval ((x, arg) :: (f, fn) :: saved_env) body

      | _ ->
          raise (Eval_error "Expected a function")
      end

(* Print runtime values without exposing saved environments *)

let rec string_of_value = function
  | VInt n -> string_of_int n
  | VBool true -> "True"
  | VBool false -> "False"
  | VPair (v1, v2) ->
      "(" ^ string_of_value v1 ^ ", "
      ^ string_of_value v2 ^ ")"
  | VClosure _ | VRecClosure _ ->
      "<fun>"



(*****************)
(* Type checking *)
(*****************)



type arith_type =
  | INT
  | BOOL
  (* Types for pairs and functions *)
  | PAIR of arith_type * arith_type
  | ARROW of arith_type * arith_type
  (* Unknown types are filled in during inference *)
  | TVAR of arith_type option ref

(* Define a type to represent finite maps/typing contexts *)
type context = (var * arith_type) list

(* empty_context : context *)
let empty_context : context = []

(* lookup : context * var -> arith_type option
 * input :
 *    g - a typing context
 *    x - a variable
 * output :
 *    if (x,tau) is in g, return Some tau
 *    otherwise, return None
 *)
let rec lookup (g, x) : arith_type option =
  match g with
  | [] -> None
  | (y, tp) :: g' ->
      if x = y then Some tp else lookup (g', x)

(* extend : context * var * arith_type -> context
 * input:
 *    g - a typing context
 *    x - a variable
 *    tp - an arith_type
 * output:
 *    A typing context that maps x to tp and any other y to g(y)
 *)
let extend (g, x, tp) : context = (x, tp) :: g

(* Report incompatible types *)

exception Type_error

(* Create a new unknown type *)

let fresh_type () = TVAR (ref None)

(* Follow links to find the current type *)

let rec resolve tp =
  match tp with
  | TVAR ({ contents = Some t } as r) ->
      let t' = resolve t in
      r := Some t';
      t'
  | _ -> tp

(* Prevent a type from containing itself *)

let rec occurs r tp =
  match resolve tp with
  | TVAR s -> r == s
  | PAIR (t1, t2) | ARROW (t1, t2) ->
      occurs r t1 || occurs r t2
  | INT | BOOL -> false

(* Make two types agree *)

let rec unify t1 t2 =
  match resolve t1, resolve t2 with
  | INT, INT | BOOL, BOOL -> ()
  | TVAR r, TVAR s when r == s -> ()
  | TVAR r, tp | tp, TVAR r ->
      if occurs r tp then raise Type_error
      else r := Some tp
  | PAIR (a, b), PAIR (c, d)
  | ARROW (a, b), ARROW (c, d) ->
      unify a c;
      unify b d
  | _ -> raise Type_error

(* Remove solved links from the final type *)

let rec normalize tp =
  match resolve tp with
  | PAIR (t1, t2) -> PAIR (normalize t1, normalize t2)
  | ARROW (t1, t2) -> ARROW (normalize t1, normalize t2)
  | tp -> tp

(* Infer expression types using the typing rules *)
(* Let bindings use one shared type without generalization *)

let rec infer (g, e) : arith_type =
  match e with
  | Var x ->
      begin match lookup (g, x) with
      | Some tp -> tp
      | None -> raise Type_error
      end

  | Let (x, e1, e2) ->
      let tp = infer (g, e1) in
      infer (extend (g, x, tp), e2)

  | Bool _ -> BOOL

  | And (e1, e2) | Or (e1, e2) ->
      unify (infer (g, e1)) BOOL;
      unify (infer (g, e2)) BOOL;
      BOOL

  | Not e1 ->
      unify (infer (g, e1)) BOOL;
      BOOL

  | Int _ -> INT

  | Plus (e1, e2) | Mult (e1, e2) ->
      unify (infer (g, e1)) INT;
      unify (infer (g, e2)) INT;
      INT

  | Equal (e1, e2) ->
      unify (infer (g, e1)) INT;
      unify (infer (g, e2)) INT;
      BOOL

  (* The condition is boolean and branch types must agree *)
  | If (e0, e1, e2) ->
      unify (infer (g, e0)) BOOL;
      let t1 = infer (g, e1) in
      let t2 = infer (g, e2) in
      unify t1 t2;
      t1

  (* A pair stores the types of both components *)
  | Pair (e1, e2) ->
      let t1 = infer (g, e1) in
      let t2 = infer (g, e2) in
      PAIR (t1, t2)

  (* Require a pair and return its first component type *)
  | First e1 ->
      let t1 = fresh_type () in
      let t2 = fresh_type () in
      unify (infer (g, e1)) (PAIR (t1, t2));
      t1

  (* Require a pair and return its second component type *)
  | Second e1 ->
      let t1 = fresh_type () in
      let t2 = fresh_type () in
      unify (infer (g, e1)) (PAIR (t1, t2));
      t2

  (* Infer the parameter type from its uses in the body *)
  | Fun (x, body) ->
      let input = fresh_type () in
      let output = infer (extend (g, x, input), body) in
      ARROW (input, output)

  (* Add the recursive function and parameter to the context *)
  | Fix (f, x, body) ->
      let input = fresh_type () in
      let output = fresh_type () in
      let fn_type = ARROW (input, output) in
      let g' = extend (g, f, fn_type) in
      let g' = extend (g', x, input) in
      unify (infer (g', body)) output;
      fn_type

  (* Match the argument type with the function input *)
  | App (e1, e2) ->
      let fn_type = infer (g, e1) in
      let arg_type = infer (g, e2) in
      let output = fresh_type () in
      unify fn_type (ARROW (arg_type, output));
      output

(* Preserve the original type checker interface *)

let type_of_expr (g, e) : arith_type option =
  try Some (normalize (infer (g, e)))
  with Type_error -> None



(********************************************)
(* Utility functions for working with ARITH *)
(********************************************)



(*
  string_of_expr : expr -> string
  in : An expression AST [[e]].
  out : The concrete expression e in string format.
*)
let rec string_of_expr e =
  match e with
  | Var x -> x
  | Let (x, e1, e2) ->
      "Let " ^ x ^ " = " ^ string_of_expr e1
      ^ " In " ^ string_of_expr e2
  | Bool true -> "True"
  | Bool false -> "False"
  | Int n -> string_of_int n
  | And (e1, e2) ->
      "(" ^ string_of_expr e1 ^ " And " ^ string_of_expr e2 ^ ")"
  | Or (e1, e2) ->
      "(" ^ string_of_expr e1 ^ " Or " ^ string_of_expr e2 ^ ")"
  | Not e1 ->
      "(Not " ^ string_of_expr e1 ^ ")"
  | Plus (e1, e2) ->
      "(" ^ string_of_expr e1 ^ " + " ^ string_of_expr e2 ^ ")"
  | Mult (e1, e2) ->
      "(" ^ string_of_expr e1 ^ " * " ^ string_of_expr e2 ^ ")"
  | Equal (e1, e2) ->
      "(" ^ string_of_expr e1 ^ " = " ^ string_of_expr e2 ^ ")"
  | If (e1, e2, e3) ->
      "If " ^ string_of_expr e1
      ^ " Then " ^ string_of_expr e2
      ^ " Else " ^ string_of_expr e3

  (* Display pairs and projections *)
  | Pair (e1, e2) ->
      "(" ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | First e1 ->
      "(First " ^ string_of_expr e1 ^ ")"
  | Second e1 ->
      "(Second " ^ string_of_expr e1 ^ ")"

  (* Display ordinary and recursive functions *)
  | Fun (x, body) ->
      "(Fun " ^ x ^ " -> " ^ string_of_expr body ^ ")"
  | Fix (f, x, body) ->
      "(Fix " ^ f ^ "." ^ x ^ " -> "
      ^ string_of_expr body ^ ")"

  (* Parentheses keep application grouping clear *)
  | App (e1, e2) ->
      "(" ^ string_of_expr e1 ^ " "
      ^ string_of_expr e2 ^ ")"

(*
  pretty_trace : expr -> bool -> unit
  in : AST [[e]], stepper flag
  out : ()
  side effects : Pretty prints execution trace of e. Blocks on keystroke
  between reductions if stepper is on.
*)
let rec pretty_trace e stepper =
  Printf.printf "%s" (string_of_expr e);
  if stepper then ignore (read_line ()) else ();
  if is_val e then (
    Printf.printf "\n";
    flush stdout
  ) else
    match step e with
    | NotReducible ->
        Printf.printf "  (Bad, Stuck Expression)\n";
        flush stdout
    | Step e' ->
        Printf.printf "->\n";
        flush stdout;
        pretty_trace e' stepper

(*
  stepper : expr -> ()
  in : AST [[e]]
  out : ()
  side effects : Pretty prints execution trace of e. Blocks on keystroke
  between reductions.
*)
let stepper e = pretty_trace e true

(*
  tracer : expr -> ()
  in : AST [[e]]
  out : ()
  side effects : Pretty prints execution trace of e.
*)
let tracer e = pretty_trace e false