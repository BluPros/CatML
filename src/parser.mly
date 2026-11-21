%{
open Lang

(* attach the source range supplied by menhir *)

let located start_pos end_pos e =
  Located ({ start_pos; end_pos }, e)
%}

%token <int> INT
%token <string> ID
%token TRUE
%token FALSE
%token TIMES
%token PLUS
%token LPAREN
%token RPAREN
%token LET
%token EQUALS
%token IN
%token IF
%token THEN
%token ELSE
%token EOF

/* boolean operators */
%token AND OR NOT

/* pair syntax */
%token COMMA FIRST SECOND

/* function syntax */
%token FUN FIX DOT ARROW

%start <Lang.expr> prog

%%

prog:
  | e = expr; EOF { e }
  ;

/* let, if, and function bodies extend to the right */
expr:
  | LET; x = ID; EQUALS; e1 = expr; IN; e2 = expr
      { located $startpos $endpos (Let (x, e1, e2)) }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr
      { located $startpos $endpos (If (e1, e2, e3)) }
  | FUN; x = ID; ARROW; body = expr
      { located $startpos $endpos (Fun (x, body)) }
  | FIX; f = ID; DOT; x = ID; ARROW; body = expr
      { located $startpos $endpos (Fix (f, x, body)) }
  | e = or_expr { e }
  ;

/* or has lower precedence than and */
or_expr:
  | e1 = or_expr; OR; e2 = and_expr
      { located $startpos $endpos (Or (e1, e2)) }
  | e = and_expr { e }
  ;

and_expr:
  | e1 = and_expr; AND; e2 = equal_expr
      { located $startpos $endpos (And (e1, e2)) }
  | e = equal_expr { e }
  ;

/* use parentheses when nesting equality expressions */
equal_expr:
  | e1 = add_expr; EQUALS; e2 = add_expr
      { located $startpos $endpos (Equal (e1, e2)) }
  | e = add_expr { e }
  ;

/* addition and multiplication group to the left */
add_expr:
  | e1 = add_expr; PLUS; e2 = mult_expr
      { located $startpos $endpos (Plus (e1, e2)) }
  | e = mult_expr { e }
  ;

mult_expr:
  | e1 = mult_expr; TIMES; e2 = app_expr
      { located $startpos $endpos (Mult (e1, e2)) }
  | e = app_expr { e }
  ;

/* application groups to the left */
/* f x y means (f x) y */
app_expr:
  | e1 = app_expr; e2 = prefix_expr
      { located $startpos $endpos (App (e1, e2)) }
  | e = prefix_expr { e }
  ;

/* prefix operators bind more tightly than application */
prefix_expr:
  | NOT; e = prefix_expr
      { located $startpos $endpos (Not e) }
  | FIRST; e = prefix_expr
      { located $startpos $endpos (First e) }
  | SECOND; e = prefix_expr
      { located $startpos $endpos (Second e) }
  | e = atom { e }
  ;

/* parentheses contain grouped expressions or pairs */
atom:
  | i = INT
      { located $startpos $endpos (Int i) }
  | x = ID
      { located $startpos $endpos (Var x) }
  | TRUE
      { located $startpos $endpos (Bool true) }
  | FALSE
      { located $startpos $endpos (Bool false) }
  | LPAREN; e = expr; RPAREN
      { e }
  | LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN
      { located $startpos $endpos (Pair (e1, e2)) }
  ;