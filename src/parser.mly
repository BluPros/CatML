%{
open Lang
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

/* Boolean operators */
%token AND OR NOT

/* Pair syntax */
%token COMMA FIRST SECOND

/* Function syntax */
%token FUN FIX DOT ARROW

%start <Lang.expr> prog

%%

prog:
  | e = expr; EOF { e }
  ;

/* Let, If, and function bodies extend to the right */
expr:
  | LET; x = ID; EQUALS; e1 = expr; IN; e2 = expr
      { Let(x,e1,e2) }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr
      { If(e1,e2,e3) }
  | FUN; x = ID; ARROW; body = expr
      { Fun(x,body) }
  | FIX; f = ID; DOT; x = ID; ARROW; body = expr
      { Fix(f,x,body) }
  | e = or_expr { e }
  ;

/* Or has lower precedence than And */
or_expr:
  | e1 = or_expr; OR; e2 = and_expr
      { Or(e1,e2) }
  | e = and_expr { e }
  ;

and_expr:
  | e1 = and_expr; AND; e2 = equal_expr
      { And(e1,e2) }
  | e = equal_expr { e }
  ;

/* Use parentheses when nesting equality expressions */
equal_expr:
  | e1 = add_expr; EQUALS; e2 = add_expr
      { Equal(e1,e2) }
  | e = add_expr { e }
  ;

/* Addition and multiplication group to the left */
add_expr:
  | e1 = add_expr; PLUS; e2 = mult_expr
      { Plus(e1,e2) }
  | e = mult_expr { e }
  ;

mult_expr:
  | e1 = mult_expr; TIMES; e2 = app_expr
      { Mult(e1,e2) }
  | e = app_expr { e }
  ;

/* Application groups to the left */
/* f x y means (f x) y */
app_expr:
  | e1 = app_expr; e2 = prefix_expr
      { App(e1,e2) }
  | e = prefix_expr { e }
  ;

/* Prefix operators bind more tightly than application */
prefix_expr:
  | NOT; e = prefix_expr { Not e }
  | FIRST; e = prefix_expr { First e }
  | SECOND; e = prefix_expr { Second e }
  | e = atom { e }
  ;

/* Parentheses contain grouped expressions or pairs */
atom:
  | i = INT { Int i }
  | x = ID { Var x }
  | TRUE { Bool true }
  | FALSE { Bool false }
  | LPAREN; e = expr; RPAREN { e }
  | LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN
      { Pair(e1,e2) }
  ;