{
open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
(* Allow names such as x1 and my_pair *)
let id = (letter | '_') (letter | digit | '_')*
let newline = "\r\n" | '\n' | '\r'

rule read =
  parse
  | white { read lexbuf }
  (* Handle line endings and update error positions *)
  | newline { Lexing.new_line lexbuf; read lexbuf }

  | "True" { TRUE }
  | "False" { FALSE }

  (* Boolean operators *)
  | "And" { AND }
  | "Or" { OR }
  | "Not" { NOT }

  | "*" { TIMES }
  | "+" { PLUS }
  | "(" { LPAREN }
  | ")" { RPAREN }

  (* Pair syntax *)
  | "," { COMMA }
  | "First" { FIRST }
  | "Second" { SECOND }

  | "Let" { LET }
  | "=" { EQUALS }
  | "In" { IN }
  | "If" { IF }
  | "Then" { THEN }
  | "Else" { ELSE }

  (* Function syntax *)
  | "Fun" { FUN }
  | "Fix" { FIX }
  | "." { DOT }
  | "->" { ARROW }

  (* Accept the mathematical symbols from the handout *)
  | "→" { ARROW }
  | "×" { TIMES }

  | id { ID (Lexing.lexeme lexbuf) }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }

  (* Report any unsupported character *)
  | _ {
      failwith
        (Printf.sprintf "unexpected character %S"
           (Lexing.lexeme lexbuf))
    }