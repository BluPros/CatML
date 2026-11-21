open CatML

(* report lexer and parser errors with source locations *)

exception Source_error of Lang.location * string

(* read the complete source file *)

let read_file filename =
  let channel = open_in_bin filename in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () ->
      really_input_string channel (in_channel_length channel))

(* get the source range of the current token *)

let token_location lexbuf : Lang.location = {
  start_pos = lexbuf.Lexing.lex_start_p;
  end_pos = lexbuf.Lexing.lex_curr_p;
}

(* parse source and preserve token locations on failure *)

let parse_source filename source =
  let lexbuf = Lexing.from_string source in
  let start_pos = {
    lexbuf.Lexing.lex_curr_p with
    Lexing.pos_fname = filename;
  } in

  lexbuf.Lexing.lex_curr_p <- start_pos;
  lexbuf.Lexing.lex_start_p <- start_pos;

  try Parser.prog Lexer.read lexbuf with
  | Parser.Error ->
      let token = Lexing.lexeme lexbuf in
      let message =
        if token = "" then
          "syntax error: unexpected end of file"
        else
          Printf.sprintf "syntax error: unexpected token %S" token
      in
      raise (Source_error (token_location lexbuf, message))

  | Failure message ->
      raise (
        Source_error (token_location lexbuf, "lexer error: " ^ message)
      )

(* display the first source line covered by an error *)
(* positions are byte offsets, matching the lexer *)

let report_error filename source (loc : Lang.location) message =
  let start_pos = loc.start_pos in
  let end_pos = loc.end_pos in
  let source_length = String.length source in

  let line_start =
    max 0 (min source_length start_pos.Lexing.pos_bol)
  in

  let rec find_line_end i =
    if i >= source_length then source_length
    else
      match source.[i] with
      | '\n' | '\r' -> i
      | _ -> find_line_end (i + 1)
  in

  let line_end = find_line_end line_start in
  let line = String.sub source line_start (line_end - line_start) in

  let column =
    max 0
      (min (String.length line)
         (start_pos.Lexing.pos_cnum - line_start))
  in

  let underline_end =
    if end_pos.Lexing.pos_lnum = start_pos.Lexing.pos_lnum then
      max column
        (min (String.length line)
           (end_pos.Lexing.pos_cnum - line_start))
    else
      String.length line
  in

  let width = max 1 (underline_end - column) in

  (* preserve tabs so the underline stays aligned *)
  let padding =
    String.init column
      (fun i -> if line.[i] = '\t' then '\t' else ' ')
  in

  Printf.eprintf "%s:%d:%d\n"
    filename
    start_pos.Lexing.pos_lnum
    (column + 1);

  Printf.eprintf "%s\n%s%s\n"
    line padding (String.make width '^');

  Printf.eprintf "%s\n" message;

  if end_pos.Lexing.pos_lnum > start_pos.Lexing.pos_lnum then
    Printf.eprintf "expression continues onto a later line\n"

(* parse, type-check, evaluate, and print *)

let run_file filename =
  let source = read_file filename in

  try
    let ast = parse_source filename source in
    ignore (Lang.type_check (Lang.empty_context, ast));
    let result = Lang.eval [] ast in
    print_endline (Lang.string_of_value result)
  with
  | Source_error (loc, message) ->
      report_error filename source loc message;
      exit 1

  | Lang.Located_type_error (loc, message) ->
      report_error filename source loc ("type error: " ^ message);
      exit 1

(* process the command-line argument *)

let () =
  if Array.length Sys.argv <> 2 then begin
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 2
  end;

  try run_file Sys.argv.(1) with
  | Sys_error message ->
      Printf.eprintf "file error: %s\n" message;
      exit 1

  | Lang.Eval_error message ->
      Printf.eprintf "runtime error: %s\n" message;
      exit 1