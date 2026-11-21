open CatML

exception Runtime_error of string

let report_position lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Printf.sprintf "%s:%d:%d"
    pos.Lexing.pos_fname
    pos.Lexing.pos_lnum
    (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)

let parse_file filename =
  let channel = open_in filename in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () ->
      let lexbuf = Lexing.from_channel channel in

      lexbuf.Lexing.lex_curr_p <-
        { lexbuf.Lexing.lex_curr_p with
          Lexing.pos_fname = filename };

      try Parser.prog Lexer.read lexbuf with
      | Parser.Error ->
          failwith
            (Printf.sprintf "%s: syntax error near %S"
               (report_position lexbuf)
               (Lexing.lexeme lexbuf))
      | Failure message ->
          failwith
            (Printf.sprintf "%s: lexer error: %s"
               (report_position lexbuf)
               message))

let run_file filename =
  let ast = parse_file filename in

  match Lang.type_of_expr (Lang.empty_context, ast) with
  | None ->
      failwith
        (Printf.sprintf "%s: type error" filename)

  | Some _ ->
      let result = Lang.multistep ast in

      if Lang.is_val result then
        print_endline (Lang.string_of_expr result)
      else
        raise
          (Runtime_error
             ("Evaluation became stuck at: "
              ^ Lang.string_of_expr result))

let () =
  if Array.length Sys.argv <> 2 then begin
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 2
  end;

  try run_file Sys.argv.(1) with
  | Sys_error message ->
      Printf.eprintf "File error: %s\n" message;
      exit 1

  | Failure message ->
      Printf.eprintf "%s\n" message;
      exit 1

  | Runtime_error message ->
      Printf.eprintf "Runtime error: %s\n" message;
      exit 1