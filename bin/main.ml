open Stella

(* File generated by the BNF Converter (bnfc 2.9.5). *)

open Lexing

let parse (c : in_channel) : AbsStella.program =
  let lexbuf = Lexing.from_channel c in
  try ParStella.pProgram LexStella.token lexbuf
  with Parsing.Parse_error ->
    let start_pos = Lexing.lexeme_start_p lexbuf
    and end_pos = Lexing.lexeme_end_p lexbuf in
    raise (BNFC_Util.Parse_error (start_pos, end_pos))

let showTree (t : AbsStella.program) : string =
  "[Abstract syntax]\n\n"
  ^ ShowStella.show (ShowStella.showProgram t)
  ^ "\n\n" ^ "[Linearized tree]\n\n"
  ^ PrintStella.printTree PrintStella.prtProgram t
  ^ "\n"

let main () =
  let channel =
    if Array.length Sys.argv > 2 then open_in Sys.argv.(2) else stdin
  in
  try
    if Array.length Sys.argv > 1 then
      match Sys.argv.(1) with
      | "typecheck" -> Typecheck.typecheckProgram (parse channel)
      | "show" -> print_string (showTree (parse channel))
      | _ -> print_string "Usage: stella [show|typecheck] {FILE}\n"
    else print_string "Usage: stella [show|typecheck] {FILE}\n";
    flush stdout;
    exit 0
  with
  | BNFC_Util.Parse_error (start_pos, end_pos) ->
      Printf.printf "Parse error at %d.%d-%d.%d\n" start_pos.pos_lnum
        (start_pos.pos_cnum - start_pos.pos_bol + 1)
        end_pos.pos_lnum
        (end_pos.pos_cnum - end_pos.pos_bol + 1);
      exit 1
  | Typecheck.TyExn err ->
      print_string (Typecheck.showError err);
      exit 2
;;

main ()
