(* File generated by the BNF Converter (bnfc 2.9.5). *)

(* Lexer definition for ocamllex. *)

(* preamble *)
{
open ParStella
open Lexing

let symbol_table = Hashtbl.create 36
let _ = List.iter (fun (kwd, tok) -> Hashtbl.add symbol_table kwd tok)
                  [("µ", SYMB1);(",", SYMB2);(";", SYMB3);("(", SYMB4);(")", SYMB5);("{", SYMB6);("}", SYMB7);("[", SYMB8);("]", SYMB9);("=", SYMB10);(":", SYMB11);("->", SYMB12);("=>", SYMB13);("|", SYMB14);("<|", SYMB15);("|>", SYMB16);(":=", SYMB17);("<", SYMB18);("<=", SYMB19);(">", SYMB20);(">=", SYMB21);("==", SYMB22);("!=", SYMB23);("+", SYMB24);("-", SYMB25);("*", SYMB26);("/", SYMB27);(".", SYMB28);("List::head", SYMB29);("List::isempty", SYMB30);("List::tail", SYMB31);("panic!", SYMB32);("Nat::pred", SYMB33);("Nat::iszero", SYMB34);("Nat::rec", SYMB35);("&", SYMB36)]

let resword_table = Hashtbl.create 45
let _ = List.iter (fun (kwd, tok) -> Hashtbl.add resword_table kwd tok)
                  [("language", KW_language);("core", KW_core);("extend", KW_extend);("with", KW_with);("fn", KW_fn);("return", KW_return);("generic", KW_generic);("type", KW_type);("exception", KW_exception);("variant", KW_variant);("inline", KW_inline);("throws", KW_throws);("cast", KW_cast);("as", KW_as);("inl", KW_inl);("inr", KW_inr);("cons", KW_cons);("false", KW_false);("true", KW_true);("unit", KW_unit);("succ", KW_succ);("if", KW_if);("then", KW_then);("else", KW_else);("let", KW_let);("in", KW_in);("letrec", KW_letrec);("match", KW_match);("or", KW_or);("and", KW_and);("new", KW_new);("throw", KW_throw);("try", KW_try);("catch", KW_catch);("not", KW_not);("fix", KW_fix);("fold", KW_fold);("unfold", KW_unfold);("auto", KW_auto);("forall", KW_forall);("Bool", KW_Bool);("Nat", KW_Nat);("Unit", KW_Unit);("Top", KW_Top);("Bot", KW_Bot)]

let unescapeInitTail (s:string) : string =
  let rec unesc s = match s with
      '\\'::c::cs when List.mem c ['\"'; '\\'; '\''] -> c :: unesc cs
    | '\\'::'n'::cs  -> '\n' :: unesc cs
    | '\\'::'t'::cs  -> '\t' :: unesc cs
    | '\\'::'r'::cs  -> '\r' :: unesc cs
    | '\"'::[]    -> []
    | '\''::[]    -> []
    | c::cs      -> c :: unesc cs
    | _         -> []
  (* explode/implode from caml FAQ *)
  in let explode (s : string) : char list =
      let rec exp i l =
        if i < 0 then l else exp (i - 1) (s.[i] :: l) in
      exp (String.length s - 1) []
  in let implode (l : char list) : string =
      let res = Buffer.create (List.length l) in
      List.iter (Buffer.add_char res) l;
      Buffer.contents res
  in implode (unesc (List.tl (explode s)))

let incr_lineno (lexbuf:Lexing.lexbuf) : unit =
    let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with
            pos_lnum = pos.pos_lnum + 1;
            pos_bol = pos.pos_cnum;
        }
}

(* BNFC character classes *)
let _letter = ['a'-'z' 'A'-'Z' '\192' - '\255'] # ['\215' '\247']    (*  isolatin1 letter FIXME *)
let _upper  = ['A'-'Z' '\192'-'\221'] # '\215'      (*  capital isolatin1 letter FIXME *)
let _lower  = ['a'-'z' '\222'-'\255'] # '\247'      (*  small isolatin1 letter FIXME *)
let _digit  = ['0'-'9']                             (*  _digit *)
let _idchar = _letter | _digit | ['_' '\'']         (*  identifier character *)
let _universal = _                                  (* universal: any character *)

(* reserved words consisting of special symbols *)
let rsyms = "µ" | "," | ";" | "(" | ")" | "{" | "}" | "[" | "]" | "=" | ":" | "->" | "=>" | "|" | "<|" | "|>" | ":=" | "<" | "<=" | ">" | ">=" | "==" | "!=" | "+" | "-" | "*" | "/" | "." | "List::head" | "List::isempty" | "List::tail" | "panic!" | "Nat::pred" | "Nat::iszero" | "Nat::rec" | "&"

(* user-defined token types *)
let stellaIdent = ('_' | _letter)('!' | '-' | ':' | '?' | '_' | (_digit | _letter)) *
let extensionName = '#' ('-' | '_' | (_digit | _letter)) +
let memoryAddress = "<0x" ('A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | _digit)+ '>'

(* lexing rules *)
rule token =
  parse "//" (_ # '\n')*
                { token lexbuf }
      | "/*" [^ '*']* '*' ([^ '*' '/'][^ '*']* '*' | '*')* '/'
                { token lexbuf }
      | rsyms   { let x = lexeme lexbuf in try Hashtbl.find symbol_table x with Not_found -> failwith ("internal lexer error: reserved symbol " ^ x ^ " not found in hashtable") }
      | stellaIdent
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_StellaIdent l }
      | extensionName
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_ExtensionName l }
      | memoryAddress
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_MemoryAddress l }
      | _letter _idchar*
                { let l = lexeme lexbuf in try Hashtbl.find resword_table l with Not_found -> TOK_Ident l }
      | _digit+ { TOK_Integer (int_of_string (lexeme lexbuf)) }
      | _digit+ '.' _digit+ ('e' ('-')? _digit+)?
                { TOK_Double (float_of_string (lexeme lexbuf)) }
      | '\"' (([^ '\"' '\\' '\n']) | ('\\' ('\"' | '\\' | '\'' | 'n' | 't' | 'r')))* '\"'
                { TOK_String (unescapeInitTail (lexeme lexbuf)) }
      | '\'' (([^ '\'' '\\']) | ('\\' ('\\' | '\'' | 'n' | 't' | 'r'))) '\''
                { TOK_Char (unescapeInitTail (lexeme lexbuf)).[0] }
      | [' ' '\t' '\r']
                { token lexbuf }
      | '\n'    { incr_lineno lexbuf; token lexbuf }
      | eof     { TOK_EOF }
