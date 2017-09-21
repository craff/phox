(* $State: Exp $ $Date: 2006/02/24 17:01:54 $ $Revision: 1.8 $ *)
(*######################################################*)
(*			tex.ml				*)
(*######################################################*)

open Basic
open Stream
open Types
open Lexer
open Parser
open Print
open Format
open Af2_basic
open Interact
open Flags
open Option

let rec parse_ident_list = parser
  [< s = parse_ident; l = parse_ident_list >] -> s :: l
| [< >] -> []

let tex_docs = ref []

let parse_tex_header str =
  let title = ref "" in
  let preambule = ref "" in
  let author = ref "" in
  let institute = ref "" in
  let doc_list = ref [] in
  let fn str = match str with parser
    [< 'Ident "title";
       'Kwd "=" ?? serror "=" str;
       'Str s ?? serror "a string" str >] ->
       if !title <> "" then failwith "title allready specified";
       title := s
  | [< 'Ident "author";
       'Kwd "=" ?? serror "=" str;
       'Str s ?? serror "a string" str >] ->
       if !author <> "" then failwith "author allready specified";
       author := s
  | [< 'Ident "institute";
       'Kwd "=" ?? serror "=" str;
       'Str s ?? serror "a string" str >] ->
       if !institute <> "" then failwith "institute allready specified";
       institute := s
  | [< 'Ident "preambule";
       'Kwd "=" ?? serror "=" str;
       'Str s ?? serror "a string" str >] ->
       preambule := !preambule ^ s
  | [< 'Ident "documents";
       'Kwd "=" ?? serror "=" str;
       l = parse_ident_list >] ->
       doc_list := !doc_list @ l
  | [< 'Dot  >] -> raise Exit
  in
  try while true do fn str done with Exit -> ();
  let gn doc =
    let fname = root ^ "." ^ doc ^ ".tex" in
    let ch = open_out (Filename.concat dirname fname) in
    output_string ch "\\input{";
    output_string ch "phox_preambule";
    output_string ch "}\n\n";
    output_string ch "\\beginafdeux%\n  {";
    output_string ch !title;
    output_string ch "}%\n  {";
    output_string ch !author;
    output_string ch "}%\n  {";
    output_string ch !institute;
    output_string ch "}%\n  {";
    output_string ch !preambule;
    output_string ch "}\n\n";
    doc, ch
  in if !compiling then tex_docs := List.map gn !doc_list

let do_tex docs cstr =
  let fn s =
    try List.assoc s !tex_docs
    with Not_found -> failwith ("Unknown document: "^s) in
  let chs = if !compiling then List.map fn docs else [] in
  let last_out_newline = ref true in
  let outc c =
    last_out_newline := c = '\n' ||
      ((c = ' ' || c = '\t') && !last_out_newline);
    List.iter (fun ch -> output_char ch c) chs in
  let outs s =
    let c = s.[String.length s - 1] in
    last_out_newline := c = '\n';
    List.iter (fun ch -> output_string ch s) chs in
  let eat_space () =
    match cstr with parser
      [< ' (' ') >] ->
        (match Stream.peek cstr with
          Some ('!' | '%' | '&' | '*' | '+' | ',' | '-' | '/' | ':' | ';' |
        '<' | '=' | '>' | '@' | '[' | '\\' | ']' | '^' | '`' | '#' |
        '{' | '|' | '}' | '~') -> ()
        | Some ('A'..'Z' | 'a'..'z') -> outs "  "
        | _ -> outc ' ')
    | [< >] -> () in
  let do_math f s =
    f false s;
    if !extra_dot then (outc '.'; extra_dot := false)
                  else eat_space ()
    in
  let do_display f s =
    f true s;
    if !extra_dot then (outc '.'; extra_dot := false)
                  else eat_space ()
    in
  let read_expr end_tok s =
    let tstrm = stream_map next_token cstr in
    parse_tex_expr end_tok tstrm in
  let verb_expr n end_tok mmath s =
    set_local n;
    let e = read_expr end_tok s in
    let save = get_formatter_output_functions () in
    let fn ch =
      set_formatter_out_channel ch;
      let sm = get_margin () and sb = get_max_indent () in
      set_max_indent !tex_max_indent;
      if mmath then begin
	set_margin !tex_margin;
	print_string "\n\\begin{Verbatim}";
        print_newline ()
       end else begin
	set_margin 10000000;
	print_string "¶";
        print_flush ()
      end;
      in_mmath := mmath;
      in_verb := true;
      print_expr e;
      tex_local := [];
      print_flush ();
      in_mmath := false;
      in_verb := false;
      if mmath then begin
        print_newline ();
	print_string "\\end{Verbatim}";
        print_newline ()
     end else begin
	set_margin sm; set_max_indent sb;
	print_string "¶";
        print_flush ()
      end;
      print_flush () in
    List.iter fn chs;
    set_formatter_output_functions (fst save) (snd save);
    set_local 0 in
  let tex_expr n end_tok mmath s =
    set_local n;
    let e = read_expr end_tok s in
    if not !last_out_newline then outs "%\n";
    let save = get_formatter_output_functions () in
    let fn ch =
      set_formatter_out_channel ch;
      in_mmath := mmath;
      (if mmath then
        print_string "\\afdmmath{}"
      else
       	print_string "\\afdmath{}");
      print_tex_expr e;
      tex_local := [];
      (if mmath then
        print_string "\\endafdmmath{}"
      else
       	print_string "\\endafdmath{}");
      in_mmath := false;
      print_flush () in
    List.iter fn chs;
    set_formatter_output_functions (fst save) (snd save);
    set_local 0 in
  let may_be_int str =
    let rec fn = parser
      [< ' ('0'..'9') as c; n = fn >] ->
        (Char.code c - Char.code '0') * 10 + n
    | [< >] -> 0 in
    fn str / 10
  in
  let fn str = match str with parser
    [< ' ('\\' as c); str >] -> (
      match str with parser
        [< ' ('['); str >] -> (
        match str with parser
          [< ' ('['); n = may_be_int; str >] ->
            do_display (tex_expr n "\\]]") str
        | [< n = may_be_int >] -> do_math (tex_expr n "\\]") str)
      | [< ' ('{'); str >] -> (
        match str with parser
          [< ' ('{'); n = may_be_int; str >] ->
            do_display (verb_expr n "\\}}") str
        | [< n = may_be_int >] -> do_math (verb_expr n "\\}") str)
      | [< ' ('\\'); str >] -> (
        match str with parser
          [< ' ('['); str >] -> outs "\\["
        | [< ' ('{'); str >] -> outs "\\{"
        | [< >] -> outs "\\\\")
      | [< >] -> outc c)
  | [< ' ('*' as c); str >] -> (
      match str with parser
          [< ' (')') >] -> outc ' '; raise Exit
        | [< >] -> outc c)
  | [< '( '\255') >] -> raise (Stream.Error "Unfinished TeX Comment")
  | [< 'c >] -> outc c in
  let save = get_formatter_output_functions () in
  try while true do fn cstr done
  with
    Exit -> ()
  | e -> set_formatter_output_functions (fst save) (snd save);
         set_local 0; raise e

let close_tex () =
  let gn (_, ch) =
    output_string ch "\n\\endafdeux\n";
    close_out ch
  in if !compiling then List.iter gn !tex_docs

let exit_tex () =
  let gn (doc, ch) =
    close_out ch;
    let fname = root ^ "." ^ doc ^ ".tex" in
    print_endline ("removing: "^fname);
    Sys.remove fname
  in if !compiling then List.iter gn !tex_docs

let parse_tex_sym = parser
  [< 'Str s >] -> ("\\hbox{"^s^"}"), Trivial
| [< 'Ident "Math"; 'Str s >] -> s, Trivial
| [< 'Ident "Mute" >] -> "", Mute
| [< s,sy,_ = parse_syntax_def true >] -> s,sy
