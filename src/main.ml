(* $State: Exp $ $Date: 2004/12/08 14:36:10 $ $Revision: 1.19 $ *)
(*######################################################*)
(*			main.ml				*)
(*######################################################*)

open Restart
open Types.Base
open Format
open Basic
open Types
open Lexer
open Parse_cmd
open Files
open Sys
open Version
open Af2_basic
open Module
open Interact
open Tex
open Flags
open Inductive
open Print
open Option

let _ =
  if not !compiling then begin
  print_newline ();
  open_vbox 0;
  print_string "** This is PhoX Logic, version ";
  print_string version;
  print_string " ";
  print_string "By C. Raffalli **";
  print_newline ();
  print_newline ()
end

let prompt = ">PhoX>"
let pprompt = "%PhoX%"

let print_prompt() =
  open_hbox ();
  print_string (if !cur_proof = No_proof then prompt else pprompt);
  print_string " "; print_flush ()

let read_fun =
  if !compiling then
    (fun _ ->
      try
        let c = input_char !cur_input in
        if c == '\n' then incr cur_line;
	if print_echo then print_char c;
        (match pipe_exit with
	  Some f -> output_char f c; if c = '\n' then flush f
        | None -> ());
    	Some c
      with End_of_file -> Some '\255')
  else
    let bol = ref true in
    (fun _ ->
      if !bol && is_top () then print_prompt();
      try
    	let c = input_char !cur_input in
    	if !bol then begin
	  incr cur_line; cur_col := 0
    	end else begin
	  incr cur_col
    	end;
    	bol := c == '\n';
	if print_echo then (print_char c; if c = '\n' then flush stdout);
        (match pipe_exit with
	  Some f -> output_char f c; if c = '\n' then flush f
        | None -> ());
    	Some c
      with End_of_file -> bol:= false; Some '\255')


exception Lambda_cmd

let emergency_exit () =
  pop_all ();
  if !compiling && not !in_inductive then begin
    exit_tex ();
    print_endline "aborted !";
    exit 2
  end

let print_pos () =
  if input_name <> "" then begin
    open_hbox ();
    print_string "File \"";
    print_string (Filename.concat dirname input_name);
    print_string "\", line ";
    print_int !cur_line;
    print_string ", characters ";
    print_int !cur_col;
    print_string ":";
    print_newline ()
  end

let rec do_one_cmd cstrm tstrm () =
  try
    parse_cmd cstrm tstrm
  with
    Error ->
      print_pos (); emergency_exit ()
  | End_of_file -> pop_input ()
  | Lambda_cmd -> ()
  | Failure s -> open_hbox (); print_string "Failure: ";print_string s;
                 print_newline (); print_pos (); emergency_exit ()
  | Break -> print_endline "Interrupt.";
             print_pos (); emergency_exit ()
  | Out_of_memory -> print_endline "Out of Memory"; print_pos ();
                     emergency_exit ()

let global = ref true

let rec loop f =
  try
    catch_break true;
    while true do f (); flush stdout done
  with
    Sys.Break ->
      catch_break false; print_endline "Interrupt.";
      if !compiling then raise Error else loop f
  | Quit ->
      if not !global then (
        print_endline "End of file before end of module !";
        print_pos (); emergency_exit ())
  | Restart ->
        print_endline "PhoX restarted";
        restart ()
  | End_of_module ->
      if !global then (
        print_endline "Unexpected \"end\".";
        print_pos (); emergency_exit ())
  | e ->
      print_endline (
      "Unknown exception \""^(Printexc.to_string e)^"\" raised !");
      loop f

let started = ref false

let go savename cstrm tstrm =
  if !started then begin
    reset_flags ();
    reset_base ()
  end;
  started:=true;
  add_basic_tex ();
  load_pervasives ();
  after_pervasives ();
  loop (do_one_cmd cstrm tstrm);
  if !compiling then write_all savename

let parse_file () =
  let cstrm = Stream.from read_fun in
  let tstrm = stream_map next_token cstrm in
  let rec fn = parser
    [< 'Ident "tex"; str >] ->
      parse_tex_header str; gn str
  | [< 'Ident "flag"; 'Ident s; v = parse_value; 'Dot; str >] ->
        set_flag s v; fn str
  | [< >] -> ()
  and gn = parser
    [< 'Ident "flag"; 'Ident s; v = parse_value; 'Dot; str >] ->
        set_flag s v; fn str
  | [< >] -> () in
  if !compiling then try fn tstrm;
  match tstrm with parser
    [< 'Ident "Module"; 'Ident mod_name; 'Dot >] ->
      global := false;
      go (Filename.concat dirname
           (concat_module_names root mod_name)) cstrm tstrm;
      local_modules := mod_name::!local_modules;
      let rec fn = parser
        [< 'Ident "Module"; 'Ident mod_name; 'Dot >] ->
          global := false;
          go (Filename.concat dirname
               (concat_module_names root mod_name)) cstrm tstrm;
          local_modules := mod_name::!local_modules;
          fn tstrm
      | [< 'Eof >] -> raise Quit
      in fn tstrm
  | [< >] ->
      go (Filename.concat dirname root) cstrm tstrm
  with
    Illegal_char c ->
                 if not !compiling then reset_lexer cstrm;
                 open_hbox ();
                 print_string "Syntax Error: Illegal char \"";
                 print_string (Char.escaped c);
                 print_string "\"."; print_newline ();
                 print_pos (); emergency_exit ()
  | Stream.Failure ->
                 if not !compiling then reset_lexer cstrm;
                 print_endline "Syntax Error: Parse_failure ?";
                 print_pos (); emergency_exit ()
  | Stream.Error s ->
                 if not !compiling then reset_lexer cstrm;
                 open_hbox ();
                 print_string "Syntax Error: ";
                 print_string (if s = "" then "?" else s);
                 print_newline ();
                 print_pos (); emergency_exit ()
  | Base_failure s ->
                 open_hbox ();
                 print_string "Error: ";
                 print_string s;print_newline ();
                 print_pos (); emergency_exit ()
  | Gen_error s ->
                 open_hbox ();
                 print_string "Error: ";
                 print_string s; print_newline ();
                 print_pos (); emergency_exit ()
  | Not_found ->
                 print_endline "Error: Bug Not_found escaped";
                 print_pos (); emergency_exit ()
  | Restart ->
                 print_endline "PhoX restarted";
                 restart ()
  | Quit ->
                 ()
  else go (Filename.concat dirname root) cstrm tstrm

let _ =
  if !compiling then
    cur_input := open_path (Filename.concat dirname input_name);
  if not !compiling then Files.print_path ();
  parse_file ();
  close_tex ();
  print_newline ();
  print_endline "bye";
  exit 0
