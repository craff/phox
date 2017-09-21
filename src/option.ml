(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.5 $ *)
(*######################################################*)
(*			option.ml			*)
(*######################################################*)

(*
  Contient la definition des constantes de base utilisees par AF2:
    implication, quantification, regle etc ...
*)

open Format
open Basic
open Data_base.Object
open Types.Base
open Types
open Files
open Lang

let read_option () =
  let num = ref 1 in
  let name = ref "" in
  let compiling = ref false and init = ref false in
  let keep_proof = ref false in
  let proof_general = ref false in
  let invisible_parenthesis = ref false in
  let short_answer = ref false in
  let pipe = ref None in
  let echo = ref false in
  while !num < Array.length Sys.argv do
    (match Sys.argv.(!num) with
      "-c" -> compiling := true
    | "-f" -> keep_proof := true
    | "-init" -> init := true
    | "-echo" -> echo := true
    | ("-pipe" | "-file") as s ->
	num:=!num+1;
	if !num >= Array.length Sys.argv then
	  failwith "open \"-pipe\" need an argument";
        let filename = Sys.argv.(!num) in
	(try
          if s = "-pipe" then Unix.mkfifo filename 384;
          pipe := Some (open_out filename)
	with Sys_error _ | Unix.Unix_error _ ->
          failwith ("can not open file: "^filename));
    | "-pg" -> proof_general := true
    | "-ip" -> invisible_parenthesis := true
    | "-r" -> recursive := true
    | "-s" -> short_answer := true
    | "-I" ->
	num:=!num+1;
	if !num >= Array.length Sys.argv then
	  failwith "open \"-I\" need an argument";
        add_path Sys.argv.(!num)
    | "-lang" ->
	num:=!num+1;
	if !num >= Array.length Sys.argv then
	  failwith "open \"-lang\" need an argument";
        set_language Sys.argv.(!num)
    | s -> name := s);
    num:=!num+1
  done;
  set_path ();
  let n = String.length !name in
  if n = 0 then begin
    if !compiling then failwith "You must specify a file to compile.";
    ref false, !init, !keep_proof, !proof_general, !invisible_parenthesis, !short_answer, "", "", "", "", !echo, !pipe
  end else if n < 5 then raise (
      Failure ("Don't know what to do with file " ^ !name))
  else begin
    let prefix = Filename.chop_extension !name in
    let basename = Filename.basename prefix in
    let dirname = Filename.dirname prefix in
    if !compiling || !init then begin
      if not (Filename.check_suffix !name "phx") then raise (
        Failure ("Don't know what to do with file " ^ !name));
      ref true, !init, !keep_proof, !proof_general, !invisible_parenthesis, !short_answer, dirname, basename^".phx", "", basename, !echo, !pipe
    end else begin
      if not (Filename.check_suffix !name "pho") then raise (
        Failure ("Don't know what to do with file " ^ !name));
      ref false, !init, !keep_proof, !proof_general , !invisible_parenthesis, !short_answer, "", "", basename^".pho", basename, !echo, !pipe
    end
  end




let compiling, init, keep_proof, proof_general ,  invisible_parenthesis, short_answer, dirname, input_name, base_name, root, print_echo, pipe_exit =
  try
    read_option ()
  with
    Failure s -> open_hbox (); print_string "Failure: ";print_string s;
                 print_newline (); exit 2
