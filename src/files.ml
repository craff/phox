(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.6 $ *)
(*######################################################*)
(*			files.ml			*)
(*######################################################*)

open Format
open Version
open Type
(* ouverture de type pour l'exception Error,
   a par ca ce fichier est portable *)

exception Quit

let cur_input = ref stdin
let cur_line = ref 1
let cur_col = ref 0

let stack_input = ref ([]:(in_channel * int * int) list)

let pop_input0 = function
  (c,lin,col)::s ->
    close_in !cur_input;
    cur_input := c;
    cur_line := lin;
    cur_col := col;
    stack_input := s
|  [] ->
    raise Quit

let is_top () = !stack_input = []

let pop_input () = (pop_input0 !stack_input)

let pop_all () =
  while (!stack_input <> []) do
    pop_input ()
  done

let path_list = ref []
let ext = ".phx"

let open_path filename =
  try open_in filename with Sys_error _ ->
  try open_in (filename^ext) with Sys_error _ ->
  let rec fn = function
    [] ->
      open_hbox ();
      print_string "File error: impossible to open file \"";
      print_string filename;
      print_string "\".";
      print_newline ();
      raise Error
  | path::l ->
     try
       open_in (Filename.concat path filename)
     with Sys_error _ ->
       try open_in (Filename.concat path (filename^ext))
     with Sys_error _ -> fn l
  in fn !path_list

let read_file filename =
  let old_input = !cur_input in
  cur_input := open_path filename;
  stack_input := (old_input,!cur_line,!cur_col)::!stack_input;
  cur_line := 1;
  cur_col := 0

let print_path () =
  open_vbox 0;
  print_string "Here is the path list:";
  print_cut ();
  List.iter (fun x -> print_string x; print_cut ()) !path_list;
  print_newline ()

let add_path s =
  if not (List.mem s !path_list) then path_list := s::!path_list

let split str c =
  let l = ref [] and s = ref 0 in
  for i = 0 to String.length str - 1 do
    if str.[i] = c then begin
      l := String.sub str !s (i - !s) :: !l;
      s:=i+1;
    end
  done;
  if String.length str > !s then
    l := String.sub str !s (String.length str - !s) :: !l;
  !l

let set_path () =
  if !path_list = [] then begin
    try
      let path = Sys.getenv "PHOXPATH" in
      List.iter add_path (split path delim)
    with Not_found ->
      List.iter add_path (split default_path delim)
  end
