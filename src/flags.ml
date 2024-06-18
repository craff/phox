(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.8 $ *)
(*######################################################*)
(*			flags.ml			*)
(*######################################################*)

open Format

type flag_value =
    Vint of int
|   Vbool of bool
|   Vstring of string
|   Vprint

type flag =
    Fint of int ref
|   Sint of (int -> unit) * (unit -> int)
|   Fbool of bool ref
(*|   Sbool of (bool -> unit) * (unit -> bool)*)
(*|   Fstring of string ref*)
|   Sstring of (string -> unit) * (unit -> string)

let get_val = function
  Fint p -> Vint !p
| Sint (_,f) -> Vint (f ())
| Fbool p -> Vbool !p
(*| Sbool (_,f) -> Vbool (f ())*)
(*| Fstring p -> Vstring !p*)
| Sstring (_,f) -> Vstring (f ())

let flag_list = ref ([] : (string * (flag * flag_value)) list)

let add_flag s f =
  flag_list := (s,(f,get_val f))::!flag_list

let get_flag s = fst (List.assoc s !flag_list)

let rec set_flag s0 v =
  try let ptr = get_flag s0 in
  match v,ptr with
    (Vint n), (Fint p) -> p := n; set_flag s0 Vprint
  | (Vint n), (Sint (set,_)) -> set n; set_flag s0 Vprint
  | (Vbool b), (Fbool p) -> p := b; set_flag s0 Vprint
  (*  | (Vbool b), (Sbool (set,get)) -> set b; set_flag s0 Vprint*)
  (*  | (Vstring s), (Fstring p) -> p := s; set_flag s0 Vprint*)
  | (Vstring s), (Sstring (set,_)) -> set s; set_flag s0 Vprint
  | (Vprint), (Fint p) ->
      open_hbox ();
      print_string s0;
      print_string " = ";
      print_int !p;
      print_newline ()
  | (Vprint), (Sint (_,get)) ->
      open_hbox ();
      print_string s0;
      print_string " = ";
      print_int (get ());
      print_newline ()
  | (Vprint), (Fbool b) ->
      open_hbox ();
      print_string s0;
      print_string (if !b then " = true" else " = false");
      print_newline ()
(*  | (Vprint), (Sbool (set,get)) ->
      open_hbox ();
      print_string s0;
      print_string (if get () then " = true" else " = false");
      print_newline ()*)
(*  | (Vprint), (Fstring p) ->
      open_hbox ();
      print_string s0;
      print_string " = \"";
      print_string (String.escaped !p);
      print_string "\"";
      print_newline ()*)
  | (Vprint), (Sstring (_,get)) ->
      open_hbox ();
      print_string s0;
      print_string " = \"";
      print_string (String.escaped (get ()));
      print_string "\"";
      print_newline ()
  | _ -> raise (Failure "bad val for this flag")
  with Not_found -> raise (Failure "Unknown flag")

let trace_trivial = ref false
let _ = add_flag "trace_trivial" (Fbool trace_trivial)

let trace_pmatch = ref false
let _ = add_flag "trace_pmatch" (Fbool trace_pmatch)

let trace_level = ref 1
let _ = add_flag "trace_level" (Fint trace_level)

let trace_eqres = ref false
let _ = add_flag "trace_eqres" (Fbool trace_eqres)

let trace_dist = ref false
let _ = add_flag "trace_dist" (Fbool trace_dist)

let min_tex_space = ref 20
let _ = add_flag "min_tex_space" (Fint min_tex_space)

let max_tex_space = ref 40
let _ = add_flag "max_tex_space" (Fint max_tex_space)

let comma_tex_space = ref 5
let _ = add_flag "comma_tex_space" (Fint comma_tex_space)

let binder_tex_space = ref 3
let _ = add_flag "binder_tex_space" (Fint binder_tex_space)

let tex_indent = ref 200
let _ = add_flag "tex_indent" (Fint tex_indent)

let trdepth = ref 4
let _ = add_flag "trivial_depth" (Fint trdepth)

let pgtrdepth = ref 1
let _ = add_flag "pg_trivial_depth" (Fint pgtrdepth)

let eqdepth = ref 100
let _ = add_flag "eq_depth" (Fint eqdepth)

let eqbreadth = ref 4
let _ = add_flag "eq_breadth" (Fint eqbreadth)

let eqflvl = ref 3
let _ = add_flag "eq_flvl" (Fint eqflvl)

let eqplvl = ref 5
let _ = add_flag "eq_plvl" (Fint eqplvl)

let auto_lvl = ref 0
let _ = add_flag "auto_lvl" (Fint auto_lvl)

let auto_type = ref false
let _ = add_flag "auto_type" (Fbool auto_type)

let _ = set_margin 80
let _ = add_flag "margin" (Sint(set_margin,get_margin))

let _ = set_max_indent 50
let _ = add_flag "max_indent" (Sint(set_max_indent,get_max_indent))

let _ = set_max_boxes 100
let _ = add_flag "max_boxes" (Sint(set_max_boxes,get_max_boxes))

let tex_margin = ref 60
let _ = add_flag "tex_margin" (Fint(tex_margin))

let tex_max_indent = ref 40
let _ = add_flag "tex_max_indent" (Fint(tex_max_indent))

let _ = set_ellipsis_text "..."
let _ = add_flag "ellipsis_text" (Sstring(set_ellipsis_text,get_ellipsis_text))
let tex_type_sugar = ref true
let _ = add_flag "tex_type_sugar" (Fbool tex_type_sugar)

let tex_infix_sugar = ref true
let _ = add_flag "tex_infix_sugar" (Fbool tex_infix_sugar)

let tex_lisp_app = ref true
let _ = add_flag "tex_lisp_app" (Fbool tex_lisp_app)

let debug_proof_check = ref false
let _ = add_flag "debug_proof_check" (Fbool debug_proof_check)

let print_sort = ref false
let _ = add_flag "print_sort" (Fbool print_sort)

let print_match_case = ref true
let _ = add_flag "print_match" (Fbool print_match_case)

let auto_left_lvl = ref 1
let _ = add_flag "auto_left_lvl" (Fint auto_left_lvl)

let new_distance = ref false
let _ = add_flag "new_distance" (Fbool new_distance)

let resol_verbose = ref 1
let _ = add_flag "resol_verbose" (Fint resol_verbose)

let cndats_max_length = ref 10
let _ = add_flag "cndats_max_length" (Fint cndats_max_length)

let cndats_max_weight = ref 5
let _ = add_flag "cndats_max_weight" (Fint cndats_max_weight)

let newcmd_resolve = ref false
let _ = add_flag "newcmd_resolve" (Fbool newcmd_resolve)

let reset_flags () =
  List.iter (function (_,(v,init)) ->
    match init,v with
      (Vint n), (Fint p) -> p := n
    | (Vint n), (Sint (set,_)) -> set n
    | (Vbool b), (Fbool p) -> p := b
    (*    | (Vbool b), (Sbool (set,get)) -> set b*)
    (*| (Vstring s), (Fstring p) -> p := s*)
    | (Vstring s), (Sstring (set,_)) -> set s
    | _ -> failwith "bug in reset_flags") !flag_list

type trace_save = bool * bool

let decr_trace_level () =
  let save = !trace_pmatch, !trace_trivial in
  decr trace_level;
  if !trace_level <= 0 then begin
    trace_pmatch := false;
    trace_trivial := false;
  end;
  if !trace_pmatch || !trace_trivial then begin
    print_string "entering trace level: ";
    print_int !trace_level;
    print_newline ();
  end;
  save

let incr_trace_level (p,t) =
  if !trace_pmatch || !trace_trivial then begin
    print_string "exiting trace level: ";
    print_int !trace_level;
    print_newline ();
  end;
  trace_pmatch := p;
  trace_trivial := t;
  incr trace_level
