open Bindlib
open Lex
open Lambda_exp
open Format

type pterm =
    PApp of pterm * pterm
  | PLam of string * pterm
  | PCro of string * pterm
  | PMu  of string * pterm
  | PVar of string
  | PSide of string


let defs =
  let name = "peirce_law" in
    ref [name, {name = name; value = cc}]

let output_all ?(kvm = false) () =
  let fn (_,t) =
    open_hovbox 2;
    print_string t.name;
    print_string " = ";
    if kvm then print_kvm_term t.value else print_term t.value ;
    close_box ()
  in
    List.iter fn (List.rev !defs)

let output ?(kvm = false) s =
  let t = List.assoc s !defs in
    open_hovbox 2;
  print_string t.name;
  print_string " = ";
  if kvm then print_kvm_term t.value else print_term t.value ;
  close_box ()

let outputs ?(kvm=false) l =
  if  l != []
  then List.iter (output ~kvm:kvm) l
  else output_all ~kvm:kvm ()
let cons_left a (l,l') = a::l, l'
let cons_right a (l,l') = l, a::l'

let get_def s = start_term (bDef (List.assoc s !defs))

let add_def s t =
  try
    (List.assoc s !defs).value <- t;
    print_string ("Warning: redefining " ^ s);
    print_newline ()
  with Not_found ->
    defs := (s,{name = s; value = t})::!defs

let del_def s =
  try
    let t = List.assoc s !defs in
      defs := List.remove_assoc s !defs;
      open_hovbox 2;
      print_string (s ^ " = ");
      print_term t.value;
      print_string " deleted.";
      close_box ();
      print_newline()
  with
      Not_found ->
	failwith (s ^ " is not defined!")

let del_def_all () =
  let name = "peirce_law" in
    if List.mem_assoc name !defs
    then ( defs :=  [name, {name = name; value = cc}] ;
	   print_string("All terms deleted except " ^ name ^".") )
    else ( defs :=  [] ; print_string ("All terms deleted.") );
    print_newline()


let del_defs l =
  if  l != []
  then List.iter del_def l
  else ignore(del_def_all())

let rec pterm_to_term env = function
    PApp(t1, t2) -> bApp (pterm_to_term env t1) (pterm_to_term env t2)
  | PLam(s, t) -> bLam (fun x -> pterm_to_term (cons_left (s, x) env) t)
  | PCro(s, t2) -> bCro (try List.assoc s (snd env) with Not_found ->
			   raise (Failure ("Unbound identifier: "^s)))
      (pterm_to_term env t2)
  | PMu(s, t) -> bMu (fun x -> pterm_to_term (cons_right (s, x) env) t)
  | PSide s -> unit (bSide s)
  | PVar s ->
      try List.assoc s (fst env) with Not_found ->
      try unit (get_def s) with Not_found ->
      raise (Failure ("Unbound identifier: "^s))

let rec parse_lambda_aux = parser
    [< 'Ident s >] ->
      PVar s
  | [< 'Kwd "\\"; 'Ident s; t = parse_lambda' >] ->
	PLam(s, t)
  | [< 'Kwd "µ"; 'Ident s; t = parse_lambda' >] ->
	PMu(s, t)
  | [< 'Str s >] ->
	PSide s
  | [< 'Lpar; t = parse_lambda'; 'Rpar >] -> t
  | [< 'Kwd "["; 'Ident s ; 'Kwd "]"; u = parse_lambda' >] -> PCro(s,u)


and parse_lambda' = parser
    [< t = parse_lambda_aux; v = parse_lambda'' t >] -> v

and parse_lambda'' u = parser
    [< t = parse_lambda_aux; v = parse_lambda'' (PApp(u,t)) >] -> v
  | [< >] -> u

let parse_lambda str =
  start_term (pterm_to_term ([],[]) (parse_lambda' str))
