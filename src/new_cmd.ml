open Type
open Lex
open Parse_base
open Lambda_util
open Af2_basic
open Interact
open Local
open Print
open Pattern
open Flags
open Af2_logic

type idorexp = Id of string | Ex of expr

type new_cmd =
    Let of (string * kind * new_cmd)
  | Def of (string * expr * new_cmd)
  | Assume of (bool * string * expr * new_cmd)
  | End of proof_cmd
  | Show of expr * proof_cmd
  | Cases of new_cmd list
  | Search of string * new_cmd
  | By of idorexp * new_elim_option list list * new_cmd

and proof_cmd =
    Trivial
  | Unfinished
  | Rule of new_cmd

let rec parse_exprlist tstr = match tstr with parser
    [< 'Kwd "[";
       'Ident str ?? serror "an identifier" tstr;
       lo = parse_with;
       'Kwd "]" ?? serror "]" tstr;
       l = parse_exprlist' >] ->
      (match l with
	l::ls -> (NOptDf(str,lo)::l)::ls
      | [] -> [[NOptDf(str,lo)]])
  | [< e = parse_free_expr; l = parse_exprlist' >] ->
      let k = mk_Var () in
      match l with
	l::ls -> (NOptFl(e,k)::l)::ls
      | [] -> [[NOptFl(e,k)]]
and parse_exprlist' = parser
    [< 'Ident "and"; suit >] -> parse_exprlist suit
  | [< 'Ident "then"; suit >] -> []::(parse_exprlist suit)
  | [< >] -> []

and parse_with = parser
  [< 'Ident "with"; l = parse_exprlist >] -> l
| [< >] -> []

let maybe_name = parser
    [< 'Kwd "["; 'Ident s; 'Kwd "]" >] -> s
  | [< 'Ident "named"; 'Ident s >] -> s
  | [<>] -> ""

let maybe_expr = parser
    [< 'Kwd "["; 'Ident s; 'Kwd "]" >] -> Id s
  | [< e = parse_expr >] -> Ex e

let rec parse_list_aux f l = parser
    [< 'Ident "and"; l = parse_list f l >] -> l
  | [< >] -> l
and parse_list f l = parser
    [< x = f ; l' = parse_list_aux f (x::l) >] -> l'

let parse_named_expr = parser
    [<  e = parse_free_expr; s = maybe_name >] -> e,s

let rec parse_newcmd _accept_empty strm =
  let cmd = match strm with parser
    [< 'Ident "begin"; cmd = parse_newcmd false; 'Ident "end" >] -> cmd
  | [< 'Ident ("assume" | "deduce" as str); l = parse_list parse_named_expr [];
       cmd = parse_newcmd true >] ->
	 List.fold_left (fun cmd (e,s) -> Assume(str = "assume", s, e, cmd)) cmd l
  | [< 'Ident "let";
       l =
         (fun st ->
	   inlet := true;
	   try
	     let r = parse_list (
	       parse_bind (0,Coma (EVar 0), Semi (EVar 0))) [] st in
	     inlet := false;
	     r
	   with
	     e -> inlet := false; raise e);
       cmd = parse_newcmd true >] ->
	 List.fold_left (fun cmd (ls,_,ass) ->
	   List.fold_left (fun cmd s ->
	     match ass with
	       Noass -> Let (s,mk_Var (),cmd)
	     | Ass t -> Let (s,t,cmd)
	     | IAss e ->
		 match e with
		   EApp(EAtom(o,_), e') when o = equal_obj ->
		     Def (s, e', cmd)
		 | _ ->
		     Let (s,mk_Var (),
			  Assume(true,"",
				 EApp(e, FVar s), cmd)))
	     cmd ls) cmd l
  | [< 'Ident "by"; s = maybe_expr; w = parse_with;
       cmd = parse_newcmd false >] ->
      By(s,w,cmd)
  | [< 'Ident "search";
       'Ident name;
       cmd = parse_newcmd false >] ->
      Search(name,cmd)
  | [< 'Ident "show"; e = parse_free_expr; p = parse_proof  >] ->
	Show (e, p)
  | [<  p = parse_proof >] -> End p
  in match cmd with End _ -> cmd | _ -> parse_nextcmd [cmd] strm

and parse_proof strm =
   match strm with parser
	[<  'Ident "trivial" >] -> Trivial
      | [<  'Kwd ";;" ; p = parse_proof' >] -> p
      | [< >] -> Unfinished

and parse_proof' strm =
   match strm with parser
	[<  'Ident "trivial" >] -> Trivial
      | [<  r =  parse_newcmd false >] -> Rule r
      | [< >] -> Unfinished


and parse_nextcmd cmds = parser
    [< 'Ident "then"; cmd' = parse_newcmd false; l = parse_nextcmd (cmd'::cmds) >] ->
      l
  | [< >] ->
      match cmds with
	[] -> assert false
      | [c] -> c
      | l -> Cases l

let rec interpret_newcmd cmd gl st =
  let save_local = !cur_local in
  let save_new_cmd_opt = !new_cmd_opt in
  cur_local := gl.local;
  new_cmd_opt := [];
  let lemmas = ref [] in
  let goal = gl.concl in
  let do_lock_intro = ref true in
  let local_lock_intro = ref [] in
  let rec fn = function
      End b -> [[], goal, b]
    | Show (e,b) ->
	do_lock_intro := false;
	local_lock_intro := e::!lock_intro;
	[[], e, b]
    | Cases l -> List.flatten (List.map fn l)
    | Let (s,k,l) ->
	List.map (fun (ls,e, b) -> s::ls,
	  EApp(EAtom(forall_obj, [k]),EAbs(s,e,k)), b)
	  (fn l)
    | Search(s,l) ->
	let k = mk_Var () in
	List.map (fun (ls,e, b) -> ""::ls,
	  EApp(EAtom(!exists_obj, [k]),EAbs(s,e,k)), b)
	  (fn l)
    | Def (s,a,l) ->
	List.map (fun (ls,e, b) ->
	  let k = mk_Var () in
	  s::ls,
	  EApp(EApp(EAtom(!let_obj, [k; mk_Var()]),a),EAbs(s,e,k)), b)
	  (fn l)
    | By(s,w,l) ->
	begin
	  let rec kn s = match s with
	    Id s ->
	      if not (List.mem_assoc s gl.hyp) then
		begin
		  lemmas := s::!lemmas;
		  s^"#local"
		end
	      else s
	  | Ex e ->
	      let rec gn = function
		  [] ->
		    begin
		      match e with
			EAtom(o,_) -> kn (Id (get_name o))
		      | FVar s -> kn (Id s)
		      | _ ->
			  raise (Ill_rule "by failed, expression
				   is not an hypothesis")
		    end
		| (s,(e',_,_,_,_))::_ when equal_expr e e' -> s
		| _::l -> gn l
	      in gn gl.hyp
	  in
	  new_cmd_opt := (kn s,w)::!new_cmd_opt
	end;
	fn l
    | Assume(_,s,h,l) ->
	local_lock_intro := h::!lock_intro;
	List.map (fun (ls,e, b) ->
	  s::ls, EApp(EApp(EAtom(arrow_obj,[]),h),e), b) (fn l)
  in
  try
    let l = fn cmd in
    let f = List.fold_left
	(fun e (_,g,_) -> EApp(EApp(EAtom(arrow_obj,[]),g),e)) goal l in
    if !do_lock_intro = true then local_lock_intro := goal::!local_lock_intro;
(*
    print_expr f;
    print_newline ();
*)
    let f =
      try
      bind_free false 0 [] f
      with Unbound s -> raise (Cant_bind [s])
    in

    print_expr f;
    print_newline ();

    let tri = {nlim = !trdepth; eqlvl = !eqdepth;
               from_trivial = false; first_order = false;
	       auto_elim = true; eqflvl = !eqflvl}  in
    let the_name =
      let rec fn = function
	(n,(e,_,_,_,_))::_ when equal_expr e f -> n
      |	_::l -> fn l
      | [] -> "NCMD#"
      in fn gl.hyp
    in
    let (gl1, st1), (gl2, st2) =
        match rule_use true tri "NCMD#" f gl st with
	  [c1;c2],[] -> c1,c2
        | _ -> assert false
    in
    let len = List.length l in
    let names = let x = ref 0 in List.map (fun _ -> incr x; ("NCMD#" ^ string_of_int !x)) l in
    let uses = List.fold_left (fun r s ->
      compose_rule r (rule_use false tri (s^"#local") (aobj (sym_get s))))
	no_rule !lemmas  in
    let local_lock_elim =
      let l' = List.map fst gl.hyp in
      List.filter (fun s -> not (List.mem_assoc s !new_cmd_opt)) l'
    in
    let lock_rule rule gl st =
      try
	if !do_lock_intro then lock_intro := !local_lock_intro;
	if local_lock_elim <> [] then lock_elim := local_lock_elim;
	let r = rule gl st in
	lock_intro := []; lock_elim := []; r
      with e ->
	lock_intro := []; lock_elim := []; raise e
    in
    let intro_opt = Names (List.map (fun s -> s,None) names) in
    let _, nl = compose_rule uses
	(compose_rule (rule_intro (ref false) tri intro_opt)
	   (lock_rule (if !newcmd_resolve then rule_resolve "n" else rule_trivial true [] [] {tri with nlim = tri.nlim + 2}))) gl1 st1
    in
    let hyp = aobj (List.assoc the_name gl2.local.caps_def) in
    let gls, nl' =
     rule_elim false tri false false false [] len hyp gl2 st2 in
    let gls = if the_name <> "NCMD#" then gls else List.map
	(function gl, st ->
	  match rule_rm true ["NCMD#"] gl st with
	    [gl,st], [] ->
	      gl, st | _ -> assert false) gls in
    let r =
      List.fold_left2 (
      fun (gls,nls) (gl, st) (names, _, try_trivial) ->
	let intro_opt = Names (List.map (fun s -> s,None) names) in
 	let gl,st as c=
	  match rule_intro (ref false) tri intro_opt gl st with
	    [gl,st], [] -> gl, st | _ -> assert false
	in
	match try_trivial with
	  Trivial ->
	    gls, snd (compose_rule uses (if !newcmd_resolve then rule_resolve "n" else rule_trivial true [] [] tri) gl st) @ nls
	| Unfinished ->
	  (c::gls), nls
	| Rule cmd ->
	    let save_opt = !new_cmd_opt in
	    begin try
	      let gls', nls' = interpret_newcmd cmd gl st in
	      gls@gls', nls@nls'
	    with
	      e ->
		new_cmd_opt := save_opt;
		raise e
	    end
      )
	([], nl'@nl) (List.rev gls) l
    in
    new_cmd_opt := [];
    cur_local := save_local;
    r
  with e ->
    print_string (Printexc.to_string e);
    print_newline ();
    new_cmd_opt := save_new_cmd_opt;
    cur_local := save_local;
    raise e
