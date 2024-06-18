(* $State: Exp $ $Date: 2006/02/24 17:01:54 $ $Revision: 1.5 $ *)
(*######################################################*)
(*			proof_general.ml		*)
(*######################################################*)

open Basic
open Lang
open Type
open Parse_base
open Lambda_util
open Interact
open Af2_basic
open Local
open Format
open Pattern
open Flags
open Print
open Rewrite
open Typing
open Typunif

let is_definition n s =
  begin
    try
      set_local (n-1);
      let e = aobj(sym_get s) in
      let k = type_check e in
      if equal_kind k kTheorem then print_string "false" else
      match e with
	EAtom(o,_) ->
	  (match get_value o with
	    Def _ ->
	      if not (!fis_close o) then print_string "true" else print_string "false";
	      print_newline ()
	  | _ -> raise Exit)
      | _ -> raise Exit
    with Exit | Not_found -> (* FIXME, was a catch all *)
	print_string "false";
	print_newline ()
  end;
  set_local 0

let is_equation n s =
  begin
    try
      set_local (n-1);
      let e = expr_of_string s in
      let e = match e with
	EAtom(oe,_) -> (
	  match get_value oe with
	    Def(EApp(EApp(EAtom(o,_),e'),_)) ->
	      if o == theorem_obj then e'
	      else e
	  | _ -> e)
      | e -> e
      in
      let fn (e1,e2,_,_,_,_) =
	let o1,_ = head e1 and o2,_ = head e2 in
	(o1 != Alleq) || (o2 != Alleq)
      in
      let l = List.filter fn (fst (decompose_eq [] e)) in
      if l = [] then raise Exit;
      print_string "true";
      print_newline ();
    with
      Exit | Not_found -> (* FIXME *)
	print_string "false";
	print_newline ()
  end;
  set_local 0


let is_hypothesis n s =
  try
    match !cur_proof with
      A_proof ({remain = remain; _}) ->
	let (gl, _) = List.nth remain (n-1) in
	ignore (List.assoc s gl.hyp);
	print_string "true";
	print_newline ();
    | _ -> raise Exit
  with
    Exit | Not_found | Failure _ -> (* FIXME *)
      print_string "false";
      print_newline ()

let is_locked n =
  if Set.mem n !nomatch_set then
    print_string "true"
  else
    print_string "false";
  print_newline ()



let first = ref true
let reset_first () = first := true

let strong_eq gl st e1 e2 =
  let (subst,_,_,_) =  get_ulocal () in
  if has_uvar subst e2 || has_uvar subst e1 then equal_expr e1 e2 else
  let tri = {nlim = 0; eqlvl = 1;
             from_trivial = false; first_order = true;
	     auto_elim = true; eqflvl = !eqflvl}
  in
  try
    ignore (pmatch gl.eqns gl.local false false (tri,call_trivial, (gl,st,[])) e1 e2);
    true
  with
    Fail_matching | Ill_rule _ ->
      false

let hyps_to_opt gl hyps =
  try
    let l = List.map (fun s ->
      let e' = expr_of_string s in
      let k = type_check e' in
      let rec fn = function
	  [] -> s, e'
	| (s,(e,_,_,_,_))::_ when equal_expr e e' ->
	    s, expr_of_string s
	| _::l -> fn l
      in
      let s, e' = fn gl.hyp in
      s, NOptFl(e',k)) hyps
    in
    let strings, opts = List.split l in
    strings, if opts = [] then [] else [opts]
  with
    _ -> raise Exit

let menu_cmd eqstrong prefix make_cmd do_rule n =
  let margin = get_margin () in
  let total = ref 0 in
  try
    let goal_prefix = if n = 1 then "" else "["^string_of_int n^"] " in
    let n = n - 1 in
    set_local n;
    set_margin 75;
    match !cur_proof with
      A_proof ({remain = remain; _}) ->
	let (goal, st) = List.nth remain n in
	let l = make_cmd goal_prefix goal st in
	let tri = {nlim = !pgtrdepth; eqlvl = !eqdepth;
               	from_trivial = false; first_order = true;
		auto_elim = true; eqflvl = !eqflvl}
	in
	let fn (cmd, opt) =
	  let mark = store_mark "" in
          let save_local = !cur_local in
	  let vvar = get_vvar () in
	  begin try
	    let (nr,_) = do_rule tri opt goal st in
	    let (nr,_) = try_axiom false !auto_lvl nr [] in
	    List.iter (fun x -> var_sat (fst x)) nr;
	    let count = ref 0 in
	    let gn (ngl, nst) =
	      cur_local := ngl.local;
	      let new_hyps =
		List.filter (fun (s,(e,_,_,_,_)) ->
		  try
		    let (e',_,_,_,_) = List.assoc s goal.hyp in
			    not (equal_expr e e')
		  with Not_found -> true) ngl.hyp
	      in
	      let defs = (List.filter (fun (s,_) -> not (List.mem_assoc s goal.local.cst_def))
		  ngl.local.cst_def) in
	      let vars = ref [] in
	      for i = vvar to get_vvar () - 1 do
		vars := ("?"^(string_of_int i)) :: !vars;
	      done;
	      let vars = List.rev !vars in
	      let hyps = List.map (fun (s,(e,_,_,_,_)) -> (s,e)) new_hyps in
	      let concl =
		if (if eqstrong then strong_eq ngl nst else equal_expr) goal.concl ngl.concl then
		  None
		else
		  Some ngl.concl
	      in
	      incr count;
	      ngl,!count, defs, vars, hyps, concl
	    in
	    let r = List.map gn nr in
	    if List.exists (fun (_,_,_,_,hy,cl) -> cl = None && hy = []) r
	    then raise Exit;
	    begin match r with
	      [] ->
		if !first then first := false else print_string "\\\\";
		print_string (get_message `Immediat);
		print_string "\\-";
		print_string cmd;
	    | (gl1,n1,c1,v1,h1,cl1)::other ->
		let rec fn fc1 c1 other =
		  try
		    match c1 with
		      [] -> raise Exit
		    | x::l ->
			fn (x::fc1) l (List.map (fun (gl,n,c,v,h,cl) ->
			  match c with
			    [] -> raise Exit
			  | y::l' -> if x = y then (gl,n,l',v,h,cl) else raise Exit) other)
		  with
		    Exit -> fc1, c1, other
		in
		let fc, c1, other = fn [] c1 other in
		let rec fn fv1 v1 other =
		    try
		      match v1 with
			[] -> raise Exit
		      | x::l ->
			  fn (x::fv1) l (List.map (fun (gl,n,c,v,h,cl) ->
			    match v with
			      [] -> raise Exit
			    | y::l' -> if x = y then (gl,n,c,l',h,cl) else raise Exit) other)
		    with
		      Exit -> fv1, v1, other
		in
		let fv, v1, other = fn [] v1 other in
		let rec fn fh1 h1 other =
		    try
		      match h1 with
			[] -> raise Exit
		      | (_,x as c)::l ->
			  fn (c::fh1) l (List.map (fun (gl,n,c,v,h,cl) ->
			    match h with
			      [] -> raise Exit
			    | (_,y)::l' when equal_expr x y -> (gl,n,c,v,l',cl)
			    | _::_ -> raise Exit) other)
		    with
		      Exit -> fh1, h1, other
		in
		let fh, h1, other = fn [] h1 other in
	        let all = List.sort
		    (fun (_,_,_,_,_,cl1) (_,_,_,_,_,cl2) -> match cl1, cl2 with
		      None, None -> 0
	            | Some _, Some _ -> 0
		    | None, Some _ -> 1
		    | Some _, None -> -1)
		    ((gl1,n1,c1,v1,h1,cl1)::other)
		in
		let fn (gl,n,c,v,h,cl) =
		  let defs = gl.local in
		  let gn (s,e as tpl) =
		    if List.mem tpl fc then [("\\{"^s^"\\}", e);(s,e)]
		    else if List.mem tpl c then [("\\{"^s^"\\|"^string_of_int n^"\\}", e);(s,e)]
		    else [tpl]
		  in
		  let defs = {defs with cst_def = List.flatten
				(List.map gn defs.cst_def)} in
		  if n = 1 then cur_local := defs;
		  (defs,n,c,v,h,cl)
		in
		let all = List.map fn all in
	        (* printing starts here *)
		let fn mot sep1 sep2 pn l =
		  match l with
		    [] -> ()
		  | (x::l) ->
		      let remain = ref (List.length l) in
		      if mot <> "" then (print_string mot; print_space ()); pn !remain x;
		      let rec gn l = decr remain; match l with
			[] -> ()
		      | [y] -> printf sep2; pn !remain y;
		      | y::l -> printf sep1; pn !remain y; gn l
		      in gn l
		in
		if !first then first := false else print_string "\\\\";
		print_flush ();
		open_hovbox 3;
		if prefix <> "" then begin
		  print_string prefix;
		  print_space ()
		end;
		let backstring n _ (s,_) = print_string
		    ("\\["^s^(if n = 0 then "" else "\\|"^string_of_int n)^"\\]") in
		let print_hyp n _ (s,e) =
		  print_expr e; print_space (); print_string
		    ("[\\["^s^(if n = 0 then "" else "\\|"^string_of_int n)^"\\]]")
		in
		fn (get_message `Let) ",@ " (get_format `And) (backstring 0) fc;
		if fc <> [] then print_space ();
		fn (get_message `LookFor) ",@ " (get_format `And) (fun _ -> print_string) fv;
		if fv <> [] then print_space ();
		let all_none = List.filter (fun (_,_,_,_,_,cl) -> cl = None) all in
		let nb_none = List.length all_none in
		let verb = if nb_none = 1 &&
		  List.for_all (fun (_,_,_,_,_,cl) -> cl = None) all then
		  match fc with
		    [] -> (get_message `WeHave)
		  | [_] -> (get_message `SuchThat)
		  | _ ->  (get_message `SuchThatS) else
		  match fv with
		    [] -> (get_message `Assume)
		  | [_] -> (get_message `SuchThat)
		  | _ ->  (get_message `SuchThatS)
		in
		fn verb ",@ " (get_format `And) (print_hyp 0) fh ;
		if fh <> [] then print_space ();
		let case = ref false in
		fn "" (get_format `Then) (get_format `Then)
		  (fun remain (defs,n,c,v,h,cl) ->
		  open_hovbox 2;
		  cur_local := defs;
		  if not !case && cl = None && remain >= 1 then begin
		    (printf (get_format `Cases) (remain + 1) : unit);
		    case := true;
		  end;
		  fn (get_message `Let) ",@ " (get_format `And) (backstring n) c;
		  if c <> [] then print_string " ";
		  fn (get_message `LookFor) ",@ " (get_format `And) (fun _ -> print_string) v;
		  if v <> [] then print_string " ";
		  let verb = if nb_none = 1 && cl = None then
		    match fc with
		      [] -> (get_message `WeHave)
		    | [_] -> (get_message `SuchThat)
		    | _ ->  (get_message `SuchThatS) else
		    match fv with
		      [] -> (get_message `Assume)
		    | [_] -> (get_message `SuchThat)
		    | _ ->  (get_message `SuchThatS)
		  in
		  fn verb ",@ " (get_format `And) (print_hyp n) h;
		  if h <> [] then print_string " ";
		  begin match cl with
		    None -> ()
		  | Some e ->
		      print_string (match fv with
			[] -> (get_message `Prove)
		      | [_] -> (get_message `SuchThat)
		      | _ ->  (get_message `SuchThatS));
		      print_space ();
		      print_expr e
		  end;
		  close_box ())
		  all;
		print_flush ();
		print_string "\\-";
		print_string cmd;
	    end;
	    restore_to mark;
	    cur_local := save_local;
	    incr total
	  with
	    Exit | Not_found | Failure _ ->
	      cur_local := save_local;
	      restore_to mark;
	  end;
	in
	List.iter fn l;
	close_box ();
	print_flush ();
	set_margin margin;
	!total
    | _ -> raise Exit
  with
    Exit ->
      close_box ();
      print_flush ();
      !total

let tri_opt () = " [ -lim "^(string_of_int !pgtrdepth)^"] "

let menu_evaluate n =
  reset_first ();
  let mark = store_mark "" in
  let save_local = !cur_local in
  try match !cur_proof with
    A_proof ({remain = remain; _}) ->
      set_local (n - 1);
      let (gl, st) = List.nth remain (n-1) in
      let tri = {nlim = 1; eqlvl = !eqdepth;
               	 from_trivial = false; first_order = true;
		 auto_elim = true; eqflvl = !eqflvl}
      in
      let goal_prefix = if n = 1 then "" else "["^string_of_int n^"] " in
      let (gl1,_) =
        match rule_rewrite tri [true, false, sym_get "eval"] Ad_lib false false gl st with
        | [gl1,st1],_ -> (gl1,st1)
        | _ -> assert false
      in
      if !first then first := false else print_string "\\\\";
      open_hovbox 2;
      print_expr gl.concl;
      print_space ();
      print_string (get_message `Computes);
      print_space ();
      print_expr gl1.concl;
      close_box ();
      print_string "\\-";
      print_string (goal_prefix^"evaluate"^tri_opt ());
      print_flush ();
      cur_local := save_local;
      restore_to mark;
      1
  | _ -> 0
  with _ ->
    cur_local := save_local;
    restore_to mark;
    0

let menu_evaluate_hyp n hypname =
  reset_first ();
  let mark = store_mark "" in
  let save_local = !cur_local in
  try match !cur_proof with
    A_proof ({remain = remain; _}) ->
      set_local (n - 1);
      let (gl, st) = List.nth remain (n-1) in
      let (e,_,_,_,_) = List.assoc hypname gl.hyp in
      let tri = {nlim = 1; eqlvl = !eqdepth;
               	 from_trivial = false; first_order = true;
		 auto_elim = true; eqflvl = !eqflvl}
      in
      let goal_prefix = if n = 1 then "" else "["^string_of_int n^"] " in
      let (gl1,_) =
        match  rule_rewrite_hyp tri [true, false, sym_get "eval"]
                                hypname Ad_lib false false gl st with
        | [gl1,st1],_ -> (gl1,st1)
        | _ -> assert false
      in
      let (e',_,_,_,_) = List.assoc hypname gl1.hyp in
      if !first then first := false else print_string "\\\\";
      open_hovbox 2;
      print_expr e;
      print_space ();
      print_string (get_message `Computes);
      print_space ();
      print_expr e';
      close_box ();
      print_string "\\-";
      print_string (goal_prefix^"evaluate_hyp "^hypname^" "^tri_opt ());
      print_flush ();
      cur_local := save_local;
      restore_to mark;
      1
  | _ -> 0
  with _ ->
    cur_local := save_local;
    restore_to mark;
    0

let make_cmd_intro ahyps goal_prefix gl _ =
  let hyps, opts = hyps_to_opt gl ahyps in
  let b, l = get_intros false
      gl.eqns gl.local true gl.concl in
  let l = List.map fst l in
  let l = if b then l@[""] else l in
  let r =   List.map (
    fun s ->
      let w = if hyps = [] then "" else
      " with "^List.fold_right
		  (fun x a -> x^(if a = "" then "" else (" and "^a))) hyps ""
      in
      let sw = if s = "" then s else "["^s^w^"]" in
      goal_prefix^"intro"^tri_opt ()^" "^sw, Names [s,Some opts])
      l
  in
  if ahyps = [] then (goal_prefix^"intros"^tri_opt (), Default)::r else r

let menu_intro n hyps =
  reset_first ();
  menu_cmd true "" (make_cmd_intro hyps) (rule_intro (ref false)) n

let make_cmd_left hypname goal_prefix gl _ =
  try
    let _,_,_,_,l = get_lefts None false Default hypname gl in
    (goal_prefix^"lefts"^tri_opt ()^" "^hypname, Default) ::
    List.map (fun x -> let s = fst (fst x) in
    goal_prefix^"left"^tri_opt ()^" "^hypname^" ["^s^"]", if s <> "" then Names [s,Some []] else RNum 1) l
  with
    _ -> []

let menu_left hypname n =
  reset_first ();
  menu_cmd true ((get_message `From)^" "^hypname^",") (make_cmd_left hypname)
    (fun tri opt -> rule_left tri hypname opt None) n

let make_cmd_elim hypname goal_prefix _ _ =
  [(goal_prefix^"elim"^tri_opt ()^" "^hypname, [])]

let make_cmd_elim_case hypname goal_prefix _ _ =
  [(goal_prefix^"elim"^tri_opt ()^" -1 [case] "^hypname, [1, OptDf("case",[])] )]

let make_cmd_elim_rec hypname goal_prefix _ _ =
  [(goal_prefix^"elim"^tri_opt ()^" -1 [rec] "^hypname, [1, OptDf("rec",[])] )]

let make_cmd_axiom hypname goal_prefix _ _ =
  [goal_prefix^"from"^tri_opt ()^" "^hypname, ()]

let make_cmd_demorgan hypname goal_prefix _ _ =
  [goal_prefix^"rewrite_hyp "^hypname^" "^tri_opt ()^" demorganl", Ad_lib;
   goal_prefix^"rewrite_hyp "^hypname^" "^tri_opt ()^" -l 1 demorganl", Lim 1]

let make_cmd_rewrite hyps goal_prefix _ _ =
  [goal_prefix^"rewrite"^tri_opt ()^" -ortho "^List.fold_right
       (fun x a -> x^(if a = "" then "" else " ")^a) hyps "", (Ortho [], true);
   goal_prefix^"rewrite"^tri_opt ()^" -l 1 "^List.fold_right
       (fun x a -> x^(if a = "" then "" else " ")^a) hyps "", (Lim 1, true);
   goal_prefix^"rewrite"^tri_opt ()^" -ortho "^List.fold_right
       (fun x a -> "-r "^x^(if a = "" then "" else " ")^a) hyps "", (Ortho [], false);
   goal_prefix^"rewrite"^tri_opt ()^" -l 1 "^List.fold_right
       (fun x a -> "-r "^x^(if a = "" then "" else " ")^a) hyps "", (Lim 1, false)]

let make_cmd_rewrite_hyp hypname hyps goal_prefix _ _ =
  [goal_prefix^"rewrite_hyp "^hypname^" "^tri_opt ()^" -ortho "^List.fold_right
       (fun x a -> x^(if a = "" then "" else " ")^a) hyps "", (Ortho [], true);
   goal_prefix^"rewrite_hyp "^hypname^" "^tri_opt ()^" -l 1 "^List.fold_right
       (fun x a -> x^(if a = "" then "" else " ")^a) hyps "", (Lim 1, true);
   goal_prefix^"rewrite_hyp "^hypname^" "^tri_opt ()^" -ortho "^List.fold_right
       (fun x a -> "-r "^x^(if a = "" then "" else " ")^a) hyps "", (Ortho [], false);
   goal_prefix^"rewrite_hyp "^hypname^" "^tri_opt ()^" -l 1 "^List.fold_right
       (fun x a -> "-r "^x^(if a = "" then "" else " ")^a) hyps "", (Lim 1, false)]

let menu_elim hypname n =
  reset_first ();
  set_local (n - 1);
  let hypexpr = expr_of_string hypname in
  let prefix = (get_message `From)^" "^hypname^"," in
  let did_rec =
    try
      match !cur_proof with
	A_proof ({remain = remain; _}) ->
	  let (gl, _) = List.nth remain (n-1) in
	  let (ehyp,_,_,_,_) = List.assoc hypname gl.hyp in
	  let hypstring = print_to_string print_expr ehyp in
	  let prefix = (get_message `Induction)^" "^hypstring^"," in
	  menu_cmd true prefix
	    (make_cmd_elim_rec hypname)
	    (fun tri opt ->
	      rule_elim false tri false false true opt 1 hypexpr) n
      | _ -> raise Not_found
    with Not_found | Exit | Failure _ -> 0
  in
  did_rec +
  (if did_rec > 0 then 0 else menu_cmd true prefix
    (make_cmd_elim hypname)
    (fun tri opt ->
      rule_elim false tri false false false opt 1 hypexpr) n) +
  menu_cmd true prefix
    (make_cmd_elim_case hypname)
    (fun tri opt ->
      rule_elim false tri false false true opt 1 hypexpr) n +
  menu_cmd true prefix
    (make_cmd_axiom hypname)
    (fun tri _ -> rule_elim false tri false false true [] 0 hypexpr) n +
  menu_cmd true prefix
      (make_cmd_demorgan hypname)
      (fun tri opt -> rule_rewrite_hyp tri [true, false, sym_get "demorganl"] hypname opt false true) n +
  menu_cmd false prefix
      (make_cmd_rewrite [hypname])
      (fun tri opt -> rule_rewrite tri [snd opt, false, sym_get hypname] (fst opt) false true) n


let make_cmd_apply hypname hyps goal_prefix _ _ =
  [goal_prefix^"apply"^tri_opt ()^" "^hypname^" with "^List.fold_right
       (fun x a -> x^(if a = "" then "" else (" and "^a))) hyps "", ()]

let make_cmd_elim_with hypname hyps goal_prefix _ _ =
  [goal_prefix^"elim"^tri_opt ()^" "^hypname^" with "^List.fold_right
       (fun x a -> x^(if a = "" then "" else (" and "^a))) hyps "", ()]

let menu_apply hypname hyps n =
  set_local (n-1);
  try
    reset_first ();
    let prefix = (get_message `From)^" "^hypname^" "^(get_message `With)^
      " "^List.fold_right
	     (fun x a -> x^(if a = "" then "" else ((get_message `AndS)^a))) hyps ""^" "
    in
    let hyps, opts =
      match !cur_proof with
	A_proof ({remain = remain; _}) ->
	  let (gl, _) = List.nth remain (n-1) in
	  hyps_to_opt gl hyps
      | _ -> raise Exit
    in
    menu_cmd true prefix
      (make_cmd_apply hypname hyps)
      (fun tri _ gl st ->
	let e = expr_of_string hypname in
	rule_apply tri "" [0, OptWith opts] 1 e gl st) n +
      menu_cmd true prefix
      (make_cmd_elim_with hypname hyps)
      (fun tri _ gl st ->
	let e = expr_of_string hypname in
	rule_elim  false tri false false false [0, OptWith opts] 1 e gl st) n
  with Exit -> 0

let menu_rewrite hyps n =
  try
    reset_first ();
    let hyps, _ =
      match !cur_proof with
	A_proof ({remain = remain; _}) ->
	  let (gl, _) = List.nth remain (n-1) in
	  hyps_to_opt gl hyps
      | _ -> raise Exit
    in
    let prefix = (get_message `From)^" "^List.fold_right
						(fun x a -> x^(if a = "" then "" else ((get_message `AndS)^a))) hyps ""^" "
    in
    menu_cmd false prefix
      (make_cmd_rewrite hyps)
      (fun tri opt -> rule_rewrite tri (List.map (fun hyp -> snd opt, false, sym_get hyp) hyps)
	  (fst opt) false true) n
  with Exit -> 0

let menu_rewrite_hyp hypname hyps n =
  try
    reset_first ();
    let hyps, _ =
      match !cur_proof with
	A_proof ({remain = remain; _}) ->
	  let (gl, _) = List.nth remain (n-1) in
	  hyps_to_opt gl hyps
      | _ -> raise Exit
    in
    let prefix = (get_message `From)^" "^hypname^" "^
      (get_message `With)^" "^
      List.fold_right
	(fun x a -> x^(if a = "" then "" else ((get_message `AndS)^a))) hyps ""^" "
    in
    menu_cmd false prefix
      (make_cmd_rewrite_hyp hypname hyps)
      (fun tri opt -> rule_rewrite_hyp tri (List.map (fun hyp -> snd opt, false, sym_get hyp) hyps)
	  hypname (fst opt) false true) n
  with Exit ->
    0
