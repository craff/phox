(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.50 $ *)
(*######################################################*)
(*			interact.ml			*)
(*######################################################*)

(* A NETOYER *)

open Basic
open Format
open Type.Base
open Type
open Parse_base
open Lambda_util
open Af2_basic
open Local
open Print
open Typunif
open Typing
open Safe_add
open Type_check
open Pattern
open Flags
open Undo
open Option

let do_add_rlocal name kind value sy gl0 st0 =
  let nlocal, o = add_rlocal gl0.local name kind value sy in
  let gl1 = {gl0 with gref = new_ref (); local = nlocal}
  and st1 = Fol {sref = gl0.gref;
                 rule = Decl_local_def (name,o); next = st0} in
  [gl1,st1], []

let do_add_csyntax n name sy gl0 st0 =
  let nlocal = add_local_ctex gl0.local n name sy in
  let gl1 = {gl0 with local = nlocal} in
  [gl1,st0], []

let do_add_syntax o name sy gl0 st0 =
  let nlocal = add_local_tex gl0.local o name sy in
  let gl1 = {gl0 with local = nlocal} in
  [gl1,st0], []

let do_add_close o gl0 st0 =
  let nlocal = add_local_close gl0.local o in
  let gl1 = {gl0 with gref = new_ref (); local = nlocal } in
  let st1 = Fol {sref = gl0.gref; rule = No_rule; next = st0} in
  [gl1,st1], []

let empty_done = [], [], Exprmap.empty

let singl_done (_,_,ad) e = [e], [], ad

let mem_expr in_elim e (l,l',_) =
  let e = norm_expr e in
  try
    let fn = fun x -> add_non_unif None [e, x] in
    List.iter fn l;
    if in_elim then (try List.iter fn l' with Non_unif -> raise Non_unif);
    false
  with Non_unif -> true

let emapadd e (l,l',ad) =
  (e::l), l', ad

let emapadd' e (l,l',ad) =
  l, (e::l'), ad

let can_open local o =
  not (!fis_close o) &&
  not (List.memq o local.local_close_tbl)

let adone (_,_,x) = x

let add_adone (l,l',ad) e n1 =
  l,l', Exprmap.add e n1 ad

exception Found of state list

type proof_state =
  {goal : expr;
   gpoly : int;
   remain : (goal*state) list;
   leaf : state list;
   pname : string option;
   ptex_name : string option;
   pexported : bool}

and new_elim_option =
    NOptFl of expr * kind
  | NOptDf of string * new_elim_option list list

and elim_option =
    OptFl of expr
  | OptDf of string * (int * elim_option) list
  | OptInt of string list
  | OptAfter of string
  | OptNoax
  | OptWith of new_elim_option list list

and proof =
    No_proof
  | A_proof of proof_state
  | To_save of sym_value * expr * int * string option * string option * bool

and arule = goal -> state -> (goal * state) list * state list

let ftrivial = ref (fun _ -> failwith "trivial not ready")

let _print_proof sl =
  print_newline ();
  let ard = ref [] in
  let rec fn = function
      Fin _ -> ()
    | Fol {sref = n1; rule = rule; next = next} ->
    	if List.mem n1 !ard then () else (
    	ard := n1::!ard;
    	Printf.printf "%d : " n1;
    	(match rule with
	  Axiom n ->
            Printf.printf "Axiom on hyp %d" n; print_newline ()
    	| Subgoal n ->
            Printf.printf "Sugoal on ref %d" n; print_newline ()
    	| No_rule ->
            Printf.printf "No_rule"; print_newline ()
	| In_rule _ ->
            Printf.printf "In_rule"; print_newline ()
    	| Arrow_intro (s,n,_) ->
            Printf.printf "Arrow_intro creating hyp %d(%s)" n s;
            print_newline ()
    	| Cut_rule (s,n,n',p) ->
            Printf.printf "Cut_rule creating hyp %d(%s) in %d, %d" p s n n';
            print_newline ()
    	| Forall_intro (s,n,_) ->
            Printf.printf "Forall_intro creating var %d(%s)" n s;
            print_newline ()
    	| Arrow_elim (n,n') ->
            Printf.printf "Arrow elim on ref %d and %d" n n'; print_newline ()
    	| Forall_elim (e,_) ->
            Printf.printf "Forall elim on object ";
            print_expr e; print_newline ()
    	| Fact_def _ ->
            Printf.printf "Factor definition of object"; print_newline ()
    	| Devl_def _ ->
            Printf.printf "Devl definition of object"; print_newline ()
    	| Lr_eqn _ ->
            Printf.printf "Lr eqn"; print_newline ()
    	| Rl_eqn _ ->
            Printf.printf "Rl eqn"; print_newline ()
    	| Decl_local_def _ -> ()
        | Comment s -> Printf.printf "Comment %s" s; print_newline ()
        | Claim e -> Printf.printf "Claim ";  print_expr e; print_newline ()
    	| Theo e ->
            Printf.printf "apply theorem"; print_expr e; print_newline ()); print_newline (); fn next)
  in List.iter fn sl

let lastopt = ref None
let lastcmp = ref None

let from_resol = ref None

let call_trivial tri ulocal (gl0,st0,nl0) lrg =
  match !from_resol with
    Some p ->
      p := List.map (fun (_,_,e) -> EApp(aobj !not_obj,e)) lrg @ !p;
      (ulocal, (gl0,st0,nl0))
  | None ->
  if tri.nlim < 0 then raise (Ill_rule "trlvl negatif");
(*
  let tri = {
  nlim = tri.nlim; eqlvl = tri.eqlvl;
  from_trivial = true; first_order = true;
  auto_elim = not tri.from_trivial;
  eqflvl = tri.eqflvl} in
*)
  let save = get_ulocal () in
  let l1 = !lastopt
  and l2 = !lastcmp in
  let pos = get_undo_pos () in
  try
    set_ulocal ulocal;
    let gn (ref1,st2,e) (glsts,gl0,st0,nl0) =
      if mem_expr false e gl0.done_list then
        raise (Ill_rule "ADone1");
      try
        let n = Exprmap.find e (adone gl0.done_list) in
        let stg = Fol {sref = ref1; rule = Subgoal n; next = st2} in
        let nl0 = stg :: nl0 in
        glsts,gl0,st0,nl0
      with Not_found ->
        let r1 = new_ref () and r2 = new_ref () and n1 = new_const () in
        let gl1 = {gl0 with gref = r1; concl = e;
                    done_list = emapadd e gl0.done_list} in
        let st1 = Fol {sref = gl0.gref;
                       	rule = Cut_rule ("Cut",r1,r2,n1); next = st0} in
        let ndone_list = add_adone gl0.done_list e n1 in
        let stg = Fol {sref = ref1; rule = Subgoal n1; next = st2} in
        let gl2 = {gl0 with gref = r2;
                    done_list = ndone_list} in
        let nl2 = stg :: nl0 in
        ((gl1,st1)::glsts),gl2,st1,nl2
    in
    let glsts,gl0,st0,nl0 =
      List.fold_right gn lrg ([],gl0,st0,nl0) in
    (* let us call trivial ! *)
    let _, nlp = !ftrivial tri glsts in
    let nulocal = get_ulocal () in
    let r = (nulocal, (gl0, st0, nlp @ nl0 )) in
    set_ulocal save;
    lastopt := l1; lastcmp:=l2;
    r
  with exn ->
    do_undo pos;
    set_ulocal save;
    lastopt := l1; lastcmp:=l2;
    raise exn

let hyp_to_rule n = function
    Hypo -> Axiom n
  | Subg -> Subgoal n
  | Theor th -> Theo th

let hyp_to_erule e n = function
    Hypo -> Eq_axiom (e,n)
  | Subg -> Eq_subgoal (e,n)
  | Theor (EAtom(o,_)) -> Eq_theo o
  | _ -> failwith "bug in hyp_to_erule"

let cur_proof = ref No_proof

type store_stack = (proof * int * (int * kind) list * contxt * string * undo_pos) list
let save_stack =
  ref ([]:store_stack)

let set_local n =
  try match !cur_proof with
    A_proof {remain = nr; _} ->
      cur_local := (fst (nth_try n nr)).local;
      cur_env := n
  | _ ->
      cur_local := empty_local;
      cur_env := 0
  with Not_found ->
    if n > 0 then failwith ("No goal number "^string_of_int n)
    else (cur_local := empty_local; cur_env := 0)


let rec var_sat_expr = function
    UVar (n,k) ->
      (try var_sat_expr (getuvar n)
      with Not_found ->
      	if n < 0 then begin
          let n' = new_vvar () in
          vvar_kind := (n',k)::!vvar_kind;
          def_uvar n (UVar(n',k))
      	end)
  | EApp(t1,t2) ->
      var_sat_expr t1;
      var_sat_expr t2
  | EAbs(_,t1,_) ->
      var_sat_expr t1
  | _ -> ()

let var_sat gl =
  var_sat_expr gl.concl;
  List.iter (function _,(e,_,_,_,_) -> var_sat_expr e) gl.hyp

let store_mark str =
  let s = !save_stack in
  save_stack := (!cur_proof, !vvar_count, !vvar_kind, get_ulocal (), str, get_undo_pos ())
                ::!save_stack;
  s

let store str = ignore (store_mark str)

let rec restore b =
  match !save_stack with
    [] -> raise (Failure "bug in restore")
  | (p,c,vk,u,str,pos)::ls ->
       cur_proof := p; set_ulocal u; vvar_count := c; save_stack:=ls;
       vvar_kind := vk; set_local 0;
       do_undo pos;
       if b then begin
	 if str <> ""
	 then print_endline ("undo: "^str)
	 else restore true
       end

let restore_to s =
  while (not (s == !save_stack)) do
    restore false;
  done

let pop_store () =
  match !save_stack with
    (_,_,_,_,"",_)::ls ->
      save_stack:=ls;
  | _ -> raise (Failure "bug in restore")


let add_to_nomatch n =
  if Set.mem n !nomatch_set then begin
    print_string "Error: existential variable ?";
    print_int n;
    print_string " already locked.";
    print_newline ();
    raise Error
  end;
  store "lock";
  print_string "Existential variable ?";
  print_int n;
  print_string " locked.";
  print_newline ();
  update nomatch_set (Set.add n !nomatch_set)

let remove_from_nomatch undoable n =
  if not (Set.mem n !nomatch_set) then begin
    print_string "Error: existential variable ?";
    print_int n;
    print_string " not locked";
    print_newline ();
    raise Error
  end;
  if undoable then store "unlock" else store "";
  print_string "Existential variable ?";
  print_int n;
  print_string " unlocked";
  print_newline ();
  update nomatch_set (Set.remove n !nomatch_set)

let unlock_instancied () =
  let fn n =
    try let _ = getuvar n in remove_from_nomatch false n
    with Not_found -> ()
  in
  Set.iter fn !nomatch_set

let print_goal sy new_goal n i ({hyp = hl; concl = f; local = local; _}) =
    let save_local = !cur_local in
    cur_local := local;
    open_vbox 0;
    if n <> 0 then begin
      open_hbox ();
      print_string "goal "; print_int i; print_string "/"; print_int n;
      if new_goal then (print_space (); print_string "(new)");
      close_box ();
      print_cut ();
    end;
    let fn (s,(e,_,_,_,_)) =
      print_string s; print_string " := "; print_expr_sy sy e;
      print_cut () in
    list_do fn hl;
    close_box ();
    print_string "   ⊢ ";print_expr_sy sy f; print_newline (); print_newline ();
    cur_local := save_local


let do_goals () =
  if not !compiling then begin
    match !cur_proof with
      A_proof {remain; _} ->
	let total = List.length remain in
	print_string
	(match remain with _::_::_ -> "Here are the goals:" | _ -> "Here is the goal:");
	print_newline ();
	let fn i (gl,_) = print_goal false false total i gl in
	if proof_general then begin
	  list_count fn remain;
	  print_string "End of goals.";
	  print_newline ()
        end else list_bcount fn remain
    | _ -> raise (Ill_rule "Not proving.")
  end;
  match pipe_exit with None -> ()
  | Some ch ->
      let save = get_formatter_output_functions () in
      set_formatter_out_channel ch;
      print_string "<phox>";
      print_newline ();
    (match !cur_proof with
      A_proof {remain; _} ->
	let total = List.length remain in
	print_string
	(match remain with _::_::_ -> "Here are the goals:" | _ -> "Here is the goal:");
	print_newline ();
	let fn i (gl,_) = print_goal true false total i gl in
        list_bcount fn remain
      | _ -> raise (Ill_rule "Not proving."));
      print_string "</phox>";
      print_newline ();
      set_formatter_output_functions (fst save) (snd save)

let get_goal n =
  try
    match !cur_proof with
      A_proof s -> (fst (List.nth s.remain n)).concl
    | _ -> raise Not_found
  with Not_found ->
    raise (Gen_error ("Can't acces goal $" ^ string_of_int n ^ "."))

let is_higher_order t =
  let rec fn = function
      EApp(t,_) -> fn t
    | UVar(n,k) -> (try fn (getuvar n) with Not_found -> order k > 1)
    | _ -> false
  in fn t

let the_head t =
  let rec fn = function
      EApp(t,_) -> fn t
    | UVar(n,_) as t -> (try fn (getuvar n) with Not_found -> t)
    | _ -> t
  in fn t

let add_assq k a l =
  let rec fn = function
  [] -> [k,a]
  | (k',la)::l ->
    if equal_pos_eq k k' then (k',a)::l
    else (k',la)::(fn l)
  in fn l



let test_seq loc e ng hypt =
  let hypt = match hypt with
    Hypo -> true
  | Subg -> false
  | _ -> raise Exit
  in
  let rec retourne acc = function
    (n,e,e',hypt,dir)::suit -> retourne ((n,e',e,hypt,not dir)::acc) suit
  | [] -> acc
  in
  let rec fn = function
      EAtom(o,_) ->
	if is_capsule o then begin
	  match get_value o with
	    Def e -> fn e
 	  | _ -> None
	end else None
    | UCst(n,_) -> (
	try let (e, l) = List.assoc n loc.cst_eq in
        match fn e with
	  None -> None
        | Some (lc, n) -> Some(lc@(retourne [] l), n)
	with Not_found -> Some ([], n))
    | _ -> None
  in
  let last' e l =
    if l = [] then e else let (_,_,e,_,_) = last l in e
  in
  match e with
    EApp(EApp(EAtom(o,_),e1),e2) when o == equal_obj ->
      begin
	let n, e', leq =
	  match fn e1, fn e2 with
	    (Some (l1,n)), (Some (_,n')) when n > n' ->
               let e0 = last' e1 l1 in
               n, e2, l1@[ng, e0, e2, hypt, true]
	  | (Some (_,n)), (Some (l2,n')) when n < n' ->
               let e0 = last' e2 l2 in
               n', e1, l2@[ng, e0, e1, hypt, false]
	  | (Some (_,n)), (Some (_,n')) when n = n' -> raise Exit
	  | (Some (l1,n)), _ when not (occur' n e2) ->
               let e0 = last' e1 l1 in
               n, e2, l1@[ng, e0, e2, hypt, true]
	  | _, (Some (l2,n')) when not (occur' n' e1) ->
               let e0 = last' e2 l2 in
               n', e1, l2@[ng, e0, e1, hypt, false]
	  | _, _ -> raise Exit
	in
        let o1,_ = head e' in
	if o1 = Uveq then raise Exit;
	add_cst_eq loc n e' leq
      end
  | _ -> raise Exit


let update_hypeq hyp eqn loc =
  let rec fn eqn loc = function
      [] -> ([], eqn, loc)
    |  (s,(e,n,b,Dont_know l,dleft))::ls -> (
	 try
	   let loc = test_seq loc e n b in
	   cons_fst (s,(e,n,b,An_eq,dleft)) (fn eqn loc ls)
	 with Exit -> try
	   let e = match b with Theor _ -> e | _ -> norm_expr e in
	   let l0, nd = decompose_eq l e in
	   let find = ref false in
	   let gn eqn (e1,e2,nl,andpath,nc,keq) =
	     let v = mk_Var() in
	     let pos = get_undo_pos () in
	     (try
		type_strong e1 v;
		type_strong e2 v
	      with
		Clash ->
		  do_undo pos;
		  failwith "bug: Ill_types equation");
	     let _,_,t1,t2 = saturate e1 e2 nl v keq [] in
	     let s1 = list_uvar t1 and s2 = list_uvar t2 in
	     let d1 = Set.is_empty (Set.diff s2 s1) in
	     let d2 = Set.is_empty (Set.diff s1 s2) in
	     let _,_,t'1,t'2 = saturate e1 e2 nl v keq [] in
	     let sy = uni_expr
			(Map.empty, (norm_expr t1), (norm_expr t2))
			(Map.empty, (norm_expr t'2), (norm_expr t'1)) in
	     let o1,_ = head e1 and o2,_ = head e2 in
	     let qq = hyp_to_erule e n b in
	     let add eqn ld =
               let o1,o2,e1,e2 = if ld then o1,o2,e1,e2 else o2,o1,e2,e1 in
               let rec mk_perm d = function
		   EAbs(_,e,_) -> d::(mk_perm (d+1) e)
		 | _ -> [] in
               find := true;
               let rec hn acc = function
	         (o2',e1',e2',nl',k',sy',eqtl as tpl)::l ->
		   if sy <> sy' || o2 != o2' || not (equal_kind v k')
                   then hn (tpl::acc) l
		   else (
		     try
		       let perm = eqcmp e1 e2 e1' e2' in
		       let rec insert x l = match x,l with
			   _, [] -> [x]
			 | (_,_,_,_,ncond,_), (_,_,_,_,ncond',_ as y)::l' ->
			       if ncond < ncond' then x::l else y::insert x l'
		       in
		       let neqtl = insert (qq,perm,andpath,ld,nc,false) eqtl in
		       rev_append acc ((o2',e1',e2',nl',k',sy',neqtl)::l)
		     with Not_found -> hn (tpl::acc) l)
	       | [] ->
		   let perm = mk_perm 0 e1 in
		   rev_append acc [o2,e1,e2,nl,v,sy,[qq,perm,andpath,ld,nc,false]]
               in
               try
		 let l = assoc_eq o1 eqn in
		 add_assq o1 (hn [] l) eqn
               with Not_found ->
		 let perm = mk_perm 0 e1 in
		 (o1,[o2,e1,e2,nl,v,sy,[qq,perm,andpath,ld,nc,false]])::eqn
	     in
	     let eqn = if o1 != Alleq &&
               (d1 || (not d2 && term_size e1 >= term_size e2))
             then add eqn true else eqn in
	     let eqn = if not sy && o2 != Alleq &&
               (d2 || (not d1 && term_size e2 >= term_size e1))
             then add eqn false else eqn in
	     eqn
	   in
	   let eqn = List.fold_left gn eqn l0 in
	   if !find then
             if nd then
               cons_fst
		 (s,(e,n,b,Dont_know (List.map (fun (_,_,_,x,_,_) -> x) l0), dleft))
		 (fn eqn loc ls)
             else
               cons_fst (s,(e,n,b,An_eq,dleft)) (fn eqn loc ls)
	   else
             cons_fst (s,(e,n,b,Not_eq,dleft)) (fn eqn loc ls)
	 with
	   Gen_error _ -> cons_fst (s,(e,n,b,Not_eq,dleft)) (fn eqn loc ls)
	 | Dont_Know_Eq -> cons_fst (s,(e,n,b,Dont_know [],dleft)) (fn eqn loc ls))

    | h::ls -> cons_fst h (fn eqn loc ls)
  in
  fn eqn loc hyp

let update_goal (gl0, st0) =
      let nh,ne,nl = update_hypeq gl0.hyp gl0.eqns gl0.local in
      let gl0 = {gl0 with hyp = nh; eqns = ne; local = nl} in
      (gl0,st0)

let update_goals = List.map update_goal

let add_hyp tri (name,(a1,_,_,_,_) as hyp) gl loc e =
  let a1 = norm_expr a1 in
  let is_trivial = match a1 with
    EApp(EApp(EAtom(o,_),u),v) when
      equal_obj == o && equal_expr u v -> true
  | _ -> false
  in
  let rec mem_hyp = function
    [] -> false
  | (_,(a2,_,_,_,_))::l -> equal_expr a1 (norm_expr a2) || mem_hyp l
  in
  if is_trivial || mem_hyp gl.hyp then begin
     if tri.from_trivial && mem_expr false e gl.done_list then
       raise (Ill_rule "ADone2");
     (gl.hyp, emapadd e gl.done_list, gl.eqns, loc, false)
  end else
  if mem_hyp gl.oldhyp then begin
     if tri.from_trivial && mem_expr false e gl.done_list then
       raise (Ill_rule "ADone3");
     let hyp, neqns, nlocal = update_hypeq [hyp] gl.eqns loc in
     (hyp@gl.hyp, emapadd e gl.done_list, neqns, nlocal, true)
  end else begin
     let hyp, neqns, nlocal = update_hypeq [hyp] gl.eqns loc in
     hyp@(List.remove_assoc name gl.hyp), singl_done gl.done_list e, neqns, nlocal, true
  end

let apply_rewrite toadd nl gl00 st00 ls =
  if ls = [] then gl00,st00,nl else begin
  let st00 = match st00 with
    Fol st -> st
  | Fin n ->
      let r = {sref = gl00.gref; rule = No_rule; next =Fin n} in
      add_to_undo (let old = gl00.gref in fun () -> gl00.gref <- old);
      gl00.gref <- new_ref (); r in
  let left_to_do = ref [] in
  let rec fn nl gl0 st0 = function
    [] -> gl0,st0,nl
  | (Req(path,context,None,e1,_,stc,st,dir))::ls ->
        let path = List.rev path in
        let cl = path_subst path gl0.concl (norm_expr (EApp(context,e1))) in
        let n2 = new_ref () in
        let gl1 = {gl0 with gref = n2; concl = cl; ax_test = false;
                   done_list = if toadd then emapadd cl gl0.done_list
		   else gl0.done_list} in
        let rule = if dir then Lr_eqn (path,context,stc.sref,n2)
                          else Rl_eqn (path,context,stc.sref,n2) in
        let st1 = Fol {sref = gl0.gref; rule = rule; next = st0} in
        stc.next <- st1;
        fn (st@nl) gl1 st1 ls
  | (Req(path,context,Some stic,_,_,stc,_,dir) as r)::ls ->
        if stic.sref = -1 then begin
          left_to_do := r::!left_to_do
        end else begin
          let n2 = new_ref () in
          let rule = if dir then Lr_eqn (path,context,stc.sref,n2)
                            else Rl_eqn (path,context,stc.sref,n2) in
          let st1 = Fol {sref = stic.sref; rule = rule; next = stic.next} in
          stc.next <- st1;
	  add_to_undo (let old = stic.next in fun () -> stic.next <- old);
          stic.next <- st1;
	  add_to_undo (let old = stic.sref in fun () -> stic.sref <- old);
          stic.sref <- n2
        end;
        fn nl gl0 st0 ls
  | (Rdef(path,None,oe,kind,l,dir))::ls ->
        let path' = List.fold_left (fun x _ -> LApp::x) path l in
        let path = List.rev path and path' = List.rev path' in
        let e = EAtom(oe,kind) in
        let akind, fe = build_subterm oe kind l in
        let cl = path_subst path gl0.concl
          (if not dir then
            try EApp(fe,kind_inst oe kind)
            with Not_found -> raise (Failure "bug in apply_rewrite")
          else EApp(fe,e)) in
        let gl1 = {gl0 with gref = new_ref(); concl = cl; ax_test = false} in
        let rule = if not dir then
          Fact_def (Path(path, fe), e, akind)
        else
          Devl_def (Path(path', e), akind)
        in let st1 = Fol {sref = gl0.gref; rule = rule; next = st0} in
        fn nl gl1 st1 ls
  | (Rdef(path,Some stic,oe,kind,l,dir) as r)::ls ->
        if stic.sref = -1 then begin
          left_to_do := r::!left_to_do
        end else begin
          let path' = List.fold_left (fun x _ -> LApp::x) path l in
          let path = List.rev path and path' = List.rev path' in
          let e = EAtom(oe,kind) in
          let akind, fe = build_subterm oe kind l in
          let rule = if not dir then
            Fact_def (Path(path, fe), e, akind)
          else
            Devl_def (Path(path', e), akind)
          in
          let st1 = Fol {sref = stic.sref; rule = rule; next = stic.next} in
	  add_to_undo (let old = stic.next in fun () -> stic.next <- old);
          stic.next <- st1;
	  add_to_undo (let old = stic.sref in fun () -> stic.sref <- old);
          stic.sref <- new_ref ()
        end;
        fn nl gl0 st0 ls
  | (Insert st1)::ls ->
      if st1.sref <> (-1) then failwith "bug 007 in apply_rewrite";
      add_to_undo (let old = st1.sref in fun () -> st1.sref <- old);
      st1.sref <- gl0.gref;
      add_to_undo (let old = st1.next in fun () -> st1.next <- old);
      st1.next <- st0;
      add_to_undo (let old = st1.rule in fun () -> st1.rule <- old);
      st1.rule <- In_rule (gl00,st00);
      add_to_undo (let old = gl0.gref in fun () -> gl0.gref <- old);
      gl0.gref <- new_ref ();
      fn nl gl0 (Fol st1) ls
  in
  let gl00,st00,nl = fn nl gl00 (Fol st00) ls in
  let r = fn nl gl00 st00 !left_to_do in
  if !left_to_do <> [] then failwith "bug 1356 in apply_rewrite";
  r end

let rec default_kvar = function
  UVar (n,k) -> (
    try default_kvar (getuvar n);()
    with Not_found ->
      let (r,a,b,c) = get_ulocal () in
      let r' = Map.add n (default_of k) r in
      set_ulocal (r',a,b,c))
| EApp (t1,t2) -> default_kvar t1; default_kvar t2
| EAbs (_,t1,_) -> default_kvar t1
| Path(_,t1) -> default_kvar t1
| _ -> ()

let default_inst_kind k =
  let rec f t = match norm t with
      KVar ptr -> update ptr kForm
    | KArrow(k, k') -> f k; f k'
    | KAtom (_,l) -> List.iter f l
    | _ -> ()
  in f k

let default_inst_path path =
  let g = function
      PAbs(_, k) -> default_inst_kind k
    | _ -> ()
  in List.iter g path

let rec default_kinst = function
  UVar (n,_) -> (
    try default_kinst (getuvar n);()
    with Not_found -> assert false)
| EApp (t1,t2) -> default_kinst t1; default_kinst t2
| EAbs (_,t1,k) -> default_inst_kind k; default_kinst t1
| EAtom(_,lk) -> List.iter default_inst_kind lk
| Path(path,t1) -> default_inst_path path; default_kinst t1
| _ -> ()

let dum_kind = Unknown

module Inttbl = Myhashtbl.Poly_Hashtbl (struct type key = int end)

let rec look_for_local_def o = function
  Fin _ -> true
| Fol {rule = Decl_local_def(_,o'); _} when o == o' -> false
| Fol {next = next; _} -> look_for_local_def o next

let build_proof _ sr sl root =
  let proofs = Inttbl.create 201 in
  let guses = Inttbl.create 201 in
  let getd n =
    let r = Inttbl.find proofs n in Inttbl.remove proofs n; r in
  let tdr = ref [] in
  let last_n = ref (-1) in
  let last_p = ref (EVar (-1)) in
  let cur = ref (Fin 0) in
  let subg = ref 0 in
  let nr = List.map (fun ({gref = n; _}, l) ->
    incr subg;
    Fol {sref = n;rule =
	 Comment ("goal "^(string_of_int !subg)); next = l}) sr
  in
  let final s = match s with
    Fin 0 -> true
  | s -> match root with Some (s') when s = s' -> true | _ -> false
  in

  let td = ref (sl@nr) in
  while (not (final !cur) || !td <> [] || !tdr <> [] || !last_n >= 0) do
    match !cur with
      s when final s -> (
       if !last_n >= 0 then begin
         Inttbl.add proofs !last_n !last_p;
         last_n := -1; last_p := EVar (-1)
       end;
       match !td with
         [] -> td:=!tdr; tdr:=[]
       | st::sl -> cur:= st; td:=sl)
    | Fin _ -> failwith "bug: Get Fin non 0 in build_proof"
    | Fol {sref = n1; rule = rule; next = next} ->
      let cont p = last_n:=n1; last_p := p; cur := next in
      try match rule with
        Axiom n ->
          cont (UCst (n, dum_kind))
      | Subgoal n ->
          Inttbl.add_find guses n (ref 1) (fun p -> incr p) (fun _ -> ());
          cont (UCst (n, dum_kind))
      | Cut_rule (s,n,n',q) -> (
          let (p1,p2) = if n = !last_n then !last_p,(getd n')
                    else if n' = !last_n then (getd n),!last_p
                    else failwith "bug 2 in build_proof" in
          try
            let nb = !(Inttbl.find guses q) in
            if nb = 1 || (match p1 with EVar _ -> true | _ -> false) then
              cont (subst_cst q p2 p1)
            else
              cont (EApp(EApp(aobj cut_rule_obj, p1),
                         bind_cst s q p2 kProof))
          with Not_found -> cont p2)
      | No_rule ->
          cont !last_p
      | In_rule _ ->
	  cont !last_p
      | Arrow_intro (s,n,e) ->
          cont (EApp(EApp(aobj arrow_intro_obj, e),
                     bind_cst s n !last_p kProof))
      | Forall_intro (s,n,k) ->
          cont (EApp(EAtom(forall_intro_obj, [k]),
             bind_cst s n !last_p k))
      | Arrow_elim (n,n') ->
          let (p1,p2) = if n = !last_n then !last_p,(getd n')
                    else if n' = !last_n then (getd n),!last_p
                    else failwith "bug 3 in build_proof" in
          cont (EApp(EApp(aobj arrow_elim_obj, p1), p2))
      | Forall_elim (e,k) ->
          cont (EApp(EApp(EAtom(forall_elim_obj,[k])
                       , !last_p),e))
      | Fact_def (e2,e3,t) -> (
          match e3 with
            EAtom (o,_) ->
              if (Data_base.Object.get_value o).origin = Local_def &&
                 look_for_local_def o next
              then begin
                print_endline ("Warning: local definition of "^
                                (get_name o)^
                               " escaping its scope. We will fix that !");
                cont (!last_p)
              end else
                cont (EApp(EApp(EApp(EAtom(fact_def_obj,[t;mk_Var()]),e2),e3), !last_p))
          | _ -> failwith "bug 008 in build_proof")
      | Devl_def (e2,t) -> (
          match e2 with
            Path(_,(EAtom (o,_))) ->
              if (Data_base.Object.get_value o).origin = Local_def &&
                 look_for_local_def o next
              then begin
                print_endline ("Warning: local definition of "^
                                (get_name o)^
                               " escaping its scope. We will fix that !");
                cont (!last_p)
              end else
                cont (EApp(EApp(EAtom(devl_def_obj,[t]),e2), !last_p))
          | _ -> failwith "bug 007 in build_proof")
      | Lr_eqn (p,context,n,n') ->
          let (p1,p2) = if n = !last_n then !last_p,(getd n')
                    else if n' = !last_n then (getd n),!last_p
                    else failwith "bug 4 in build_proof" in
          cont (EApp(EApp(EApp(aobj(lr_eqn_obj),Path(p,context)),Path(p,p1)),p2))
      | Rl_eqn (p,context,n,n') ->
          let (p1,p2) = if n = !last_n then !last_p,(getd n')
                    else if n' = !last_n then (getd n),!last_p
                    else failwith "bug 5 in build_proof" in
          cont (EApp(EApp(EApp(aobj(rl_eqn_obj),Path(p,context)),Path(p,p1)),p2))
      | Decl_local_def (_,o) -> (
          try let f = bind_atom (get_name o) o !last_p (get_kind o) in
          let e = match get_value o with
            Def e -> e
          | _ -> failwith "bug 546 in build_proof" in
          cont (EApp(EApp(EApp(aobj local_def_obj, Syntax (get_syntax o)),
                     e), f))
          with Not_found -> cont (!last_p))
      | Theo e ->
          cont (EApp(aobj use_theorem_obj, e))
      |	Comment s ->
	  cont (EApp(aobj comment_obj, EData(Data.EString s)))
      |	Claim e ->
	  cont  (EApp(aobj lclaim_obj, e))

      with Not_found -> cur := Fin 0
  done;
  let fn p _ v =
    match p with
      Some _ -> failwith "Parts of the proof are missing !"
    | None -> Some v
  in
  let p =
    match Inttbl.it_table fn None proofs with
      None -> failwith "Parts of the proof are missing !"
    |	 Some p -> p
  in
  norm_expr p

let select_eq l (eqns : leqns) =
  let rec fn = function
    [] -> []
  | (o,e1,e2,nl,k,sy,eqtl) :: suit ->
      let neqtl = select (fun (typ,_,_,_,_,_) -> not ( List.mem typ l)) eqtl in
      if neqtl = [] then fn suit else (o,e1,e2,nl,k,sy,neqtl)::(fn suit)
  in if l = [] then eqns else List.map (fun (pos_eq,x) -> pos_eq,fn x) eqns

let add_rhyp local name e =
  let o =
    {fkind = kForm; fvalue = Def e; syntax = Trivial;
     poly = 0; exported = false; origin = Local_hyp} in
  fst (real_local_add local name o)

let rule_rm b l gl0 st0 =
   let leqn = ref [] in
   let old = ref gl0.oldhyp in
   let names = ref [] in
   let hyps = ref [] in
   let rec fn l = function
     (s,(e,n,bt,st,_)) as c::ls ->
           if b = (List.mem s l) then begin
             if st = An_eq then leqn:=(hyp_to_erule e n bt)::!leqn;
             old:=c::!old;
	     names := s::!names;
	     hyps := n::!hyps;
             fn (if b then subtract l [s] else l) ls
           end else c::(fn (if b then l else subtract l [s]) ls)
     | [] ->
	 match
	   l with [] -> []
	 | s::_ -> raise (Ill_rule ("Hypothesis \""^s^"\" not found."))
   in
   let nhyp = fn l gl0.hyp in
   let gl1 = {gl0 with hyp = nhyp;
	      local = remove_local_cst gl0.local !names !hyps;
              eqns = select_eq (!leqn) gl0.eqns ;
              oldhyp = !old} in
   [gl1,st0],[]

let warn_if_used gl name =
  if not !compiling then begin
    let save_local = !cur_local in
    cur_local := gl.local;
    try try
      ignore (find_local name);
      raise Exit
    with Not_found ->
      ignore (sym_get name);
      raise Exit
    with
      Not_found -> cur_local := save_local;
    | Exit ->
	cur_local := save_local;
	print_string "Warning: name \""; print_string name;
	print_string "\" already in use.";
	print_newline ()
  end

let rule_rename oname nname gl0 st0 =
  warn_if_used gl0 nname;
  try
    let gl1 = {gl0 with local = rename_local_cst gl0.local oname nname} in
    [gl1,st0],[]
  with Not_found -> try
    let find = ref 0 in
    let nhyp = List.map (fun (n,h as c) ->
      if n = oname then (incr find; (nname, h)) else c) gl0.hyp
    in
    if !find = 0 then raise Not_found;
    let gl1 = {gl0 with
	       local = rename_caps_def gl0.local oname nname;
	       hyp = nhyp }
    in
    [gl1,st0],[]
  with Not_found ->
    raise (Ill_rule "tactic rename failed.")

let rule_use dir tri s e gl0 st0 =
   let r1 = new_ref () and r2 = new_ref () and n1 = new_const ()in
   cur_local := gl0.local;
   let s = (if s = "" then free_name "G" [] else s) in
   warn_if_used gl0 s;
   try let k = type_check e in
   try
     unif k kForm;
     let nlocal = if (String.get s 0) <> '#' then
       add_rhyp gl0.local s e
     else gl0.local in
     let gl1 = {gl0 with gref = r1; concl = e;
                ax_test = false; done_list = emapadd e gl0.done_list} in
     let st1 = Fol {sref = gl0.gref; rule = Cut_rule (s,r1,r2,n1);
                    next = st0} in
     let nh,ndl,neqns, nlocal, new_hyp =
      add_hyp tri (s,(e,n1,Subg,Dont_know [], (false,[]))) gl0 nlocal gl0.concl in
     let gl2 = {gl0 with gref =  r2; local = nlocal;
                ax_test = false; left_test = not new_hyp && gl0.left_test;
		hyp = nh; eqns = neqns;
                done_list = ndl} in
     if dir then [(gl1,st1);(gl2,st1)],[] else [(gl2,st1);(gl1,st1)],[]
   with Clash ->
     unif k kTheorem;
     let nh = match (get_inst e) with
       EApp(EApp(EAtom _,e),_) -> e
     | _ -> raise (Failure "bug0 in rule_use") in
     let nlocal = if (String.get s 0) <> '#' then
       add_rhyp gl0.local s nh
     else gl0.local in
     let nh,ndl,neqns,nlocal,new_hyp =
       add_hyp tri (s,(nh,n1,Theor e,Dont_know [], (false, []))) gl0
	 nlocal gl0.concl
 in
     let gl2 = {gref = gl0.gref; concl = gl0.concl; local = nlocal;
                ax_test = false; left_test = not new_hyp && gl0.left_test;
		hyp = nh; eqns = neqns; oldhyp = gl0.oldhyp;
                done_list = ndl} in
     [gl2,st0],[]
   with Clash -> raise (Ill_rule "tactic use failed.")

let do_next n =
  store "next";
  match !cur_proof with
    A_proof ({remain; _} as record) ->
          let nremain =
            try if n = 0 then rotate remain
                else if n < 0 then extract (-n) remain
                else insert n remain
            with Invalid_argument _ -> failwith "next failed." in
          cur_proof := A_proof {record with remain = nremain };
          (match nremain with
            [] -> raise (Failure "bug in do_next")
          | (_,_)::_ -> do_goals ());
          set_local 0
  | _ -> raise (Ill_rule "Not proving.")

let rec do_undo_cmds = function
  0 -> do_goals (); set_local 0
| n -> if !save_stack = [] then raise
         (Ill_rule "can't undo initial goal (use abort)")
       else (restore true; do_undo_cmds (n - 1))


let rule_axiom from_auto tri hyp gl st =
  let pos = get_undo_pos () in
  try
    let (e,n,b,_,_) = (List.assoc hyp gl.hyp) in
    let lu = if from_auto then list_uvar e else Set.empty in
    let call_trivial = (tri, call_trivial, (gl, st, [])) in
    let dm, rwt, (gl0,st0,nl0) =
      pmatch gl.eqns gl.local false from_auto call_trivial e gl.concl in
    if from_auto && tri.from_trivial && dm && Set.fold (fun x b ->
            b || try let _ = getuvar x in true
	    with Not_found -> false) lu false
     then raise (Ill_rule "did match !");
    let (gl1,st1,nl1) = apply_rewrite true nl0 gl0 st0 rwt in
    ([],(Fol {sref = gl1.gref;rule = hyp_to_rule n b;
         next = st1}::nl1))
  with
    Not_found ->
      do_undo pos;
      raise (Ill_rule "Not an hypothesys.")
  | Fail_matching | Ill_rule _ ->
      do_undo pos;
      raise (Ill_rule "Hypothesis doesn't match.")

type deep_elim =
    NoDeep
  | Ax of  rrule list * rule option
  | Intros of string list
  | And_intro of rrule list * deep_elim * deep_elim
  | Or_intro of rrule list * deep_elim * bool (* left = true *)
  | Exists_intro of rrule list * deep_elim * expr

type iel =
  Ar of expr * expr * deep_elim
| Fl of expr * expr * kind
| Df of expr * path list * expr * kind
| Th of expr
| Gv of expr
| Hp of string
| Rl of int * iel list * rrule list

type rule_opt =
  RNum of int
| Names of (string * new_elim_option list list option) list
| Auth of obj list
| Inv_only
| Default

let new_names = ref []

let get_exists_var addq do_open local e =
  let rec fn e stack = match e with
      EApp(EAtom(o,_),EAbs(n,_,_))
      when o == !exists_obj || o == !exists_one_obj
      -> [if addq then "?"^n else n]
    | EApp(e1,u) -> fn e1 (u::stack)
    | EAtom(o,_) when do_open && can_open local o -> (
	match get_value o with
          Def e -> fn (norm_sexpr e stack) []
	| Prg e -> fn (norm_sexpr e stack) []
	| _ -> [])
    | UVar(n,_) -> (try fn (getuvar n) stack
    with Not_found -> [])
    | _ -> []
  in fn e []

let make_intropt local intro_names e1 optinf =
    let ls = get_exists_var false false local e1 in
    let rec fn ls d = function
      [] -> []
    | (-1 | -4)::l -> fn ls (d+1) l
    | n::l ->
        let rec gn n ls = match n,ls with
          (0,ls) -> ls,[]
        | (n,[]) -> let (ls,la) = gn (n-1) [] in (ls,""::la)
        | (n,(s::ls)) ->
            let s = match !intro_names with
              [] -> "?"^s
            | s::l -> intro_names:=l; s in
            let (ls,la) = gn (n-1) ls in
            (ls,s::la)
        in
        let ls, la = gn n ls in
        (d, OptInt la)::(fn ls (d+1) l)
    in fn ls 1 optinf

let rec rule_width pat n =
  match pat with
    EAbs(_,e,_) -> rule_width e (n-1)
  | _ -> n

let sort_rules elim loc e = function
    [] -> []
  | [_] as rules -> rules
  | rules ->
      let rules = List.map (
	function (_,(_,_,pat,n,_,_,_)) as r ->
	  (dist loc e (saturate_pattern pat),
	   if elim then 0 else rule_width pat n), r) rules
      in
      let rules = List.sort (
	fun (n,(_,(_,_,_,_,l,o,_))) (n',(_,(_,_,_,_,l',o',_))) ->
          let fn n l o =
	    let x = match l with
	      Intro_opt(x,_) -> x
            | Elim_opt (x::_) -> x
	    | _ -> failwith "bug1 in sort_rules"
            in
	    if isINV x && elim then (o,2,n) else
	    if isINV x && not elim then (o,-1,n) else
            if isNEC x then (o,1,n) else (o,0,n)
	  in
	  let n = fn n l o and n' = fn n' l' o' in
	  if n < n' then -1 else 1) rules in
      List.map snd rules

let get_intros inv_only leqn loc do_open e0 =
  let e0 = norm_expr e0 in
(*
  print_expr e; print_newline ();
  Printf.printf "do_open %b" do_open; print_newline ();
*)
  let el, oh, intros =
    try
      let rec fn el oh e =
        let f,o,_,l = decom false e in
        let noh = o::oh in
        try el, noh, symhash_find tbl_intro o
        with Not_found -> match f with
            None  -> el, noh, []
          | Some f -> if do_open && can_open loc o then
              let e1 = norm_sexpr f l in fn (e1::el) noh e1
                      else el, noh, []
      in fn [e0] [] e0
    with Not_found -> [e0], [], []
  in
  let intros =
      select  (fun (_,(_,_,_,_,l,_,_)) ->
                 match l with Intro_opt(x,_) -> not (isTOT x)
                                              && not (do_open && isNEC x)
		                              && not inv_only
                            | _ -> failwith "bug1 in get_intros") intros

  in
  let acc = ref [] in
  let totals e =
    match e with EApp(_,ea) ->
      let rec fn ea =
        try
          let f,o,_,largs = decom' ea in
          if List.exists (equal_pos_eq o) !acc then [] else begin
            acc:=o::!acc;
            (try
              match o with
                Oneq o -> symhash_find tbl_intro o
              | _ -> raise Not_found
            with Not_found -> []) @
            (match f with
              None  ->
		let l2 =
		  match o with
		    Uneq n ->
                      let (e,_) = List.assoc n loc.cst_eq in [e]
		  |  _ -> []
                in
                let l = if do_open then
                           (try eqhash_find tbl_rewrite o with Not_found -> [])
                         @ (try assoc_eq o leqn  with Not_found -> [])
                        else []
                in
                let l = List.fold_left (fun x (p, _, _, _, _, _, _) ->
                          match p with
                            Oneq o when
                              not (List.exists (equal_pos_eq p) !acc) ->
                                aobj o::x
                          | Uneq n when
                              not (List.exists (equal_pos_eq p) !acc) ->
                                UCst(n,mk_Var ())::x
                          | _ -> x) l2 l in
                List.fold_left (fun x e -> fn e @ x) [] l
            | Some f -> if match o with Oneq o -> can_open loc o
                                      | _ -> failwith "but 56876" then
                          fn (norm_sexpr f largs) else [])
          end
        with Not_found -> []
      in fn ea
    | _ -> []
  in
  let totals =
      select  (fun (_,(_,_,_,_,l,_,_)) ->
                 match l with Intro_opt(x,o) ->
		   isTOT x && (not inv_only || isINV x) &&
		   (not do_open || not (isNEC x)) &&
				    (match o with Some o ->
				      oh = [] ||
                                      List.memq o oh
                                    | None -> true)
                 | _ -> failwith "bug2 in get_intros")
              (List.fold_left (fun l e -> l @ totals e) [] el) in
  let rules =
    List.fold_left
      (fun r (s,(_,th,_,_,_,_,_) as c) ->
	if List.exists (fun (s',(_,th',_,_,_,_,_)) ->
	  s = s' && th == th') r
	then r else c::r)
      []
      (intros @ totals) in
  let rules = sort_rules false loc e0 rules in
(*
  let fn  (s,(th,_,_,_,l,_,_)) = print_expr th; print_newline () in
  print_endline "get_intros ->";
  List.iter fn rules;
  print_newline ();
*)
  intros = [], rules

let false_expr = EApp(EAtom(forall_obj,[kForm]),
                      EAbs("X",EVar 0,kForm))

let treat_rule gl0 flags =
  if isCTD flags then
    {gl0 with done_list = emapadd false_expr gl0.done_list}
  else gl0

let new_cmd_opt = ref []
let lock_intro = ref []
let lock_elim = ref []
let lock_depth = ref []

let rec rule_intro did_inv tri rule_opt gl0 st0 =
  let td, hyps, can_ope, register, inv_only = match rule_opt with
    RNum n -> let rec f = function 0 -> [] | n -> ("",None)::f (n-1) in
             false, f n, ref [], ref false, false
  | Names l -> false, l, ref [], ref false, false
  | Auth l -> true, [], ref l, ref false, false
  | Inv_only -> true, [], ref [], ref true, true
  | Default -> true, [], ref [], ref true, false
  in
  let did_intro = ref false in
  new_names := [];
  let test o =
    if td then
      if !register then false
      else not (List.memq o !can_ope)
    else false
  in
  let set o =
    did_intro := true;
    if !register then begin
      can_ope := o::!can_ope; register:= false;
      if rule_opt = Default then begin
	if o==forall_obj then can_ope := arrow_obj::!can_ope;
	if o==arrow_obj then can_ope := forall_obj::!can_ope;
	if o== !exists_obj then can_ope := !and_obj::!can_ope;
	if o== !and_obj then can_ope := !exists_obj::!can_ope
      end
    end
  in
  let register o =
    if !register then can_ope := o::!can_ope
  in
  let exit r =
    if td && !did_intro then r else raise (Ill_rule "Can't apply intro.")
  in
  let rec fn ng nl gl st = function
      [] ->
	if td then
          fn ng nl gl st [("",None)]
	else
          ((gl,st)::ng),nl
    | (s,eopt)::ls as ls0 ->
      match norm_expr gl.concl with
	| EApp(EApp(EAtom(o,_),a1),ncl) when o == arrow_obj ->
            if inv_only || test o then exit ((gl,st)::ng),nl else (
              set o;
              cur_local := gl.local;
              let s =
		if s <> "" && eopt = None then
		  match s.[0] with
		    '?' ->
		      free_name (String.sub s 1 (String.length s - 1)) []
		  | '[' -> raise (Ill_rule "option mismatch")
		  | _ -> s
		else free_name "H" []
              in
	      warn_if_used gl s;
              let nlocal = add_rhyp gl.local s a1 in
              let n = new_const () in
	      type_strong a1 kForm; (* BUg à corriger mieux *)
              let nh,ndl,neqns,nlocal,new_hyp =
		add_hyp tri (s,(a1,n,Hypo,Dont_know [], (false, []))) gl nlocal ncl in
              let rl = Arrow_intro (s,n,a1) in
              new_names := s::!new_names;
              let st1 = Fol {sref = gl.gref;
			     rule = rl; next = st} in
              let gl1 = {gref = new_ref (); concl = ncl; hyp = nh;
			 eqns = neqns;
			 left_test = not new_hyp && gl0.left_test;
			 ax_test = false; done_list = ndl; local = nlocal;
			 oldhyp = gl.oldhyp} in
              fn ng nl gl1 st1 ls)
	| EApp(EApp(EAtom(o,[_;_]),a1),(EAbs(so,_,k) as a2)) when o == !let_obj ->
	    let s = if s <> ""  && eopt = None then
	      if s.[0] = '?' then
		free_name (String.sub s 1 (String.length s - 1)) []
	      else s
	    else free_name so []
	    in
            let (gl1, st1) =
              match do_add_rlocal s k (Def a1) Trivial gl st with
              | [gl1,st1], [] -> (gl1,st1)
              | _ -> assert false
            in
	    cur_local := gl1.local;
	    let o = sym_get s in
	    let goal = EApp(a2,aobj o) in
            let (gl1, st1) =
              match rule_elim false tri false false true [] 0 goal gl1 st1 with
              | [gl1,st1], [] -> (gl1,st1)
              | _ -> assert false
            in
            fn ng nl gl1 st1 ls
	| EApp(EAtom(o,[_]),(EAbs(so,_,k) as a2) ) when o == forall_obj ->
            if inv_only || test o then
              exit ((gl,st)::ng),nl else (
		set o;
		cur_local := gl.local;
		let s =
		  if s <> "" then
		    match s.[0] with
		      '?' ->
			free_name (String.sub s 1 (String.length s - 1)) []
		    | '[' -> raise (Ill_rule "option mismatch")
		    | _ -> s
		  else free_name so []
		in
		let n = new_const () in
		let v = UCst (n,k) in
		warn_if_used gl s;
		let nlocal =
		  if (String.get s 0) <> '#' then add_local gl.local s v
                  else gl.local in
		let ncl = norm_expr (EApp(a2,v)) in
		let rl = Forall_intro (s,n,k) in
		let (r,u,m,l) as save_ulocal = get_ulocal () in
		let pos = get_undo_pos () in
		(try
		  let u = List.fold_left (
		    fun u (_,(f,_,_,_,_)) ->
		      propagate r u (singl n) f) u gl.hyp in
		  let u = List.fold_left (
		    fun u (r1,r2,_,_,_,_,_,_) ->
		      let u = propagate r u (singl n) (r1.allt) in
		      propagate r u (singl n) (r2.allt)) u m in
		  let u = propagate r u (singl n) gl.concl in
		  set_ulocal (r,u,m,l)
		with Fail_propagate ->
		  do_undo pos;
		  set_ulocal save_ulocal;
		  raise (Ill_rule "matching captures variable"));
		let st1 = Fol {sref = gl.gref;
			       rule = rl; next = st} in
		if tri.from_trivial && mem_expr false ncl gl.done_list then
		  raise (Ill_rule "ADone4");
		let gl1 = {gl with
			   gref = new_ref (); concl = ncl; local = nlocal;
			   eqns = gl.eqns; ax_test = false;
			   done_list = emapadd ncl gl.done_list; } in
		fn ng nl gl1 st1 ls)
	| _ -> gn ng nl gl st ls0

  and gn ng nl gl st ls =
    try
    let tpl =
      try Some (decom true (norm_expr gl.concl))
      with Not_found -> None
    in
    if match tpl with Some (_, o, _, _) -> test o | None ->
      match rule_opt with Names _ | RNum _ -> false | _ -> true
    then exit ((gl,st)::ng),nl else
      let b, l = get_intros inv_only gl.eqns gl.local tri.from_trivial gl.concl in
     try
        if l = [] then raise Not_found;
        try kn tpl ng nl gl st ls l
        with Ill_rule _ as e -> if b then raise Not_found else raise e
      with Not_found ->
        let f,o,k,u = match tpl with
          Some (_,o,_,_ as tpl) ->
	    if not (can_open gl.local o) then raise Not_found; tpl
        | None ->
	    raise Not_found
        in
        match f with Some f ->
          let e = EAtom(o,k) in
          register o;
          let akind, fe = build_subterm o k u in
          let ncl = norm_expr (EApp(fe,f)) in
          let st1 =
            if (Data_base.Object.get_value o).origin = Local_hyp then
              st
            else
              let rl = Fact_def (Path([], fe), e, akind) in
              Fol {sref = gl.gref; rule = rl; next = st}
          in
          let gl1 = {gl with gref = new_ref (); concl = ncl;
                     ax_test = false} in
          (* to avoid opening of definition if no rule applied *)
	  let sd = !did_intro in
	  did_intro := false;
          (try
	    let r = fn ng nl gl1 st1 ls in
	    did_intro := !did_intro || sd;
	    r
	  with
	    Ill_rule "Can't apply intro." as e ->
	      did_intro := sd;
	      if sd then raise Not_found else raise e
	  | e ->
	      did_intro := sd; raise e)
        | None -> exit ((gl,st)::ng),nl
  with Not_found -> exit ((gl,st)::ng),nl

  and kn tpl ng nl gl st ls = function
          [] ->  exit ((gl,st)::ng),nl
        | (s0,(f,th,aux,nb,optinf,_,_))::l' ->
	let th, f, _ = generalize_for_rules th f aux in
        let (s',eopt,ls') = match ls with
          [] -> "",[],[]
        | (s',Some e)::ls' ->  s',e,ls'
        | (s',None)::ls' ->  s',[],ls' in
        if (s' <> s0) && (s' <> "") then kn tpl ng nl gl st ls l' else begin
        if !trace_trivial then begin
	  print_string ("Trying intro named: "^s0^" ");
	  print_expr f;
	  print_newline ();
	end;
        let noeq = snd (head th) != equal_reflexive_obj in
        try let ng',nl' =
          rule_elim true tri noeq false true [0, OptWith eopt] nb th gl st in
        (match tpl with Some (_,o,_,_) -> set o | None -> ());
        if ng' = [] && ls' <> [] then raise (Ill_rule "Can't apply intro.");
	(match optinf with
	  Intro_opt (x,_) -> if isINV x then did_inv := true
	|  _ -> ());
        List.fold_right (fun (gl,st) (ng,nl) -> fn ng nl gl st ls')
                        ng' (ng, nl'@nl)
        with Ill_rule _ | Fail_matching ->
        kn tpl ng nl gl st ls l' end in

  fn [] [] gl0 st0 hyps

and rule_elim in_rule tri noeq no_elim abs opt n e1 gl0 st0 =

  let intro_names, opt = match opt with
    (0,OptInt s)::opt -> ref s, opt
  | _ -> ref [], opt
  in

  let k = type_check e1 in

  let e1,lr =
    match (get_inst e1) with
      EApp(EApp(EAtom (o,_),e),_) when o == theorem_obj -> e,[Th e1]
    | _ ->
    if in_rule then e1,[] else
    try
      unif k kForm;
      match e1 with
        EAtom (o,_) when (Data_base.Object.get_value o).origin = Local_hyp ->
          e1,[Hp (get_name o)]
      | _ -> e1,[Gv e1]
    with Clash -> raise (Ill_rule "Not a formula or a Theorem")
  in

  let rec fn in_rule noeq numincr gl0 st0 nl0 prev goal abs opt nb e1 la = function
    0 -> (
      try
	 begin
           match opt with
             [0, OptWith(_::_)] -> raise Exit
           | _ -> ()
         end;
         let is_uni = function
           EApp(EApp(EAtom(o,_),UVar(n,_)),UVar(p,_)) ->
             not (o == equal_obj && n <> p)
         | _ -> false in
         if noeq && tri.from_trivial && nb > 1 &&
            snd (head goal) == equal_obj && is_uni e1 then
           raise (Ill_rule "elim on equations useless");
         if try List.assoc nb opt = OptNoax with Not_found -> false then
           raise (Ill_rule "Allready tried");
	 let tri =
	   if in_rule && noeq then {tri with eqflvl = 1}
	   else tri
	 in
	 let call_trivial = (tri, call_trivial, (gl0, st0, nl0)) in
         if tri.first_order && tri.from_trivial && is_higher_order e1 then
           raise (Ill_rule "Not first order");
	 let hd = the_head e1 in
         let _, rwt, (gl0,st0,nl0) =
           pmatch gl0.eqns gl0.local in_rule false call_trivial e1 goal in
	 if tri.from_trivial && not (linear_uvar hd) then
           raise (Ill_rule "Non trivial matching required");
         (match !lastopt with
           None -> ()
         | Some tbl ->
             if not in_rule then
               lastopt := Some (Map.add nb OptNoax tbl));
         (match !lastcmp with
           None -> ()
         | Some l ->
               lastcmp := Some ((e1, goal)::l));
         (norm_expr prev,norm_expr goal,rwt,la,gl0,st0,nl0)
       with Fail_matching | Exit ->
           if not abs && not (List.exists (equal_expr e1) !lock_intro) then
             fn in_rule noeq numincr gl0 st0 nl0 prev goal abs opt nb e1 la 1 else
           raise (Ill_rule "Goal doesn't match")
         | Free_match ->
           if not abs then
             fn in_rule noeq numincr gl0 st0 nl0 prev goal abs opt nb e1 la 1 else
           raise (Ill_rule "Non deterministic matching"))
  | n ->
      (match (norm_expr e1) with
    EApp(EAtom (o,[k]),(EAbs _ as f)) when o == forall_obj ->
      let continuation_nowith uv =
	let e = norm_expr (EApp (f,uv)) in
        fn in_rule noeq numincr gl0 st0 nl0 prev goal
           abs opt (nb+1) e ((Fl (uv,e1,k))::la) (n - 1)
      in
      let continuation_with lopts uv =
	let e = norm_expr (EApp (f,uv)) in
	let save_ulocal = get_ulocal () in
	let pos = get_undo_pos () in
        try
	  let nopt = [0, OptWith lopts] in
          fn in_rule noeq numincr gl0 st0 nl0 prev goal
            abs nopt (nb+1) e ((Fl (uv,e1,k))::la) (n - 1)
        with Ill_rule _ ->
          set_ulocal save_ulocal;
	  do_undo pos;
          fn in_rule noeq numincr gl0 st0 nl0 prev goal
            abs opt (nb+1) e ((Fl (uv,e1,k))::la) (n - 1)
      in
      begin match opt with
        [0, OptWith(lopt::ls)] ->
	  let rec fn acc = function
              [] -> continuation_nowith (UVar(new_uvar(),k))
	    | NOptFl(e,k') as opt::l ->
		let save_ulocal = get_ulocal () in
		let pos = get_undo_pos () in
		begin try
		  unif k' k;
		  continuation_with (cons_nonempty (List.rev acc@l)  ls) e
		with
		  Clash | Ill_rule _ ->
		    set_ulocal save_ulocal;
		    do_undo pos;
		    fn (opt::acc) l
		end
            | opt::l -> fn (opt::acc) l
	  in fn [] lopt
      | _ ->
	  try
	    match List.assoc nb opt with
	      OptFl e -> type_strong e k; continuation_nowith e
	    | _ -> raise (Ill_rule "Invalid option for a forall")
	  with Not_found | Type_Clash _ ->
	    continuation_nowith (UVar(new_uvar(),k))
      end
  | EApp(EApp(EAtom (o,_),ea),er) ->
     if o != arrow_obj then
       gn in_rule (noeq && o == !and_obj) numincr gl0 st0 nl0 prev
          goal abs opt nb e1 la n else begin
     let continuation_nowith deep_elim =
       let save_ulocal = get_ulocal () in
       let pos = get_undo_pos () in
       try
         fn in_rule noeq numincr gl0 st0 nl0 ea goal abs
           opt (nb+1) er ((Ar(e1,ea,deep_elim))::la) (n - 1)
       with e ->
	 do_undo pos;
	 set_ulocal save_ulocal; raise e
     in
     let continuation_with lopts deep_elim =
       let save_ulocal = get_ulocal () in
       let pos = get_undo_pos () in
       let nopt = [0, OptWith(lopts)] in
       try
         try
           fn in_rule noeq numincr gl0 st0 nl0 ea goal abs
             nopt (nb+1) er ((Ar(e1,ea,deep_elim))::la) (n - 1)
	 with Ill_rule _ ->
           set_ulocal save_ulocal;
	   do_undo pos;
           fn in_rule noeq numincr gl0 st0 nl0 ea goal abs
             opt (nb+1) er ((Ar(e1,ea,NoDeep))::la) (n - 1)
       with e ->
	 do_undo pos;
	 set_ulocal save_ulocal; raise e
     in
     match opt with
       [0, OptWith(lopts)] ->
	 let rec fn ea acc lopts continuation = match lopts with
           []::ls ->
	     begin
	       let save_ulocal = get_ulocal () in
	       let pos = get_undo_pos () in
	       try
		 continuation (List.rev acc::ls) NoDeep
	       with Ill_rule _ -> try
		 do_undo pos;
		 set_ulocal save_ulocal;
		 ignore (decom' ea);
		 let el = UVar(new_uvar(),kForm) in
		 let er = UVar(new_uvar(),kForm) in
		 let and_expr = EApp(EApp(EAtom(!and_obj,[]),el),er) in
		 let nr = snd (smatch gl0.local and_expr ea) in
		 fn el [] (List.rev acc::ls)
		   (fun opts dl ->
		     fn er [] opts (fun opts dr ->
		       continuation opts
			 (if dl = NoDeep && dr = NoDeep then NoDeep else And_intro(nr,dl,dr))))
	       with
		 Clash | Fail_matching | Ill_rule _ -> try
		 do_undo pos;
		 set_ulocal save_ulocal;
		 ignore (decom' ea);
		 let el = UVar(new_uvar(),kForm) in
		 let er = UVar(new_uvar(),kForm) in
		 let and_expr = EApp(EApp(EAtom(!or_obj,[]),el),er) in
		 let nr = snd (smatch gl0.local and_expr ea) in
		 try
		   fn el [] (List.rev acc::ls)
		     (fun opts dl ->
		       if dl = NoDeep then raise Exit;
		       continuation opts (Or_intro(nr,dl,true)))
		 with
		   Exit | Ill_rule _ ->
		     fn er [] (List.rev acc::ls)
		     (fun opts dr ->
		       if dr = NoDeep then raise Exit;
		       continuation opts (Or_intro(nr,dr,false)))
	       with
		 Clash | Fail_matching | Ill_rule _ | Exit -> try
		   do_undo pos;
		   set_ulocal save_ulocal;
		   let ty = mk_Var () in
		   let el = UVar(new_uvar(),KArrow(ty,kForm)) in
		   let er = UVar(new_uvar(),ty) in
		   let exists_expr = EApp(EAtom(!exists_obj,[ty]),el) in
		   let nr = snd (smatch gl0.local exists_expr ea) in
		   let e = norm_expr (EApp(el,er)) in
		   fn e [] (List.rev acc::ls) (fun opts dl ->
		     continuation opts
		       (if dl = NoDeep then NoDeep else Exists_intro(nr,dl,e)))
	       with
		   Clash | Fail_matching | Not_found ->
		     (raise (Ill_rule "An option for Arrow does not match"))
	     end
	 | (NOptFl(e,k) as opt::l)::ls ->
	     let save_ulocal = get_ulocal () in
	     let pos = get_undo_pos () in
	     begin try
	       unif k kForm;
 	       let ax =
		 match e with EAtom(o,_) when
		   (Data_base.Object.get_value o).origin = Local_hyp ->
      		     (try
		       let (_,n,b,_,_) =
			 (List.assoc (get_name o) gl0.hyp) in
		       Some (hyp_to_rule n b)
      		     with
		       Not_found ->
			 raise (Ill_rule (
				"Hypothesis \""^(get_name o)^"\" removed (2).")))
		 | _ -> None
	       in
	       let rr = snd (smatch gl0.local e ea) in
	       continuation (cons_nonempty (List.rev acc@l) ls)
		 (Ax(rr, ax))
	     with
	       Clash | Fail_matching | Ill_rule _ ->
		 do_undo pos;
		 set_ulocal save_ulocal;
		 fn ea (opt::acc) (l::ls) continuation
	     end
         | (opt::l)::ls ->
	     fn ea (opt::acc) (l::ls) continuation
	 | [] ->
	     continuation [] NoDeep
	 in
	 fn ea [] lopts continuation_with
     | _ ->
	 try match List.assoc nb opt with
	   OptFl e ->
	     type_strong e kForm;
	     let ax =
	       match e with EAtom(o,_) when
		 (Data_base.Object.get_value o).origin = Local_hyp ->
      		   (try
		     let (_,n,b,_,_) =
		       (List.assoc (get_name o) gl0.hyp) in
		     Some (hyp_to_rule n b)
      		   with
		     Not_found ->
		       raise (Ill_rule (
			      "Hypothesis \""^(get_name o)^"\" removed (1).")))
	       | _ -> None
	     in
	     continuation_nowith (Ax(snd (smatch gl0.local e ea), ax))
         | OptInt l -> continuation_nowith (Intros l)
         | _ -> raise (Ill_rule "Invalid option for an arrow")
	 with
	   Not_found ->
	     continuation_nowith NoDeep
  end

  | _  -> gn in_rule false numincr gl0 st0 nl0 prev goal abs opt nb e1 la n)

  and gn in_rule noeq numincr gl0 st0 nl0 prev goal abs opt nb e1 la n =
    let f,o,k,u =
      try
        decom in_rule (norm_expr e1)
      with Not_found -> raise (Ill_rule "Tactic elim failed.")
    in
    try
      if no_elim || (in_rule && n > 0) then raise Not_found;
      let l = sort_rules true gl0.local e1 (symhash_find tbl_elim o) in
      let nopt = ref opt in
      let search_opt nb opt =
	try  List.assoc nb opt
	with Not_found ->
	  match opt with
            [0, OptWith(lopt::ls)] ->
	      let rec fn acc = function
                  [] -> raise Not_found
		| NOptDf(str,opt0) as opt::l' ->
		    if List.mem_assoc str l then begin
		      nopt := [0, OptWith(cons_nonempty (List.rev acc@l') ls)];
		      OptDf (str,if opt0 <> [] then [0, OptWith(opt0)] else [])
		    end else fn (opt::acc) l'
                | opt::l' -> fn (opt::acc) l'
	      in fn [] lopt
          | _ -> raise Not_found
      in
      try match search_opt nb opt
      with OptDf (str,opt0) ->
        let (f,th,aux,n0,optinf,_,_) = try List.assoc str l
        with Not_found ->
          raise (Ill_rule "Invalid rule for this connective") in
        let th, f, _ = generalize_for_rules th f aux in
        let (flags, optinf) = match optinf with
            Elim_opt (x::l) -> x, l
          | _ -> failwith "bug 737 in elim" in
        if tri.from_trivial && (isNEC flags) then
          raise (Ill_rule "NEC");
	let pos = get_undo_pos () in
        let save_ulocal = get_ulocal () in (
	  try
	    let (prev',res,_,iel,gl0,st0,nl0) =
	      let opt0 = if opt0 <> [] || not (isLEFT flags) then opt0
              else make_intropt gl0.local intro_names e1 optinf in
              fn true noeq numincr gl0 st0 nl0 (FVar "")
                (UVar(new_uvar(),kForm)) true opt0 1 f [Th th] n0 in
	    let tri = {tri with eqflvl = 1}
	    in
            let call_trivial = (tri, call_trivial, (gl0, st0, nl0)) in
            let _, rwt2, (gl0,st0,nl0) =
              pmatch gl0.eqns gl0.local
		in_rule true call_trivial e1 prev' in
            let abs, nn =
              if isTRM (flags) then true, 0 else abs, n - 1 in
            fn in_rule noeq numincr gl0 st0 nl0 prev goal abs !nopt (nb+1) res
              ((Rl(flags,iel,rwt2))::la) nn
          with
	    e -> do_undo pos; set_ulocal save_ulocal; raise e)
      | OptAfter elim_name ->
          let rec fn = function
              [] -> []
            | (n',_)::_ as l when elim_name = n' -> l
            | _::l -> fn l
          in kn in_rule noeq numincr gl0 st0 nl0 prev
               goal abs opt (nb+1) e1 la n (fn l)
      | OptNoax ->
          kn in_rule noeq numincr gl0 st0 nl0 prev
            goal abs opt (nb+1) e1 la n l
      | _ -> raise (Ill_rule "Invalid option for a defined connective")
      with Not_found ->
        kn in_rule noeq numincr gl0 st0 nl0 prev goal abs opt (nb+1) e1 la n l
    with Not_found ->
      let f = match f with
          Some f -> f
        | None -> raise (Ill_rule "Tactic elim failed.") in
      let u = List.map (fun _ -> LApp) u in
      let ncl = path_subst u e1 f in
      let nla =
        if (Data_base.Object.get_value o).origin = Local_hyp
        then la
        else (Df(e1,u,EAtom(o,k),subst_obj_kind k o))::la
      in fn in_rule false numincr gl0 st0 nl0 prev goal abs opt nb ncl nla n

  and kn in_rule noeq numincr gl0 st0 nl0 prev goal abs opt nb e1 la n = function
    [] -> raise (Ill_rule "Tactic elim failed.")
  | (elim_name,(f,th,aux,n0,optinf,_,_))::ls ->
        if !trace_trivial then begin
	  print_string ("Trying elim named: "^elim_name^" ");
	  print_expr f;
	  print_newline ();
	end;
        let th, f, _ = generalize_for_rules th f aux in
	let pos = get_undo_pos () in
        let save_ulocal = get_ulocal () in
        try
          let (flags, optinf) = match optinf with
            Elim_opt (x::l) -> x, l
          | _ -> failwith "bug 737 in elim" in
          if tri.from_trivial && (isNEC flags) then
            raise (Ill_rule "NEC");
          let ovar = list_uvar e1 in
	  let size_e1 = term_size_rec e1 in
          let (prev',res,_,iel,gl0,st0,nl0) =
            let opt0 = if isLEFT flags then make_intropt gl0.local intro_names e1 optinf
                                       else [] in
            fn true noeq numincr gl0 st0 nl0 (FVar "")
               (UVar(new_uvar(),kForm)) true opt0 1 f [Th th] n0 in
 	  let tri = {tri with eqflvl = 1} in
          let call_trivial = (tri, call_trivial, (gl0, st0, nl0)) in
          let _, rwt2, (gl0,st0,nl0) =
            pmatch gl0.eqns gl0.local in_rule true call_trivial e1 prev' in
	  let did_unif =
	    Set.fold (fun n b -> b ||
			try let _ = getuvar n in true with Not_found -> false)
	      ovar false
	  in
          let abs, nn =
            if isTRM (flags) then true, 0 else abs, n - 1 in
	  let numincr =
	    if term_size_rec res > size_e1 then
	      numincr + 1
	    else numincr
	  in
	  if numincr >= 100 || did_unif then
	    raise (Ill_rule "elim failed (may loop)");
          let r = fn in_rule noeq numincr gl0 st0 nl0 prev goal abs opt
                     nb res ((Rl(flags,iel,rwt2))::la) nn in
          (match !lastopt with
            None -> ()
          | Some tbl ->
              if in_rule then failwith "I think this is a bug";
              lastopt := Some (Map.add (nb-1) (OptAfter elim_name) tbl)); r
        with Ill_rule _ | Fail_matching | Free_match ->
	  do_undo pos;
          set_ulocal save_ulocal;
          let opt = select
            (function _,(OptNoax | OptAfter _) -> false | _ -> true) opt in
          kn in_rule noeq numincr gl0 st0 nl0 prev goal abs opt nb e1 la n ls

  and hn toadd ng nl gl0 st0 = function
    [] -> gl0.ax_test <- false; ((gl0,st0)::ng),nl
  | [Gv e1] ->
(*
      print_string "Given : ";
      print_expr e1;
      print_newline ();
*)
      let gl0 = {gl0 with concl = e1; ax_test = false} in
      ((gl0,st0)::ng),nl
  | [Hp hyp] -> (
(*
      print_string "Hyp : ";
      print_string hyp;
      print_newline ();
*)
      try
        let (_,n,b,_,_) = (List.assoc hyp gl0.hyp) in
        let st = Fol {sref = gl0.gref;rule = hyp_to_rule n b;
                      next = st0} in
        ng, (st::nl)
      with
        Not_found -> raise (Ill_rule ("Hypothesis \""^hyp^"\" removed (3).")))
  | [Th e] ->
(*
      print_string "Theorem : ";
      print_expr e;
      print_newline ();
*)
      let st1 =
        Fol {sref = gl0.gref;rule = Theo e; next = st0} in
      (ng,st1::nl)
  | (Ar(e1,e,deep_elim))::ls ->
(*
      print_string "Arrow : ";
      print_expr e1;
      print_newline ();
      print_expr e;
      print_newline ();
*)
      let e1 = norm_expr e1 in
      let e = norm_expr e in
      let r1 = new_ref () and r2 = new_ref () in
      if (tri.from_trivial) && (toadd && mem_expr true e1 gl0.done_list ||
                              mem_expr false e gl0.done_list) then
          raise (Ill_rule "ADone5");
      let gl1 = {gl0 with gref = r1; concl = e1; ax_test = false;
                 done_list = if toadd then emapadd' e1 gl0.done_list
	           else gl0.done_list} in
      let gl2 = {gl0 with gref = r2; concl = e; ax_test = false;
                 done_list = if toadd then emapadd e gl0.done_list
	           else gl0.done_list} in
      let st1 = Fol {sref = gl0.gref; rule = Arrow_elim (r1,r2); next = st0} in
      let rec jn accnr accnl gl2 st1 = function
	  Ax(rr, ax) ->
	    begin match ax with
	      Some ax ->
		let gl2, st2, accnl = apply_rewrite true accnl gl2 st1 rr in
		let st = Fol {sref = gl2.gref;rule = ax; next = st2} in
		accnr, (st::accnl)
	    |	None ->
		let gl2, st2, accnl = apply_rewrite true accnl gl2 st1 rr in
		(accnr@[gl2,st2]), accnl
	    end
	| And_intro(rr,dl,dr) ->
	   let gl2, st1, accnl = apply_rewrite true accnl gl2 st1 rr in
           (match rule_intro (ref false) tri (Names ["n",Some []]) gl2 st1 with
	   | [(gll,stl);(glr,str)],nl' ->
	      let accnr, accnl = jn accnr (nl'@accnl) gll stl dl in
	      jn accnr accnl glr str dr
           | _ -> assert false)
	| Or_intro(rr,dl,true) ->
	   let gl2, st1, accnl = apply_rewrite true accnl gl2 st1 rr in
           (match rule_intro (ref false) tri (Names ["l",Some []]) gl2 st1 with
	   | [(gll,stl)],nl' ->
	      jn accnr (nl'@accnl) gll stl dl
           | _ -> assert false)
	| Or_intro(rr,dr,false) ->
	    let gl2, st1, accnl = apply_rewrite true accnl gl2 st1 rr in
	    (match rule_intro (ref false) tri (Names ["r",Some []]) gl2 st1 with
            | [(gll,stl)],nl' ->
	       jn accnr (nl'@accnl) gll stl dr
            | _ -> assert false)
	| Exists_intro(rr,d,e) ->
	    let gl2, st1, accnl = apply_rewrite true accnl gl2 st1 rr in
	    (match rule_intro (ref false) tri (Names ["n",Some []]) gl2 st1 with
            | [gl,st],nl' ->
	       ignore (smatch gl.local gl.concl e);
	       jn accnr (nl'@accnl) gl st d
            | _ -> assert false)
	| Intros(l)  ->
	    let l = List.map (fun s -> s,None) l in
            let ng', nl' = rule_intro (ref false) tri (Names l) gl2 st1 in
	    (accnr@ng'), (nl'@accnl)
	| NoDeep ->
	    accnr@[gl2,st1],accnl
      in
      let ng', nl = jn [] nl gl2 st1 deep_elim in
      hn toadd (ng'@ng) nl gl1 st1 ls
  | (Fl (e2,e1,k))::ls ->
(*
      print_string "Forall : ";
      print_expr e2;
      print_newline ();
      print_expr e1;
      print_newline ();
*)
      let e1 = norm_expr e1 in
      let e2 = norm_expr e2 in
      type_strong e2 k;

      if tri.from_trivial && toadd && mem_expr true e1 gl0.done_list then
          raise (Ill_rule "ADone6");
      let gl1 = {gl0 with gref = new_ref(); concl = e1; ax_test = false;
                 done_list = if toadd then emapadd' e1 gl0.done_list
	         else gl0.done_list} in
      let st1 = Fol {sref = gl0.gref; rule = Forall_elim (e2,k);
                     next = st0} in
      hn toadd ng nl gl1 st1 ls
  | (Df (e1,u,e,k))::ls ->
(*
      print_string "Def : ";
      print_expr e1;
      print_newline ();
      print_expr e;
      print_newline ();
*)
      let e1 = norm_expr e1 in
      let rl = Devl_def (Path(u, e), k) in
      let st1 = Fol {sref = gl0.gref; rule = rl; next = st0} in
      let gl1 = {gl0 with gref = new_ref (); concl = e1;
                 ax_test = false } in
      hn toadd ng nl gl1 st1 ls
  | (Rl (flags,iel,rwt2))::ls ->
(*
      print_string "Rewrite : ";
      print_newline ();
*)
      let gl0 = treat_rule gl0 flags in
      let (ng',nl) = hn false [] nl gl0 st0 iel in
      let (gl2,st2),ng' = match List.rev ng' with
          c::ng' -> c,ng'
        | _ -> raise (Failure "bug77 in rule_elim")
      in
      let gl2,st2,nl = apply_rewrite false nl gl2 st2 rwt2 in
      hn toadd ((List.rev ng')@ng) nl gl2 st2 ls
  | _ -> raise (Failure "bug10 in rule_elim")

  in
    let (_,_,rwt,la,gl0,st0,nl) =
      fn in_rule noeq 0 gl0 st0 [] (FVar "") gl0.concl abs
         opt 1 (norm_expr e1) lr n in
    let (gl0,st0,nl) = apply_rewrite false nl gl0 st0 rwt in
    hn (not in_rule) [] nl gl0 st0 la


let get_lefts inv_only from_trivial opt hypname gl0 =
  let hyp,nhyp,bt,status,dleft =
    try List.assoc hypname gl0.hyp
    with Not_found -> raise (Ill_rule ("hypothesis "^hypname^" not found."))
  in
  let can_left o =
    match opt with
      Auth l -> List.memq o l
    | _ -> true
  in
  let rec fn od e =
    let e = norm_expr e in
    try
      let f,o,_,l = decom false e in
      if can_left o then
	let od = o::od in
	let tt = try symhash_find tbl_elim o with Not_found -> [] in
	let tt = select (function (_,(_,e2,_,_,Elim_opt ln,_,_)) ->
	  if from_trivial && (inv_only != None &&
			      !auto_left_lvl <= 1 && fst dleft) ||
	    List.memq e2 (snd dleft) then false else
	    let flags, ln = match ln with
	      flags::ln -> flags, ln
	    | _ -> assert false
	    in
	    let has_cond = List.exists (fun x -> x < 0 && x <> -4) ln in
            isLEFT flags && not (isDND flags)
              && (inv_only = None ||
		  (isINV flags && (!auto_left_lvl > 0 || not has_cond)))
          | _ -> false) tt in
	let tt = List.map (fun (s,x) ->
	  (s,od),x) tt
	in
	if tt = [] then
	  match f with
	    None  -> []
	  | Some f ->
	      if can_open gl0.local o then
		let e1 = norm_sexpr f l in
		fn od e1 else []
	else tt
      else []
    with Not_found -> []
  in hyp, nhyp, bt, status, fn [] hyp


let rec rule_left tri hypname rule_opt inv_only gl0 st0 =
  let tri =
    { tri with nlim = tri.nlim - 2; eqlvl = tri.eqlvl / 40;
      first_order = true; auto_elim = false; eqflvl = min 1 tri.eqflvl
    } in
  if rule_opt = RNum 0 then raise (Ill_rule "left exhausted");

  let hyp, nhyp, bt, status, rules = get_lefts inv_only tri.from_trivial rule_opt hypname gl0 in
  let lefts = sort_rules false gl0.local hyp rules in
  let all_names = List.map (fun x -> fst (fst x)) lefts in

  let rec fn = function
    [] -> raise (Ill_rule "No left rule apply.")
  | ((name,od),(e1,e20,aux,n,ln,_,_))::lefts ->
      try
	if !trace_trivial then begin
	  print_string "trying left rule on hyp: ";
	  print_string hypname;
	  print_string " on goal: ";
	  print_int gl0.gref;
	  print_newline ();
	  print_string "rule is:";
	  print_object e20;
	  print_string ("("^name^")");
	  print_expr e1; print_newline ();
	end;

       let flags, ln = match ln with
          Elim_opt (x::l) -> x,l
        | _ -> failwith "bug 8326" in
        let ln = select (fun x -> x <> -4) ln in
	let od =
	  if rule_opt = Default then
	    if List.memq !exists_obj od then unionq [!and_obj] od
	    else if List.memq !and_obj od then unionq [!exists_obj] od
	    else od
	  else od
	in
        let ll, eopt, rule_opt = match rule_opt with
          Default | Inv_only -> [], [], Auth od
        | Auth _ as a -> [], [], a
        | RNum n ->  [], [], RNum (n-1)
        | Names l ->
	    let l, eopt =
	      if name = "" then  List.map fst l, []
	      else match l with
		[] -> [], []
	      | (x,e)::l when x = name ->
		  List.map fst (List.filter (fun (_,e) -> e = None) l),
		  (match e with None -> [] | Some e -> e)
	      | (x,None)::_ as l when not (List.mem x all_names) ->
		  List.map fst (List.filter (fun (_,e) -> e = None) l),
		  []
	      | (_,_)::_ -> raise (Ill_rule "left failed")
	    in
	    l, eopt, RNum 0
        in
        let e2, _, _ = generalize_for_rules e20 e1 aux in
        let nr, nl =
          rule_elim true tri false true true [0, OptWith eopt] n e2 gl0 st0
        in
        let rec gn accr accl ll ni nr = match nr, ni with
          ((gl1,st1)::nr),(is::ni) ->
	    if isINV flags && tri.from_trivial then begin
	      let fn ((s,(e,pos,b,status,(_,dleft))) as hyp) =
		if s = hypname then  (s,(e,pos,b,status,(true,e20::dleft)))
		else hyp in
	      gl1.hyp <- List.map fn gl1.hyp;
	    end;
            if is < 0 then begin
              if isINV flags (* & tri.from_trivial *) then
		let _, nl = !ftrivial tri [gl1, st1] in
		gn accr (nl@accl) ll ni nr
              else gn (accr@[gl1,st1]) accl ll ni nr
            end else begin
              let gl1, st1, _ =
                if isINV flags && (isREM flags || not tri.from_trivial) &&
		  List.mem_assoc hypname gl1.hyp
		then
                  match rule_rm true [hypname] gl1 st1 with
                    [gl1,st1], [] -> gl1, st1, List.length gl0.hyp - 1
                  | _ -> failwith "bug 0 in rule_left"
                else
		  gl1, st1, List.length gl0.hyp
              in
              let ll1, ll2 =
		let rec hn ni ln = match ni, ln with
                  0, l -> [], l
		| n, (x::l) -> let ll,l = hn (n-1) l in ((x,None)::ll),l
		| n, [] -> let ll,l = hn (n-1) [] in (("",None)::ll),l
		in
		if ll = [] then
                  fst (hn is (get_exists_var true true gl1.local hyp)), []
		else
                  hn is ll
              in
	      let did_inv = ref false in
              (match rule_intro did_inv tri (Names ll1) gl1 st1 with
		[gl1,st1], [] ->
                  let rec fn nr nl(* : state list *) = function
                      [] -> nr, nl
                    | hn::hns ->
			let nnr, nnl = List.fold_right
                            (fun (gl, st) (nr,nl) ->
                              try
				let nr',nl' =
                                  rule_left tri hn rule_opt inv_only gl st
				in nr'@nr, nl'@nl
                              with Ill_rule _ ->
				((gl,st)::nr), nl)
                            nr ([],nl)  in
                        fn nnr nnl hns
                  in if rule_opt = RNum 0 then
                    gn (accr@[gl1,st1]) accl ll2 ni nr
                  else
                    let nnr, nnl = fn [gl1,st1] [] !new_names in
                    gn (accr@nnr) (nnl@accl) ll2 ni nr
	      | _ -> failwith "bug 4 in rule_left")
	    end
        | [_], [] -> accr, accl
        | _ -> failwith "bug 1 in rule_left" in
        let nl =
          let (gl1,st1) = last nr in
          let gl1 = if status = An_eq then
            {gl1 with
             local = remove_local_cst gl1.local [] [nhyp];
             eqns = select_eq [hyp_to_erule hyp nhyp bt] gl1.eqns}
           else gl1
          in
          let r = match rule_axiom true tri hypname gl1 st1 with
            [], nl0 -> nl0@nl
          | _ -> failwith "bug 2 in rule_left" in
	  r
        in
        let r = gn [] nl ll ln nr in
	if !trace_trivial then begin
	  print_string "success of left rule on hyp: ";
	  print_string hypname;
	  print_string "on goal: ";
	  print_int gl0.gref;
	  print_newline ();
	end;
        match inv_only with
          None -> r
        | Some p -> p := ln; r
      with Ill_rule _ -> fn lefts
  in try fn lefts
     with
        Ill_rule _  when not tri.from_trivial &&
                               match rule_opt with RNum _ | Names _ -> true
                                            | _ -> false
            -> raise (Gen_error "left rule do not apply")

let rule_auto_elim tri gl0 st0 =
   let rec fn = function
     [] -> raise Not_found
   | (s,(e,_,_,_,_))::l -> (
       let save_ulocal = get_ulocal () in
       let upos = get_undo_pos () in
       try
	 if List.exists (equal_expr e) !lock_intro then raise Exit;
         let p = ref [] in
         let ovar = list_uvar e in
         let r = rule_left tri s (RNum 1) (Some p) gl0 st0 in
	 Set.iter (fun n ->
	   try let _ = getuvar n in raise Exit with Not_found -> ())
	   ovar;
         r, Some (List.rev !p)
       with
       | Exit | Ill_rule _ | Gen_error _ ->
	   set_ulocal save_ulocal; do_undo upos;
           fn l)
   in fn gl0.hyp


let test_clean_auto_elim nr nl n p st0 st1 father =
  (* looks for cuts between n and p *)
  let rec get_cuts acc st = match st, st0 with
    Fin n, Fin p when n = p -> acc
  | Fol x, Fol y when x.sref = y.sref -> acc
  | Fol x, _ ->
      let acc = match x.rule with
        Cut_rule (_,_,_,q) -> assert (n < q && q < p);
	  Set.add q acc
      | _ -> acc
      in get_cuts acc x.next
  | _ -> failwith "bug 3475 in test_clean_auto_elim"
  in
  let cuts = get_cuts Set.empty st1 in
  (* checks if hypothesys of cuts produced by the left rule have been used *)
  if List.exists (function
    Fol {rule = Axiom q; _} -> n < q && q < p
  | Fol {rule = Subgoal q; _} -> Set.mem q cuts
  | _ -> false) nl
  then
    None
  else begin
    (* remove the memorized cut *)
    List.iter (fun ({done_list = (l,l',m2); _} as gl,_) ->
        let (b,m) = Exprmap.fold (fun k n (b,m) ->
            if Set.mem n cuts then (true, Exprmap.remove k m) else (b, m)
          ) m2 (false, m2) in
        if b then
	  add_to_undo (let old = gl.done_list in fun () -> gl.done_list <- old);
	  gl.done_list <- l,l', m
      ) nr;
    (* remove the useless proof leafes *)
    let tbl = Hashtbl.create 41 in
    Hashtbl.add tbl father true;
    let fst1 = ref None in
    let _ = match st0 with
      Fin _ -> ()
    | Fol x -> Hashtbl.add tbl x.sref false in
    let rec to_keep = function
        Fin _ ->
          true
      | Fol x ->
	  if x.sref = father then fst1 := Some x;
          try Hashtbl.find tbl x.sref
          with Not_found ->
            let b = to_keep (x.next) in
            Hashtbl.add tbl (x.sref) b; b
    in
    let nnl = select to_keep nl in
    let fst1 = match !fst1 with
      None ->  failwith "bug 375 in test_clean_auto_elim"
    | Some fst1 -> fst1 in
    let old_next = fst1.next in
    add_to_undo (let old = fst1.next in fun () -> fst1.next <- old);
    fst1.next <- st0;
    Some (nnl, fst1, old_next)
  end

type goal_typ =
  To_prove of (trinfo * goal * state)
| To_prove_auto of (trinfo * int * int * state * state * int *
                    (goal * state) list)
| Non_unif_mark of bool ref

let rec try_map f = function
  [] -> raise (Ill_rule "Tactic trivial failed.")
| a::l ->
    let su = get_ulocal () in
    let pos = get_undo_pos () in
    try f (l = []) a
    with Ill_rule _ ->
      set_ulocal su; do_undo pos; try_map f l

let mktri tri lim =
  { nlim = lim; eqlvl = tri.eqlvl;
    from_trivial = tri.from_trivial; first_order = tri.first_order;
    auto_elim = tri.auto_elim; eqflvl= tri.eqflvl }

let sort_goals anr =
  let count_intro g =
    try 1 + List.length (snd (get_intros false g.eqns g.local true g.concl))
    with Not_found -> 1
  in
  let anr = List.map (
    function (g, st) ->
      let ctx,_,_,_ = get_ulocal () in
      let d =  depth_uvar ctx g.concl in
      let d = if d <> 0 then d * 10000 / count_intro g else 0 in
(*
      let d = d, - count_intro g in
*)
      (g,st,d)) anr
  in
  let anr =
    let cmp (_,_,d1) (_,_,d2) =
      if d1 > d2 then -1 else 1
    in
    List.sort cmp anr
  in
  List.map (fun (gl,st,_) -> gl,st) anr

let compose_rule rl1 rl2 gl state =
  let (nr,nl) = rl1 gl state in
  let rec fn nr nl = function
      [] -> nr, nl
    | (gl',state')::suit ->
	let (nr',nl') = rl2 gl' state' in
        fn (nr@nr') (nl'@nl) suit
  in
  fn [] nl nr

let map_rule rl rls gl state =
  let (nr, nl) = rl gl state in
  let rec fn nr nl rls nrs = match rls, nrs with
      [], [] -> nr, nl
    | (rl::rls), ((gl',state')::suit) ->
	let (nr',nl') = rl gl' state' in
        fn (nr@nr') (nl'@nl) rls suit
    | _ -> failwith "bug in map_rule"
  in
  fn [] nl rls nr

let sort_rule rl gl state =
  let (nr,nl) = rl gl state in
  (sort_goals nr, nl)

let try_rule rl gl state =
  try
    store "";
    rl gl state
  with
    Ill_rule _ ->
      restore false; [gl, state], []

let orelse_rule rl1 rl2 gl state =
  try
    store "";
    rl1 gl state
  with
    Ill_rule _ ->
      restore false; rl2 gl state

let dispatch_rule rl rls gl state =
  let nr,nl = rl gl state in
  let rec fn accnr accnl nr rls = match nr, rls with
    ((gl,st)::nr), (rl::rls') ->
      let nnr, nnl = rl gl st in
      fn (accnr@nnr) (accnl@nnl) nr (if rls' = [] then rls else rls')
  | [], _ -> accnr, accnl
  | _, [] -> assert false
  in fn [] nl nr rls

let no_rule gl st =
  [gl,st], []

let rule_trivial, mult_trivial  =

  let rec try_taxiom tri dcr bnr anr nl nr = match nr with
    [] ->
      let ntri = match dcr with
	Some f -> mktri tri (tri.nlim - f * (1 + List.length anr))
      | None -> tri
      in
      let anr = List.map (fun (gl,st) -> To_prove(ntri,gl,st))
		  (sort_goals anr) in
      fn (anr@bnr) nl
  | (gl,st as nd)::nr ->
      if !trace_trivial then begin
        print_endline "To prove: ";
        print_string "Goal ref = ";
        print_int gl.gref;
        print_string " trlvl = ";
        print_int tri.nlim;
        print_string " eqlvl = ";
        print_int tri.eqlvl;
	if not tri.auto_elim then print_string "*";
        print_newline ();
        print_goal false false 0 0 gl;
        print_newline ();
(*
	let (r,u,m,l) = get_ulocal () in
	print_nonunifs r l;
        print_newline ();
*)
      end;
      let rec lfn = function
        [] ->
            gl.ax_test <- true;
            try_taxiom tri dcr bnr (nd::anr) nl nr
      | (_,(e,n,b,_,_))::ls ->
          try
            if !trace_trivial then begin
              print_int gl.gref;
              print_string " -- Trying axiom with ";
              print_expr e;
              print_newline ();
            end;
            let save_ulocal = get_ulocal () in
	    let pos = get_undo_pos () in
            let call_trivial = ({tri with eqflvl = 1},
				call_trivial, (gl, st, nl)) in
            let (dm,(gl,st,nl)) =
              let dm, rwt,(gl,st,nl) =
		(if false && tri.nlim > 0 then
                  pmatch gl.eqns gl.local false false call_trivial e gl.concl
		else
		  let a,b = smatch gl.local e gl.concl in
		  a,b,(gl,st,nl)(*c : bug parser de caml ?*))
	      in
              dm, apply_rewrite true nl gl st rwt
            in
            try try_taxiom tri dcr bnr anr (Fol {sref = gl.gref;
              rule = hyp_to_rule n b;
              next = st }::nl) nr
            with Ill_rule _ as exn ->
              set_ulocal save_ulocal;
	      do_undo pos;
              if dm then begin
                (try add_non_unif None [e, gl.concl]
                with Non_unif -> raise (Ill_rule "Non unif"));
                lfn ls
              end else raise exn
            with Fail_matching -> lfn ls
      in
	let hyp =
	  List.map (fun (_,(e,_,_,_,_) as cl) ->
		      dist gl.local gl.concl e, cl)
	    gl.hyp
	in
	let hyp = List.sort (fun (d,_) (d',_) -> compare d d') hyp in
	let hyp = List.map snd hyp in

        if tri.nlim < 0 then raise (Ill_rule "Tactic trivial failed.");

        lfn hyp

  and fn nr st =

      (* let rec show = function
        To_prove (tri,gl,st0)::suit -> print_goal false false 0 0 gl; show suit
      | _::suit -> show suit
      | [] -> ()
      in *)

      match nr with
        (Non_unif_mark b)::suit ->
          (try fn suit st
          with Ill_rule _ as e -> b := true; raise e)

      | (To_prove_auto(tri,n,p,st0,st1,father,nr))::suit -> (
           match test_clean_auto_elim nr st n p st0 st1 father with
             None -> (
               match nr with
                 (gl1,st1 as c)::nr'' ->
                   try_taxiom tri None
                     (To_prove_auto(tri,n,p,st0,st1,gl1.gref,nr'')::suit)
                     [] st [c]
               | [] -> fn suit st)
           | Some (nst, _, _) ->
	       fn suit nst)

      | (To_prove (tri,gl,st0))::suit ->

           (* auto_elim *)

           (try
	     if gl.left_test ||
	       not tri.auto_elim || tri.nlim <= 0 then raise Not_found;
             let n = new_const () in
             if !trace_trivial then begin
               print_int gl.gref;
               print_string " -- Trying auto elim";
               print_newline ();
             end;
	     let r1 = new_ref () in
	     let st1 = Fol {sref = gl.gref; rule = No_rule; next = st0} in
	     let gl1 = {gl with gref = r1} in
             let (nr',st'),drm = rule_auto_elim tri gl1 st1 in
             match drm with
               None ->
                 try_taxiom tri None suit [] (st'@st) nr'
             | Some _ ->
                 let p = new_const () in
                 match nr' with
                   (gl2,st2 as c)::nr'' ->
		     try_taxiom tri None
			 (To_prove_auto(tri,n,p,st1,st2,gl2.gref,nr'')::
			  suit) [] (st'@st) [c]
                 | [] ->
                     try_taxiom tri None suit [] (st'@st) []
           with Not_found ->
	     gl.left_test <- true;
           (* intros *)

           let use_intro = ref false in
           try
	     if List.exists (equal_expr gl.concl) !lock_intro then raise Exit;
             let osize = term_size_rec gl.concl in
             let ovar = list_uvar gl.concl in
             let intros =
               let b, l = get_intros (tri.nlim < 0)
		   gl.eqns gl.local true gl.concl in
               if b then fst (List.split l)@[""] else fst (List.split l)
             in
	     let did_inv = ref false in

	     try_map (fun islast x ->
	     if !did_inv then raise Exit;
             let lastvar = get_uvar (), get_vvar () in
             let nr',st' =
               lastcmp := Some [];
               if !trace_trivial then begin
                 print_int gl.gref;
                 print_string " -- Trying intro ";
                 print_string x;
                 print_newline ();
               end;
               try rule_intro did_inv tri (Names [x,None]) gl st0
               with e -> lastcmp:= None; raise e in
             use_intro := true;
	     let did_unif =
	       Set.fold (fun n b -> b ||
		   try let _ = getuvar n in true with Not_found -> false)
		 ovar false
	     in
	     if !did_inv && did_unif then did_inv:=false;
             let als = match !lastcmp with
               None -> failwith "again a bug 4"
             | Some l -> lastcmp:= None; l in
             let b = ref false in
             let nr' = update_goals nr' in
             let ntri =
               mktri tri (if List.for_all (fun (gl',_) ->
		 term_size_rec gl'.concl < osize) nr'
                 then tri.nlim else tri.nlim - 1)
	     in
             let suit = if suit <> [] then (Non_unif_mark b)::suit
                                      else suit in
             try try_taxiom ntri None suit [] (st'@st) nr'
             with Ill_rule _ as e ->
               if !b && not islast then begin
                 try add_non_unif (Some lastvar) als;
		 with Non_unif when did_unif -> ()
	       end;
               raise e) intros
           with Non_unif | Ill_rule _ | Exit ->

           (* elim *)

           if tri.nlim <= 0 then raise (Ill_rule "Tactic trivial failed.");
           let var_set = list_uvar gl.concl in
	   let compare_hyp (hypn1, _) (hypn2, _) =
	     let f hypn =
	       if List.mem hypn !lock_elim then 2
	       else if String.length hypn >= 5 &&
			 String.sub hypn 0 5 = "NCMD#" then 0
	       else 1
	     in
	     f hypn1 - f hypn2
	   in
	   let hyp = List.sort compare_hyp gl.hyp in
           try_map (fun _ (hypn,(f,_,_,_,dleft)) ->
	     if snd dleft <> [] then raise (Ill_rule "");
(*
	     let new_cmd_hyp = String.length hypn >= 5 &&
			 String.sub hypn 0 5 = "NCMD#" in
*)
	     let tri =
	       if List.mem hypn !lock_elim then
		 {tri with nlim = tri.nlim / 2}
	       (* else if
		 (* List.mem_assoc hypn !new_cmd_opt or *) new_cmd_hyp then
		 {tri with nlim = tri.nlim + 1} *)
	       else tri
	     in
             try
               if !use_intro then
               match fst (head f) with
                 Oneq o ->  let _ = symhash_find tbl_elim_after_intro o in
                           raise (Ill_rule "")
               | _ -> raise Not_found
               else raise Not_found
             with Not_found ->
	       let save_local = !cur_local in
	       cur_local :=
		 List.fold_left (fun l (name, (e,_,_,_,_)) ->
		   add_rhyp l name e) gl.local gl.oldhyp;
               let opt =
	         try
		   let w = List.assoc hypn !new_cmd_opt in
		   let rec fn = function
		       NOptFl(e,k) ->
			 let e = bind_free false 0 [] e in
			 type_strong e k;
			 NOptFl(e,k)
		     | NOptDf(s,l) ->
			 NOptDf(s, List.map (List.map fn) l)
		   in
		   if w = [] then ref [] else
		   ref [0, OptWith (List.map (List.map fn) w)]
		 with
		   Not_found -> ref []
		 | Unbound _ -> ref []
		 | e -> cur_local := save_local; raise e
	       in
	       cur_local := save_local;
	       let depth, abs =
		 try
		   List.assoc hypn !lock_depth, true
		 with
		   Not_found -> 0, false
	       in
               try while true do
                 let save_ulocal = get_ulocal () in
		 let pos = get_undo_pos () in
                 let lastvar = get_uvar (), get_vvar () in
                 let (nr',st'), als = try
                   lastopt := Some Map.empty;
                   lastcmp := Some [];
                   if !trace_trivial then begin
                     print_int gl.gref;
                     print_string " -- Trying elim with ";
                     print_string hypn;
                     print_newline ();
                   end;
                   let r = rule_elim false tri true false
                               abs !opt depth f gl st0 in
                   Set.iter (function p ->
                       if not (linear_uvar (UVar(p,mk_Var()))) then (
                         set_ulocal save_ulocal;
                         raise (Ill_rule "not linear")))
                     var_set;
                   (match !lastopt with
                     None -> failwith "Again a bug"
                   | Some tbl ->
                       opt := Map.fold (fun n o l -> (n,o)::l) tbl [];
                       lastopt := None);
                   match !lastcmp with
                     None -> failwith "Again a bug 2"
                   | Some cpls -> lastcmp := None; r, cpls
                 with
                   e ->
		     lastopt := None; lastcmp := None; raise e in
                 let b = ref false in
                 try
                   let nr' = update_goals nr' in
                   let suit = if suit <> [] then (Non_unif_mark b)::suit
                                      else suit in
(*
		   let factor =
		     if new_cmd_hyp or List.mem_assoc hypn !new_cmd_opt
		     then 1 else 2
		   in
*)
                   raise (Found (try_taxiom tri (Some 1) suit [] (st'@st) nr'))
                 with
                   Ill_rule _ ->
		     do_undo pos;
                     set_ulocal save_ulocal;
                     if !b then add_non_unif (Some lastvar) als;
               done; failwith "bug 567 in trivial" with
                 Found r -> r
               | Non_unif -> raise (Ill_rule "non unif")) hyp)
      | [] -> st

  in

  (fun b lm lp tri gl st ->
   let gn (gl,st,nl) s =
     try let th = aobj (sym_get s) in
     type_strong th kTheorem;
     match rule_use true {tri with from_trivial = false} "" th gl st with
       [gl,st],nl' -> gl,st,(nl'@nl)
     | _ -> raise (Failure "bug 364 in trivial")
     with Not_found -> raise (Ill_rule ("Theorem \""^s^"\" doesn't exists."))
     | Clash -> raise (Ill_rule ("\""^s^"\"is not a theorem."))
   in
   let gl,st = match rule_rm b lm gl st with
     [c],[] -> c
   | _ -> raise (Failure "bug 365 in trivial") in
   let gl,st,nl = List.fold_left gn (gl,st,[]) lp in
   [], try_taxiom tri None [] [] nl [gl,st]),

  (fun tri glsts ->
   [], try_taxiom tri None [] [] [] glsts)


let _ = ftrivial := mult_trivial

let rule_auto b lm lp tri gl st =
  let trlvl = ref 0 in
  let cont = ref true in
  let res = ref ([], []) in
  while !cont do try
    if not !compiling then begin
      print_string "Trying depth ";
      print_int !trlvl;
      print_string " ... ";
      print_flush ();
    end;
    let tri = {nlim = !trlvl; eqlvl = tri.eqlvl;
               from_trivial = tri.from_trivial;
               first_order = tri.first_order;
	       auto_elim = true; eqflvl = !eqflvl
	      } in
    res := rule_trivial b lm lp tri gl st;
    cont := false
  with
    Ill_rule _ ->
      if not !compiling then print_endline "Failed";
      trlvl := !trlvl + !trdepth
  done;
  if not !compiling then print_endline "succeed";
  !res

let rule_theo e gl0 st0 =
  let f = match get_inst e with
      EApp(EApp(_,f),_) -> f
    | _ -> raise (Failure "bug in rule_theo") in
  if not (equal_expr f gl0.concl) then
    raise (Ill_rule "Theorem doesn't match");
  ([],[Fol {sref = gl0.gref;rule = Theo e; next = st0}])

let is_claim o =
  match get_value o with
    Def (EApp(EApp(EAtom(o1,_), _), EAtom(p,_))) ->
      (o1 == theorem_obj) && (p == claim_obj)
  | _ -> false

let is_just_theo o =
  match get_value o with
    Def (EApp(EApp(EAtom(o1,_), _), _)) ->
      (o1 == theorem_obj)
  | _ -> false

let is_theo o f =
  match get_value o with
    Def (EApp(EApp(EAtom(o1,_), g), _)) ->
      (o1 == theorem_obj) && (equal_expr f g)
  | _ -> false

let do_save s exported =
  reset_undo_unif ();
  let gname, name, tname, exported, value, gl, poly =
    match !cur_proof with
      No_proof -> raise (Ill_rule "No proof to save")
    | To_save (v, g, poly, gname, tname, exported') ->
        cur_proof:= No_proof;
	let name = match s, gname with
	  None, None ->
	    raise (Ill_rule "You must give a name to the theorem")
	| Some s, None -> s
	| None, Some s -> s
	| Some s, Some s' when s = s' -> s
	| Some _, Some _ ->
	    raise (Ill_rule "You allready gave another name to the theorem")
	in
	gname, name, tname, (exported && exported'), v, g, poly
    | A_proof ({ goal = e; remain = nr; leaf = lf; _} as prf) ->
	let name = match s, prf.pname with
	  None, None ->
	    raise (Ill_rule "You must give a name to the theorem")
	| Some s, None -> s
	| None, Some s -> s
	| Some s, Some s' when s = s' -> s
	| Some _, Some _ ->
	    raise (Ill_rule "You allready gave a name to the theorem")
	in
  	if prf.remain <> [] then raise (Ill_rule "Proof not finished");
  	cur_proof:= No_proof;
  	save_stack := [];
  	if not !compiling then print_endline "Building proof .... ";
  	let p = build_proof e nr lf None in
  	if not !compiling then print_endline "Typing proof .... ";
  	let k = type_check p in
  	unif k kProof;
  	let goal = norm_expr prf.goal in
  	let v = EApp(EApp(aobj theorem_obj, goal), p) in
  	type_strong v kTheorem;
  	if not !compiling then print_endline "Verifying proof .... ";
 	default_kvar v; default_kvar prf.goal;
  	let f' = proof_check p in
  	type_strong f' kForm;
 	default_kinst v; default_kinst prf.goal;
  	if not (equal_expr goal (norm_expr f')) then raise (Bad_proof 100);
  	if not !compiling then print_endline "Saving proof ....";
  	prf.pname, name, prf.ptex_name,
	  (exported && prf.pexported), Def (norm_expr v),
	norm_expr prf.goal, prf.gpoly
  in
  (try
    let o = sym_get name in
    if is_theo o gl then begin
      if is_claim o then
        print_endline ("claim "^name^" instanciated with a theorem");
      redef_obj o value exported;
      (match tname with
	None -> ()
      |	Some tname -> add_tex_syntax [] o tname Trivial exported);
      not_proof_mode ()
    end else begin
      cur_proof:=To_save (value,gl,poly,gname,tname,exported);
      raise (Failure "Def. Error: This is not a proof of this allready defined theorem.\nYou can save the theorem using another name.")
    end
  with
    Not_found ->
      let o = add_sym name kTheorem value Trivial false exported Idtren (Some poly) in
      if not !compiling then print_newline ();
      (match tname with
	None -> ()
      |	Some tname -> add_tex_syntax [] o tname Trivial exported);
      not_proof_mode ()
  | All_ready_def ->
      open_vbox 0;
      print_string "Def. Error: Can not redefine symbol \"";
      print_string name;
      print_string "\".";
      print_cut ();
      print_string "You can save the theorem using another name.";
      print_newline ();
      cur_proof:=To_save (value,gl,poly,gname,tname,exported);
      raise Error
  | Rec_def ->
      print_endline
        "This proof is using the theorem ! we keep the old proof.";
      not_proof_mode ();
      raise Error);
  reset_local (); reset_ref (); reset_nomatch_set ()

let make_claim name =
  try
    let o = sym_get name in
    match get_value o with
      Def (EApp(EApp(EAtom(o1,k), e), _)) when
	(o1 == theorem_obj) ->
          let v = EApp(EApp(EAtom(o1,k), e), aobj claim_obj) in
          type_strong v kTheorem;
          redef_obj o (Def v) ((get_sym o).exported)
    | _ -> raise Not_found
  with Not_found -> raise (Gen_error (name ^ " is not a theorem"))


let do_claim s tname e exported =
  let p = aobj(claim_obj) in
  let v = EApp(EApp(aobj theorem_obj, e), p) in
  type_strong v kTheorem;
  let o = add_sym s kTheorem (Def v) Trivial false true Idtren None in
  (match tname with
    None -> ()
  | Some tname -> add_tex_syntax [] o tname Trivial exported);
  ()

type depend_arg =
    Axioms
  | All
  | Immediate

let do_depend arg s =
  let o = try sym_get s with Not_found -> raise (Not_def s) in
  if is_claim o then print_endline "This is an axiom." else
  let l =
    match arg with
      Axioms -> get_rlink is_claim o
    | All -> get_rlink is_just_theo o
    | Immediate -> List.filter is_just_theo (get_link o)
  in
  let l = List.map get_name l in
  let l = List.sort compare l in
  if l = [] then
    print_endline "This theorem uses nothing."
  else
    List.iter print_endline l

let do_abort () =
  if !cur_proof <> No_proof
    then cur_proof:= No_proof
    else raise (Ill_rule "Not proving.");
  reset_local (); save_stack := []; reset_ref ();
  not_proof_mode (); set_local 0;
  reset_undo_unif ();
  print_endline "Current proof aborted."

let rule_claim gl st =
  let st1 = Fol {sref = gl.gref;
		 rule = (Claim gl.concl); next = st} in
  [],[st1]

let rule_absurd gl st =
  let tri =
       {nlim = 0; eqlvl = 0;
        from_trivial = false; first_order = false;
	auto_elim = false; eqflvl = 0} in
  let ab_theo = aobj !absurd_obj in

  match rule_elim false tri false
               false false [] 2 ab_theo gl st with
    [gl,st], nl ->
      let ng, nl' = rule_intro (ref false) tri (RNum 1) gl st in
      ng, nl'@nl
  | _ ->
      failwith "bug in rule_absurd"

let rule_contradiction gl st =
  let tri =
       {nlim = 0; eqlvl = 0;
        from_trivial = false; first_order = false;
	auto_elim = false; eqflvl = 0} in
  let ab_theo = aobj !contradiction_obj in

  match rule_elim false tri false
               false false [] 2 ab_theo gl st with
    [gl,st], nl ->
      let ng, nl' = rule_intro (ref false) tri (RNum 1) gl st in
      ng, nl'@nl
  | _ ->
      failwith "bug in rule_absurd"

let rule_apply tri s l n e gl st =
  match rule_use true tri s (UVar(new_uvar (), kForm)) gl st with
    [(gl1, st1); (gl2, st2)], [] ->
      let ng, nl = rule_elim false tri false false false l n e gl1 st1 in
      (ng@[gl2,st2]), nl
  | _ ->
      failwith "bug in rule_absurd"


let try_axiom did_unif auto_lvl nr nl =
    if auto_lvl <= 0 then (nr,nl) else
    let rec kn nl = function
	[] -> [],nl
      | (gl,st as c)::nr ->
	  let nr',nl' = kn nl nr in
	  if gl.ax_test && not did_unif then ((c::nr'),nl') else
	  let old_nomatch_set = !nomatch_set in
	  let gu =
	    if auto_lvl < 3 || !auto_type then list_uvar gl.concl
	    else Set.empty
	  in
	  let rec fn = function
	      [] -> (
		let pos = get_undo_pos () in
		try
		  if not !auto_type then raise Exit;
		  let tri = {nlim = 0; eqlvl = 0;
               		     from_trivial = false; first_order = true;
			     auto_elim = true; eqflvl = 0} in
		  nomatch_set := Set.union !nomatch_set gu;
		  let nr'',nl'' =
		    rule_intro (ref false) tri Inv_only gl st
		  in
		  nomatch_set := old_nomatch_set;
		 kn (nl''@nl') (nr''@nr')
		with Exit | Ill_rule _ ->
		  nomatch_set := old_nomatch_set;
		  do_undo pos;
		  gl.ax_test <- true; ((c::nr'),nl'))
	    | (_,(e,n,b,_,_))::ls ->
		let pos = get_undo_pos () in
		try let (gl,st,nl'') =
		  if auto_lvl > 1 then begin
		    if auto_lvl < 3 then begin
		      let gh = Set.union gu (list_uvar e) in
		      nomatch_set := Set.union !nomatch_set gh
		    end;
		    let _,rwt = smatch gl.local e gl.concl in
		    nomatch_set := old_nomatch_set;
		    apply_rewrite true nl' gl st rwt
		  end else begin
		    if equal_expr e gl.concl then (gl,st,nl')
		    else raise Fail_matching
		  end
		in
		(nr',(Fol {sref = gl.gref;
			   rule= hyp_to_rule n b;
			   next = st }::nl''))
		with Fail_matching ->
		  nomatch_set := old_nomatch_set;
		  do_undo pos; fn ls
	  in
	  let hyp =
	    List.map (fun (_,(e,_,_,_,_) as cl) ->
	      dist gl.local gl.concl e, cl)
	      gl.hyp
	  in
	  let hyp = List.sort (fun (d,_) (d',_) -> compare d d') hyp in
	  let hyp = List.map snd hyp in
	  fn hyp
    in kn nl nr


let do_goal e name tname exported =
  type_form e;
  let e = norm_expr e in
  if !cur_proof <> No_proof then raise (Ill_rule "Already proving.");
  reset_local (); save_stack := []; reset_ref (); reset_dm ();
  set_proof_mode get_goal;
  cur_local := empty_local;
  reset_nomatch_set ();
  let lt = ref (0, []) in
  let e = generalize_expr lt e in
  var_sat_expr e;
  let poly = fst !lt in
  if poly > 0 then begin
    print_string "Warning: this theorem uses ";
    print_int poly;
    print_string " sort parameter(s).";
    print_newline ();
    print_string "Use \"print_sort $0.\" for more details.";
    print_newline ();
  end;
  let gl = {gref = new_ref (); hyp = []; eqns = []; local = empty_local;
             concl = e; ax_test = false; left_test = false;
             done_list= singl_done empty_done e; oldhyp = []} in
  init_undo_unif ();
  cur_proof:=A_proof {goal = e; remain =[gl,Fin 0] ; leaf = []; gpoly = poly;
		      pname = name; ptex_name = tname; pexported = exported};
  do_goals ()

let prove_claim name exported =
  try
    let o = sym_get name in
    match get_value o with
      Def (EApp(EApp(EAtom(o1,_), e), EAtom(p,_))) when
	(o1 == theorem_obj) && (p == claim_obj) ->
	  do_goal e (Some name) None exported
    | _ -> raise Not_found
  with Not_found -> raise (Gen_error (name ^ " is not a claim"))

let do_instance auto_lvl e1 e2 =
  try
    store "instance";
    let k = type_check e2 in
    type_strong e1 k;
    let snomatch_set = !nomatch_set in
    nomatch_set := Set.empty;
    let _ = smatch !cur_local e1 e2 in
    nomatch_set := snomatch_set;
    var_sat_expr e1;
    var_sat_expr e2;
    unlock_instancied ();
    if auto_lvl > 0 then begin
      match !cur_proof with
	A_proof ({ remain = nr; leaf = nl; _} as record) ->
	  let ng = List.length nr in
	  let (nr,nl) =
            try_axiom true auto_lvl nr nl in
	  List.iter (function x -> var_sat (fst x)) nr;
	  let ng' = List.length nr in
	  if not !compiling then begin
            open_hbox ();
            print_int ng;
            print_string (if ng > 1 then " goals " else " goal ");
	    print_endline "possibly instanced.";
            if ng' < ng then begin
              print_string ", with ";
              print_int (ng -ng');
              print_string " automatically solved."
	    end
          end;
	  let nr = update_goals nr in
	  cur_proof := A_proof { record with remain = nr; leaf= nl };
      | _ -> raise (Ill_rule "Not proving.")
    end;
    set_local 0;
    if not !compiling then do_goals ()

  with e -> restore false; raise e

let print_answer b new_goals nr =
(* b : booleen, nr : liste des buts créés, suit : liste des anciens buts.
b:=false : affichage avec syntaxe infixe etc. pour les expressions,
b:= true : arbre (en not. prefixe)  des expressions *)
  let total = List.length nr in
  let fn i (gl,_ as c ) =
    let new_goal = new_goals c in
    if not short_answer then print_goal b new_goal total i gl
	else print_goal b false total i gl
  in
  if proof_general then begin
    list_count fn nr
  end else begin
    list_bcount fn nr;
  end


let do_rule auto_lvl str goal_num rl =
  store str;
  try match !cur_proof with
    A_proof ({goal = f0;remain = remain; leaf = leaf; _} as record) ->
      let leaf = ref leaf in
      let nb_new_goals = ref 0 in
      let did_unif = ref false in
      let treat_one_goal goal_number (gl, state) =
	set_local goal_number;
	let uvars = List.fold_left
	    (fun x (_,(e,_,_,_,_)) -> Set.union x (list_uvar e))
	    (list_uvar gl.concl) gl.hyp
	in
	let (nr,nl) = rl gl state in
	let uvars' = List.fold_left
	    (fun x (_,(e,_,_,_,_)) -> Set.union x (list_uvar e))
	    (list_uvar gl.concl) gl.hyp
	in
	did_unif := !did_unif || not (Set.is_empty (Set.diff uvars uvars'));
	begin
	  match pipe_exit with None -> () | Some ch ->
	    let save = get_formatter_output_functions () in
	    set_formatter_out_channel ch;
            print_string "<proof>";
            print_newline ();
	    let p = build_proof f0 nr nl (Some state) in
	    let fn p (name, (_,n,_,_,_)) =
	      subst_cst n p
		(EApp (aobj comment_obj, EData(Data.EString ("Hypothesis "^name))))
	    in
	    let p = List.fold_left fn p gl.hyp in
	    print_expr_sy true p;
	    print_newline ();
            print_string "</proof>";
            print_newline ();
	    set_formatter_output_functions (fst save) (snd save);
	end;
	nb_new_goals := !nb_new_goals + List.length nr;
	leaf := nl @ !leaf;
	nr
      in
      let nr =
	try
	  flat_select_map treat_one_goal goal_num remain
	with
	  Not_found ->
	    raise (Gen_error (if remain = [] then "Proof finished" else "Bad goal number"))
      in
      let old =
	let rec fn = function
	    (true, _)::l -> fn l
	  | (false, (gl, _))::l -> gl.gref::(fn l)
	  | [] -> []
	in fn nr
      in
      let nr = List.map snd nr in
      let nl = !leaf in
      let ng = !nb_new_goals and ototal = List.length nr in
      let (nr,nl) =
        if auto_lvl > 0 then try_axiom !did_unif auto_lvl nr nl
        else (nr,nl) in
      let total =  List.length nr in
      let solved = ototal - total in
      if not !compiling then begin
        open_hbox ();
        print_int ng;
        print_string " new ";
        print_string (if ng > 1 then "goals" else "goal");
        if solved > 0 then begin
          print_string ", with ";
          print_int solved;
          print_string " automatically solved."
        end else begin
          print_string "."
        end;
        print_newline ();
        print_newline ()
      end;
      let nr = update_goals nr in
      List.iter (fun x -> var_sat (fst x)) nr;
      cur_proof := A_proof { record with remain = nr; leaf= nl };
      let is_new (gl,_) = not (List.mem gl.gref old) in
      if not !compiling then print_answer false is_new nr;
      begin
	match pipe_exit with None -> ()
	| Some ch ->
	    let save = get_formatter_output_functions () in
	    set_formatter_out_channel ch;
	    print_string "<phox>";
	    print_newline ();
	    print_answer true is_new nr;
	    print_string "</phox>";
	    print_newline ();
	    set_formatter_output_functions (fst save) (snd save);
      end;
      set_local 0;
      solved
  | _ -> raise (Ill_rule "Not proving.")
  with e -> restore false; raise e


let _ = fdo_add_close :=
	fun n o -> let _ = do_rule 0 "close_def" n (do_add_close o) in ()

let _ = fdo_add_syntax :=
  fun n o name sy ->
    let _ = do_rule 0 "tex_syntax" n (do_add_syntax o name sy) in ()
