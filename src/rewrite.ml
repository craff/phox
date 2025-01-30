(*######################################################*)
(*			rewrite.ml			*)
(*######################################################*)

open Basic
open Type.Base
open Type
open Local
open Lambda_util
open Print
open Typunif
open Typing
open Af2_basic
open Pattern
open Interact
open Undo
open Safe_add

let left_over = ref []

type env = E of ((expr * env) list) [@@unboced]

let push a (E env) = E(a::env)
let length (E env) = List.length env
let nth (E env) n = List.nth env n

let match_complete loc _unfold e stack () =
  let one_match = ref false in
  let rec fn t1 (env:env) stack =
    match t1 with
      EApp(t1,a) -> fn t1 env ((a,env)::stack)
    | EAbs(_,t1,_) ->
	begin
	  match stack with
	    a::stack -> fn t1 (push a env) stack
	  | _ -> true
	end
    | EVar n ->
	if length env <= n then false
	else begin
	  match nth env n with v, env ->
	    fn v env stack
	end
    | EAtom(o',_) when o' == match_object -> (
	if !one_match then true else
	match stack with
	  (t,env)::stack ->  one_match := true; fn t env stack
	| _ -> assert false)
    | EAtom(o,_) when is_case o ->
        one_match := true;
	let case_name = get_name o in
	let ob =
	  sym_get (String.sub case_name 5 (String.length case_name - 5)) in
	begin
	  match stack with
	    (s,envs)::(f,envf as cf)::((v,envv as cv)::stack as stack0) ->
	      let has_case o' =
		try
		  let _ = sym_get ("case_"^get_name o') in
		  true
		with
		  Not_found -> false
	      in
	      let rec gn nb v (env:env) stack = match v with
		EAtom(o',_) when o' == ob ->
		  let rec hn n e = if (n > 0)
		      then EAbs("x",lift (hn (n-1) e),mk_Var ()) else e
		  in
		  let f = EApp(EVar 0, EVar 1) in
		  let envf = E[cf;cv] in
		  let cf = hn nb f, envf in
		  fn s envs (cf::stack)
	      | EAtom(o',_) when has_case o' ->
		  fn f envf stack0
	      | EVar n ->
		  if length env <= n then false
		  else begin
		    match nth env n with v, env ->
		      gn nb v env stack
		  end
	      | EApp(v,a) ->
		  gn (nb+1) v env ((a,env)::stack)
	      | EAtom(o,_) -> (
		  match get_value o with
		    Def e -> gn nb e (E[]) stack
		  | _ -> false)
	      |	UCst(n,_) -> (
		  try
		    let e, _ = List.assoc n loc.cst_eq in
		    gn nb e (E[]) stack
		  with Not_found -> false)
	      | _ -> false
	      in
	      gn 0 v envv stack
	  | _ -> false
	end
    | EAtom(o,_) -> (
	match get_value o with
	  Def e -> fn e (E[]) stack
	| _ -> true)
    |  UCst(n,_) -> (
	try
	  let e, _ = List.assoc n loc.cst_eq in
	  fn e (E[]) stack
	with Not_found -> true)
    | _ -> true
  in
  fn e (E[]) (List.map (fun e -> e,(E[])) stack)

let analyse_one_theorem eqn unfold ld copt qq e =
  let l0, _ = decompose_eq [] e in
  let find = ref false in
  let gn eqn (e1,e2,nl,andpath,nc,keq) =
    let v = mk_Var() in
      (try
         type_strong e1 v;
         type_strong e2 v
       with
         Clash -> failwith "bug: Ill_types equation");
    let _,_,t1,t2 = saturate e1 e2 nl v keq [] in
    let _,_,t'1,t'2 = saturate e1 e2 nl v keq [] in
    let sy = uni_expr
	       (Map.empty, (norm_expr t1), (norm_expr t2))
		 (Map.empty, (norm_expr t'2), (norm_expr t'1)) in
    let o1,_ = head e1 and o2,_ = head e2 in

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
                rev_append acc ((o2',e1',e2',min nl nl',k',sy',neqtl)::l)
	      with Not_found -> hn (tpl::acc) l)
        | [] ->
            let perm = mk_perm 0 e1 in
            rev_append acc [o2,e1,e2,nl,v,sy,[qq,perm,andpath,ld,nc,copt]]
      in
      try
        let l = assoc_eq o1 eqn in
        add_assq o1 (hn [] l) eqn
      with Not_found ->
        let perm = mk_perm 0 e1 in
        (o1,[o2,e1,e2,nl,v,sy,[qq,perm,andpath,ld,nc,copt]])::eqn
    in
    add eqn ld
  in
  let eqn = List.fold_left gn eqn l0 in
  if not !find then raise Dont_Know_Eq else eqn, unfold


let rec analyse_input gl = function
  [] -> [], []
| (ld,copt,o)::ls ->
    let eqn, unfold = analyse_input gl ls in
    try match  (Data_base.Object.get_value o).fvalue with
      Def (EApp(EApp(EAtom(o',_),e),_)) when o' == theorem_obj ->
	analyse_one_theorem eqn unfold ld copt (Eq_theo o) e
    | Def (EApp(EApp(EAtom(o',_),_),_) as l)
	when o' == theorem_list_cons_obj ->
	let rec fn (eqn, unfold as res) = function
	    EApp(EApp(EAtom(o',_),EAtom(oe,_)),l)
              when o' == theorem_list_cons_obj -> begin
		match (Data_base.Object.get_value oe).fvalue with
		  Def (EApp(EApp(EAtom(o',_),e),_)) when o' == theorem_obj ->
		    fn (analyse_one_theorem eqn unfold ld copt (Eq_theo oe) e) l
		| Def _ ->
		    let s = get_name oe in
		    let (e,n,b,_,_) = List.assoc s gl.hyp in
		    fn (analyse_one_theorem eqn unfold ld copt (hyp_to_erule e n b) e) l
		| _ -> failwith "bug 132 in analyse_input"
	      end
	  | EAtom(o',_) when o' == theorem_list_nil_obj ->
	      res
	  | _ -> failwith "bug 131 in analyse_input"
	in fn (eqn, unfold) l
    | Def _ -> begin
	let s = get_name o in
	try
	  let (e,n,b,_,_) = List.assoc s gl.hyp in
	  analyse_one_theorem eqn unfold ld copt (hyp_to_erule e n b) e
	with Not_found ->
	  eqn, (o::unfold)
      end
    | _ -> raise Not_found
    with
      Gen_error _ | Dont_Know_Eq | Not_found ->
	raise (Gen_error (get_name o ^ " is not an equation."))

let rec eat_LApp = function
  LApp::l -> eat_LApp l
| l -> l

let call_trivial copt tri (gl0,st0,nl0) glsts =
  let tri = {nlim = tri.nlim; eqlvl = 0;
             from_trivial = true; first_order = true;
	    auto_elim = not tri.from_trivial; eqflvl = 1} in
  let fn (ref1,st2,e) (las,gl0,st0,nl0) =
    if mem_expr false e gl0.done_list then
      raise (Ill_rule "call_trivial already failed");
    try
      let n = Exprmap.find e (adone gl0.done_list) in
      let stg = Fol {sref = ref1; rule = Subgoal n; next = st2} in
      let nl2 = stg :: nl0 in
      las,gl0,st0,nl2
    with Not_found ->
      let r1 = new_ref () and r2 = new_ref () and n1 = new_const () in
      let gl1 = {gl0 with gref = r1; concl = e;
                ax_test = false;
                done_list = emapadd e gl0.done_list} in
      let st1 = Fol {sref = gl0.gref;
                     rule = Cut_rule ("G",r1,r2,n1); next = st0} in
      let ndone_list = add_adone gl0.done_list e n1 in
      let stg = Fol {sref = ref1; rule = Subgoal n1; next = st2} in
      let gl2 = {gl0 with gref = r2; done_list = ndone_list} in
      let nl2 = stg :: nl0 in
      ((gl1,st1)::las),gl2, st1, nl2
   in
   let las,gl,st,nl = List.fold_right fn glsts ([],gl0,st0,nl0) in
   if copt then (
     left_over := las @ !left_over;
     gl, st, nl)
   else
     let _, nl1 = mult_trivial tri las in
     gl, st, nl1@nl

let dep_path path p =
  let rec fn = function
    (Req(a1,c,a2,a3,a4,a5,a6,b))::ls -> (Req(a1@path,c,a2,a4,a3,a5,a6,b))::(fn ls)
  | (Rdef(a1,a2,a3,a4,a5,b))::ls -> (Rdef(a1@path,a2,a3,a4,a5,b))::(fn ls)
  | x::ls -> x::(fn ls)
  | [] -> []
  in fn p

let try_eq test tri gst head stack env path eqns =
  let t = norm_sexpr head stack in

  let k0 = fast_type_infer env t in
  let rec hn = function
    [] -> raise Not_found
  | (o1,k1,eqns)::suit ->
      let _,e1,e2,nl,k,_,eqtl =
	match generalize_for_equations [eqns] with
          [o2,e1,e2,nl,k,sy,eqtl] ->
	    o2,e1,e2,nl,k,sy,eqtl
        | _ -> failwith "bug in try_eq"
      in
      store "";
      let rec fix_head e stack =
	try
	  let e' = norm_sexpr e stack in
	  let f,head', k,stack = decom'' e' in
	  if equal_pos_eq o1 head' then begin
	    List.iter2 unif k k1
	  end
	  else match f with
	    None -> failwith "bug -1 in try_eq"
	  | Some e -> fix_head e stack
        with Not_found -> failwith "bug -2 in try_eq"
      in
      let pos = get_undo_pos () in
      try
	fix_head e1 [];
        let (_,largs,t',_) = saturate e1 e2 nl k k0 env in
(*
	let rec truncate largs e1 =
	  match largs, e1 with
	    _::l, EAbs(_,t,_) -> truncate l t
	  | _ -> largs
	in
*)
	let context =
	  EAbs("x",List.fold_left (fun t (u,_) -> EApp(t,u))
		 (EVar 0) (List.map (fun (e,t) -> (lift e,t))
                   (last_in_list (List.length largs - nl)
		    (List.rev largs))),
	       mk_Var ()) in
	let nbargs = List.length largs - 1 in
	let local = match o1 with
	  Oneq o ->
	    {!cur_local with
	     local_close_tbl = o::!cur_local.local_close_tbl}
	| _ -> !cur_local
	in
	let rwt = dep_path path (snd (smatch_env local t t' env)) in
	test 1 (List.length rwt);

	let apply_eqn copt eqnth perm andpath ld =

          let e, st0 = match eqnth with
	      Eq_theo o -> (
		match get_value o with
              Def (EApp(EApp(EAtom(ot,_),e),_)) when ot == theorem_obj ->
                let sref = new_ref () in
                e, {sref = sref; rule = Theo (aobj o); next = Fin (new_fin ())}
		| _ -> failwith "bug 0 in apply_eqn")
            | Eq_axiom (e,n) ->
		let sref = new_ref () in
		e, {sref = sref; rule = Axiom n; next = Fin (new_fin ())}
            | Eq_subgoal (e,n) ->
		let sref = new_ref () in
		e, {sref = sref; rule = Subgoal n; next = Fin (new_fin ())}
          in

          let rec fn las acc st0 perm andpath = function
              EApp(EAtom(o,_),(EAbs(_,_,k) as e)) when
		o == forall_obj ->
		  let sref = new_ref () in
		  let pos, nperm = match perm with
		      [] -> failwith "bug 2 in apply_eqn"
		    | pos::nperm -> pos, nperm
		  in
		  let es, ks = List.nth largs (nbargs - pos) in
		  unif k ks;
		  let st1 = {sref = sref; rule = Forall_elim (es,k);
                             next = Fin (new_fin ())} in
		  st0.next <- Fol st1;
		  fn las acc st1 nperm andpath (norm_sexpr e [es])
            | EApp(EApp(EAtom(o,_),e1),e2) when o == arrow_obj ->
		  let ref1 = new_ref () and ref2 = new_ref () in
		  let st2 = {sref = ref2; rule = Arrow_elim(st0.sref, ref1);
                             next = Fin (new_fin ())} in
		  st0.next <- Fol st2;
		  type_strong e1 kForm;
		  fn ((ref1,Fol st2,e1)::las) acc st2 perm andpath e2
            | EApp(EApp(EAtom(o,_),e1),e2) when o == !and_obj ->
		  let ref3 = new_ref () in
		  let b, nandpath = match andpath with
                      [] -> failwith "bug 5 in apply_eqn"
		    | b::l -> b,l in
		  let st4 = {sref = new_ref ();
                             rule = Arrow_elim (ref3,st0.sref);
                             next = Fin (new_fin ())} in
		  let st3 = {sref = ref3;
                             rule = Forall_elim (e2,kForm);
                             next = Fol st4} in
		  let st2 = {sref = new_ref ();
                             rule = Forall_elim (e1,kForm);
                             next = Fol st3} in
		  let st1 = {sref = new_ref ();
                             rule = Theo (match b with
			       Left_and -> aobj !and_elim_l_obj
                             | Right_and -> aobj !and_elim_r_obj
			     | _ ->	failwith "bug path in apply_eqn");
                         next = Fol st2} in
		  st0.next <- Fol st4;
		  fn las (Fol st1::acc) st4 perm nandpath (match b with
		    Left_and -> e1 | Right_and -> e2 | _ ->
		      failwith "bug path in apply_eqn")
            | EApp(EApp(EAtom(o,_),e1),e2) when o == equal_obj ->
		  (if ld then (e2,e1) else (e1,e2)), st0, acc, las
            | e ->

		let nandpath = match andpath with
		  Open_def::l -> l
		|  _ -> failwith "bug path 2 in apply_eqn" in
		let (f, o, k, u) = decom false e in
		match f with
		  None -> failwith "bug path 3 in apply_eqn"
		| Some f ->
		    let e = EAtom(o,k) in
		    let akind, fe = build_subterm o k u in
		    let ne = norm_expr (EApp(fe,f)) in
		    let st1 =
		      if (Data_base.Object.get_value o).origin = Local_hyp then
			st0
		      else
			let path = List.map (fun _ -> LApp) u in
			let rl = Devl_def (Path(path, e), akind) in
			let st =
			  {sref = new_ref (); rule = rl; next = Fin (new_fin ())} in
			st0.next <- Fol st;
		   st
		    in
		    fn las acc st1 perm nandpath ne
          in
	  let (e1,e2), st, acc, las =
            fn [] [] st0 perm andpath (norm_expr e) in
          let gst = call_trivial copt tri gst las in
          ((rev_path rwt)@
           [Req(path, context, None, e1, e2, st, ((Fol st0)::acc), not ld)]), gst
	in
	let rec try_eqtl = function
            [] -> raise Exit
	  | (eqth,perm,andpath,ld,_,copt)::eqtl ->
              try
		let r = apply_eqn copt eqth perm andpath ld in
		r
              with Ill_rule _ -> try_eqtl eqtl
      in
	let r = try_eqtl eqtl in pop_store ();
	r
        with Clash | Exit | Fail_matching | Ill_rule _ | Fail_saturate ->
	  do_undo pos; restore false;  hn suit
  in
  let sno_match = !no_match in
  try
    no_match := true;
    let r = hn eqns in
    no_match := sno_match;
    r
  with e ->
    no_match := sno_match;
    raise e

type rewrite_opt =
  Ad_lib
| Once_path of path list
| Once_ipath of int list
| Once_nth of int
| Lim of int
| Until of expr
| Ortho of path list list

let global_opt = ref Ad_lib

let rec ipath_to_path l e =
  let rec decom acc = function
    EApp(t,t') -> decom (t'::acc) t
  | _ -> acc in
  match e with
    EAbs(s,e,k) -> PAbs(s,k)::ipath_to_path l e
  | _ ->
      match l with
        [] -> []
      | n::l ->
        let rec fn n args = match n, args with
          1, e::args -> RApp::gn e args
        | n, _::args when n > 1 -> fn (n-1) args
        | _ -> raise (Gen_error "bad path")
        and gn e = function
          [] -> ipath_to_path l e
        | _::args -> LApp::gn e args
        in fn n (decom [] e)

let test_opt path nb = match !global_opt with
  Ad_lib | Until _ -> ()
| Once_path p when equal_path p (eat_LApp path) -> ()
| Once_nth n when n > 0 -> global_opt := Once_nth (n-1); raise Not_found
| Once_nth 0 -> ()
| Lim n when n >= nb -> global_opt := Lim (n-nb)
| Ortho lp ->
    let p = List.rev path in
    let rec fn acc = function
	[] -> p::acc
      | p'::lp ->
	  let rec gn p p' = match p, p' with
	    x::p, x'::p' when x = x' ->
	      gn p p'
	  | [], _::_ ->
	      fn acc lp
	  | _, [] ->
	      raise Not_found
	  | _ -> fn (p'::acc) lp
	  in
	  gn p p'
    in
    global_opt := Ortho (fn [] lp)


| _ -> raise Not_found

let cont_opt e' = match !global_opt with
  Ad_lib -> true
| Until e -> not (equal_expr e e')
| Lim n when n > 0 -> true
| Ortho _ -> true
| _ -> false

let rewrite_one tri gst eqn unfold in_unfold under_lam e =
  let save_fis = !fis_close in

  if in_unfold then fis_close := (fun o -> List.memq o unfold);

  let rec get_eqns do_case acc head k stack =
    let eqn = try
      begin
	match head with
	  Oneq o when is_case o ->
	    if not (Lazy.force do_case) then raise Not_found
	| _ -> ()
      end;
      assoc_eq head eqn with Not_found -> []
    in
    let acc = (List.map (fun x -> (head,k,x)) eqn)@acc in
    if not in_unfold then
      match head with
	Oneq o -> (
	  match get_value o with
	    Def e' when not (!fis_close o) -> (
	      try
		let _, head, k, stack = decom' (norm_sexpr e' stack) in
		get_eqns do_case acc head k stack
	      with Not_found -> acc)
	  |  _ -> acc)
      | _ -> acc
    else acc
  in

  let loc = match gst with (gl,_,_) -> gl.local in
  let r =
    try
      let rec fn path stack env e =
	match e with
        EAtom (o,_) when match get_value o with
          Prg _ -> true | _ -> false -> (
            match get_value o with
              Prg e ->  fn path stack env e
            | _ -> failwith "bug in rewrite_one")
      | EAtom (o,k) as e ->
          if List.memq o unfold then
            match get_value o with
              Def _ ->
                if in_unfold then test_opt path 1 else test_opt path 0;
                [Rdef(eat_LApp path,None,o,k,stack,false)], gst
            | _ -> failwith "bug in rewrite_one"
          else
            let test r l = test_opt path (if in_unfold then r + l else r) in
              try_eq test tri gst e stack env (eat_LApp path)
                (get_eqns (Lazy.from_fun
		   (match_complete loc unfold e stack)) [] (Oneq o) k stack)
      | UCst(n,k) as e ->
          let test r l = test_opt path (if in_unfold then r + l else r) in
          try_eq test tri gst e stack env (eat_LApp path)
                 (get_eqns (Lazy.from_val true) [] (Uneq n) [k] stack)
      | EApp(t,t') -> (
	  match !global_opt with
	    Ortho _ ->
              (try
		fn (RApp::path) [] env t'
              with Not_found ->
		fn (LApp::path) (t'::stack) env t)
	  | _ ->
              try
		fn (LApp::path) (t'::stack) env t
              with Not_found ->
		fn (RApp::path) [] env t')
      | EAbs(s,t,k) as t0 ->
          if stack <> [] then
            fn (eat_LApp path) [] env (norm_sexpr t0 stack)
          else if under_lam then
            fn (PAbs(s,k)::path) [] (k::env) t
	  else raise Not_found
      | UVar (n,_) ->
          fn path stack env (getuvar n)
      | _ -> raise Not_found
      in
      fn [] [] [] e
    with exn -> fis_close := save_fis; raise exn
  in
  if in_unfold then fis_close := save_fis;
  r

let check_recurive unfold in_unfold opt =
  if (List.exists is_recursive unfold) then
    match in_unfold, opt with
      (true, Ad_lib) | (false, _) ->
	raise (Gen_error "unlimited rewrite on recursive definition")
    | _ -> ()

let rule_rewrite tri args opt in_unfold under_lam gl st =
  let save = !left_over in
  try
    left_over := [];
    global_opt := (match opt with
        Once_ipath p -> Once_path (ipath_to_path p gl.concl)
      | _ -> opt);
    let eqn, unfold = analyse_input gl args in
    check_recurive unfold in_unfold opt;
    let one_step (gl,_,_ as gst) =
      let r, (gl,st,nl)  = rewrite_one tri gst eqn unfold in_unfold under_lam gl.concl in
      let (gl,_,_) as res = apply_rewrite true nl gl st r in
      type_strong gl.concl kForm;
      res
    in
    let rec fn gst =
      let (gl,_,_) as gst = one_step gst in
      if cont_opt gl.concl then try fn gst with Not_found -> gst else gst
    in
    let (gl,st,nl) = fn (gl,st,[]) in
    begin
      match !global_opt with
	Until e -> if not (equal_expr e gl.concl) then raise Not_found
      | _ -> ()
    end;
    let r = ([gl,st] @ !left_over),nl in
    left_over := save; r
  with _ -> (* FIXME *)
    left_over := save;
    raise (Ill_rule "rewrite failed")

let apply_rewrite_hyp e0 ls =
  if ls = [] then e0 else
  let rec fn e0 = function
    [] -> e0
  | (Req(path,context,None,e1,_,_,_,_))::ls ->
        let path = List.rev path in
        let e0 = path_subst path e0 (norm_expr(EApp(context,e1))) in
        fn e0 ls
  | (Req(_,_,Some _,_,_,_,_,_))::ls ->
        fn e0 ls
  | (Rdef(path,None,oe,kind,l,dir))::ls ->
        let path = List.rev path in
        let e = EAtom(oe,kind) in
        let _, fe = build_subterm oe kind l in
        let e0 = path_subst path e0
          (if not dir then
            try EApp(fe,kind_inst oe kind)
            with Not_found -> raise (Failure "bug in apply_rewrite")
          else EApp(fe,e)) in
        fn e0 ls
  | (Rdef(_,Some _,_,_,_,_))::ls ->
        fn e0 ls
  | (Insert _)::ls ->
        fn e0 ls
  in fn e0 ls

let tri0 =  { nlim = 0; eqlvl = 0;
    from_trivial = false; first_order = false; auto_elim = true; eqflvl = 0 }

let rule_rewrite_hyp tri args hypname opt in_unfold under_lam gl st =
  let save = !left_over in
  try
    left_over := [];
    global_opt := (match opt with
        Once_ipath p -> Once_path (ipath_to_path p gl.concl)
      | _ -> opt);
    let e, n0, b0, _, _ = List.assoc hypname gl.hyp in
    let eqn, unfold = analyse_input gl args in
    check_recurive unfold in_unfold opt;
    let gl,st = match rule_rm true [hypname] gl st with
      [c],[] -> c | _ -> failwith "bug 1 in rewrite_hyp"
    in
    let one_step (rwt, gst, e) =
      let r, gst  = rewrite_one tri gst eqn unfold in_unfold under_lam e in
      let e = apply_rewrite_hyp e r in
      type_strong e kForm;
      ((rev_path r)@rwt, gst, e)
    in
    let rec fn x =
      let (_,_,e) as x = one_step x in
      if cont_opt e then try fn x with Not_found -> x else x
    in
    let rwt, (gl,st,nl), e = fn ([], (gl,st,[]), e) in
    begin
      match !global_opt with
	Until e' -> if not (equal_expr e' e) then raise Not_found
      | _ -> ()
    end;
    let (gl1,st1),(gl2,st2) = match rule_use true tri0 hypname e gl st with
      [c1;c2], [] -> c1, c2 | _ -> failwith "bug 2 in rewrite_hyp"
    in
    let gl1,st1,nl = apply_rewrite true nl gl1 st1 rwt in
    let nl = (Fol {sref = gl1.gref;rule = hyp_to_rule n0 b0;
         next = st1}::nl) in
    let r = ([gl2,st2] @ !left_over),nl in
    left_over := save; r
  with _ -> (* FIXME *)
    left_over := save;
    raise (Ill_rule "rewrite failed")

let make_th_list name list export =
  let rec fn = function
    [] ->
      EAtom(theorem_list_nil_obj,[])
    | o::l ->
	let e = aobj o in
        type_strong e kTheorem;
	EApp(EApp(EAtom(theorem_list_cons_obj,[]),e), fn l)
  in
  let l = fn list in
  let _ = add_sym name kTheorem_list (Def l) Trivial false export Idtren None
  in ()
