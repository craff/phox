(*######################################################*)
(*			inductive.ml			*)
(*######################################################*)

open Basic
open Lex
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
open Pattern
open Flags
open Interact
open Rewrite
open Option

(* this function test if all the arguments of the inductive predicate
   are useful and removes the useless ones *)

let in_inductive = ref false

type global_options =
  Claim_elim | Claim_case | Non_disjoint | Typed

type local_options =
  Claim_intro | Non_injective | Invertible | Constructor | Totality

let check_args kX le intros =
  let tbl = ref Set.empty in
  let arity = List.length le in

  let rec hn n = function
    EAbs(_,t,_) -> hn (n+1) t
  | t -> t
  in

  let gn (_, intro) =
    let intro = EApp(intro, UCst(-1,kX)) in
    hn 0 (norm_expr intro)
  in

  let tintros = List.map gn intros in

  let rec fn depth stack = function
    EApp(t,u) -> fn depth (u::stack) t
  | EAbs(_,t,_) ->
	if stack <> [] then failwith "bug in check_args";
	fn (depth+1) [] t
  | UCst(-1,_) ->
	let rec fn n = function
          [] ->
	   for i = n downto 0 do
	     tbl := Set.add i !tbl;
	   done
        | EVar p::l when p = n + depth ->
            fn (n-1) l
        | _::l ->
           tbl := Set.add n !tbl;
           fn (n-1) l
        in fn (arity-1) stack
  | _ -> List.iter (fn depth []) stack
  in

  List.iter (fn 0 []) tintros;

  let nkX = mk_Var () in

  let rec fle n =
    if n = arity then UCst(-1,nkX) else
    let t = fle (n+1) in
    if Set.mem n !tbl then EApp(t,EVar (n+1)) else t
  in

  let found =
    try
      for i = 0 to arity-1 do
        if not (Set.mem i !tbl) then raise Exit
      done;
      false
    with
      Exit -> true
   in

   if found then begin
     let rec fa n t =
       if n = 0 then t else
       let n = n - 1 in
       let t = if Set.mem n !tbl then
         EApp(t, EVar n) else t
       in
       fa n t
     in
     let rec fl n t =
       if n = 0 then t else
       fl (n-1) (EAbs("x",t,mk_Var ()))
     in
     let tf = fl arity (fa arity (EVar(arity))) in

     nkX, fle 0, List.map (fun (n,t) -> n,
       norm_expr (EAbs("X",EApp(t,tf), nkX))) intros

   end else
     kX, fle 0, intros


let build_elim op kX le intros =

  let rec fn stack = function
    EApp(t,u) -> fn (u::stack) t
  | EAbs(n,t,k) ->
      if stack <> [] then failwith "bug 1 in build_elim";
      EAbs(n,fn [] t,k)
  | UCst(-1,_) as t ->
      List.fold_left (fun t u -> EApp(t,u)) t stack
  | EAtom(o,_) as f when o == forall_obj ->
      begin
	match stack with
	  [t] -> EApp(f, fn [] t)
	| _ -> failwith "bug 2 in build_elim"
      end
  | EAtom(o,_) as f when o == arrow_obj ->
      begin
	match stack with
	  [t; u] ->
	    let u = fn [] u in
	    if occur (-1) t then
              let t' = subst_cst (-1) t (aobj op) in
	      EApp(EApp(f,t'),EApp(EApp(f, t), u))
	    else
	      EApp(EApp(f, t), u)
	| _ -> failwith "bug 3 in build_elim"
      end
  | _ -> failwith "bug 4 in build_elim"

  in
  let gn (n, intro) =
    let intro = EApp(intro, UCst(-1,kX)) in
    (n, bind_cst "X" (-1) (fn [] (norm_expr intro)) kX)
  in

  let _, _, cintros = check_args kX le (List.map gn intros) in
  cintros

let build_case op kX le intros =

  let forget = ref [] in

  let rec fn depth real_depth stack = function
    EApp(t,u) -> fn depth real_depth (u::stack) t
  | EAbs(n,t,k) ->
      if stack <> [] then failwith "bug 1 in build_elim";
      EAbs(n,fn depth (real_depth + 1) [] t,k)
  | UCst(-1,_) as t ->
      let t0 = List.fold_left (fun t u -> EApp(t,u)) t stack in
      let teq v (t,n) =
        let eq v = EApp(EApp(aobj(arrow_obj),EApp(EApp(aobj(equal_obj),EVar n),v)),t) in
	match v with
	  EVar p when p = n -> (t, n+1)
	| EVar p when List.for_all (fun (_,n') -> real_depth - n - 1 <> n') !forget ->
	    if List.mem_assoc (real_depth - p - 1) !forget then
              eq v, n + 1
            else begin
              forget := (real_depth - p - 1, real_depth - n - 1)::!forget;
	      t, n+1
            end
	| _ -> eq v, n+1
      in
      fst (List.fold_right (fun u t -> teq u t) stack (t0, depth) )
  | EAtom(o,_) as f when o == forall_obj ->
      begin
	match stack with
	  [t] ->
	    let next = fn (depth + 1) real_depth [] t in
	    (try
	      let n = List.assoc real_depth !forget in
	      EApp(next, EVar (real_depth - n - 1))
	    with Not_found ->
	      EApp(f, next))
	| _ -> failwith "bug 2 in build_elim"
      end
  | EAtom(o,_) as f when o == arrow_obj ->
      begin
	match stack with
	  [t; u] ->
	    let u = fn depth real_depth [] u in
	    if occur (-1) t then
              let t' = subst_cst (-1) t (aobj op) in
	      EApp(EApp(f, t'),u)
	    else
	      EApp(EApp(f, t), u)
	| _ -> failwith "bug 3 in build_elim"
      end
  | _ -> failwith "bug 4 in build_elim"

  in
  let gn (n, intro) =
    let intro = EApp(intro, UCst(-1,kX)) in
    (n, (forget := []; bind_cst "X" (-1) (fn 0 0 [] (norm_expr intro)) kX))
  in

  let nkX, nle, cintros = check_args kX le (List.map gn intros) in
  nkX, nle, cintros

let inductive export name sy go kX le tname intros =
  (* definition of the predicate *)
  let nkX, nle, cintros = check_args kX le intros in
  let e0 = UCst(-1,nkX) in
  let rec hn n e = function
    [] -> e
  | _::l -> EApp(hn (n+1) e l, EVar n)
  in
  let hn' e =
    hn 1 (EApp(e, e0)) le
  in
  let rec kn e = function
    [] -> e
  | (s,k)::l ->	EAbs(s,kn e l,k)
  in
  let rec gn = function
    [] -> nle
  | (_, ei)::l ->
	EApp(EApp(aobj(arrow_obj), hn' ei), gn l)
  in
  let pred = kn (EApp(aobj(forall_obj), bind_cst "X" (-1) (gn cintros) nkX)) le in
  let pred = norm_expr pred in
  let k = type_check pred in
  let o = add_sym name k (Def pred)
	       sy false export Idtren None in
  let const = ref [o] in
  try
  (* intro rules *)

  let fn ((name, lo), intro) =
    let rec kn e = function
      [] -> e
    | (s,k)::l ->
	let t = kn e l in
	try unlift t
	with Exit ->
	  EApp(aobj forall_obj, EAbs(s,t,k))
    in
    let intro =
      kn (norm_expr (hn 0 (EApp(intro, aobj o)) le)) le
    in
    type_form intro;
    if (List.mem Claim_intro lo) then
      do_claim (name^"."^tname) None intro export
    else begin
      do_goal intro (Some (name^"."^tname)) None export;
      let tri = {nlim = !trdepth; eqlvl = 0;
		 from_trivial = false; first_order = false;
		 auto_elim = true; eqflvl = 0} in
      let _ = do_rule 1 "intros" [1]
		(compose_rule
		   (rule_intro (ref false) tri Default)
		   (compose_rule
		      (try_rule (rule_intro (ref false) tri Default))
	              (try_rule (rule_auto true [] [] tri)))) in
      do_save None export
    end;
    ((name, lo), intro), (name, sym_get  (name^"."^tname))
  in
  let intro_theos, intro_objs = List.split (List.map fn intros) in
  const := (List.map snd intro_objs) @ !const;
  let adds ((_, lo), _) (name, th) =
    let invertible = List.mem Invertible lo in
    let constructor = List.mem Constructor lo in
    let totality = constructor || List.mem Constructor lo in
    add_intro constructor totality false invertible name th 0.0 export
  in
  List.iter2 adds intro_theos intro_objs;

  (* induction rule *)

  let eintros = build_elim o kX le intros in
  let e0 = UCst(-1,nkX) in
  let rec hn n e = function
    [] -> e
  | _::l -> EApp(hn (n+1) e l, EVar n)
  in
  let hn' e =
    hn 0 (EApp(e, e0)) le
  in
  let rec gn = function
    [] -> EApp(EApp(aobj(arrow_obj), hn 0 (aobj o) le), unlift nle)
  | (_, ei)::l ->
	EApp(EApp(aobj(arrow_obj), hn' ei), gn l)
  in
  let rec knf e = function
      [] -> e
  | (s,k)::l -> EApp(aobj forall_obj, EAbs(s,knf e l,k))
  in
  let elim = norm_expr
    (EApp(aobj(forall_obj), bind_cst "X" (-1) (knf (gn eintros) le) nkX)) in
  type_form elim;
  if (List.mem Claim_elim go) then
      do_claim ("rec."^tname) None elim export
  else begin
    do_goal elim (Some ("rec."^tname)) None export;
    let tri = {nlim = !trdepth; eqlvl = 0;
               from_trivial = false; first_order = false;
	       auto_elim = true; eqflvl = 0} in
    let _ = do_rule 1 "intros" [1] (rule_intro (ref false) tri Default) in
    let gl = match !cur_proof with
	A_proof {remain = [gl,_]; _} -> gl
      | _ -> failwith "bug in Inductive (proving elim)"
  in
    let (hypname, (hyp,_,_,_,_)) = List.hd gl.hyp in
    let cutform = EApp(EApp(aobj !and_obj, hyp), gl.concl) in
    let _ = do_rule 1 "use" [1] (rule_use true tri "" cutform) in
    let eform = aobj (sym_get hypname) in
    let do_case n gl st =
      (map_rule
         (rule_intro (ref false) tri (Auth[forall_obj;!and_obj;arrow_obj]))
         [rule_intro (ref false) tri (Names [fst (List.nth intro_objs n),None]);
          let total = List.length gl.hyp in
          let pos = total - n - 1 in
	  let eform = aobj (sym_get (fst (List.nth gl.hyp pos))) in
          rule_elim false tri false false false [] 0 eform] gl st) in
    let rec rls = function
      0 -> []
    | n -> do_case (n-1)::rls (n-1) in
    let _ = do_rule 1 "elim+auto" [1]
	      (compose_rule
		 (map_rule
                    (rule_elim false tri false false false [] 1 eform)
                    (List.rev (rls (List.length intro_objs))))
		 (rule_auto true [] [] tri)) in
    let _ = do_rule 1 "auto" [1] (rule_auto true [] [] tri) in
    do_save None export
  end;
  let elim_obj = sym_get ("rec."^tname) in
  const := elim_obj :: !const;
  add_elim o "rec" 1 elim_obj fNONE 0.0 export;

  (* case rule *)

  let nkX, nle, eintros = build_case o kX le intros in
  let e0 = UCst(-1,nkX) in
  let rec hn n e = function
    [] -> e
  | _::l -> EApp(hn (n+1) e l, EVar n)
  in
  let hn' e =
    hn 0 (EApp(e, e0)) le
  in
  let rec gn = function
    [] -> EApp(EApp(aobj(arrow_obj), hn 0 (aobj o) le), unlift nle)
  | (_, ei)::l ->
	EApp(EApp(aobj(arrow_obj), hn' ei), gn l)
  in
  let rec knf e = function
      [] -> e
  | (s,k)::l -> EApp(aobj forall_obj, EAbs(s,knf e l,k))
  in
  let case = norm_expr
    (EApp(aobj(forall_obj), bind_cst "X" (-1) (knf (gn eintros) le) nkX)) in
  type_form case;
  if (List.mem Claim_case go) then
      do_claim ("case."^tname) None case export
  else begin
    do_goal case (Some ("case."^tname)) None export;
    let tri = {nlim = !trdepth; eqlvl = !eqdepth;
               from_trivial = false; first_order = false;
	       auto_elim = true; eqflvl = 0} in
    let _ = do_rule 1 "intros" [1] (rule_intro (ref false) tri Default) in
    let gl = match !cur_proof with
	A_proof {remain = [gl,_]; _} -> gl
      | _ -> failwith "bug in Inductive (proving elim)"
    in
    let (hypname, _) = List.hd gl.hyp in
    let cutform = List.fold_left (fun t (_, (hyp,_,_,_,_)) ->
				    EApp(EApp(aobj arrow_obj, hyp), t)) gl.concl (List.tl gl.hyp) in
    let _ = do_rule 1 "use" [1] (rule_use true tri "" cutform) in
    let eform = aobj (sym_get hypname) in
    let _ = do_rule 1 "elim+auto" [1]
	    (compose_rule
	       (rule_elim false tri false false false [] 1 eform)
	       (rule_auto true [] [] tri)) in
    let _ = do_rule 1 "auto" [1] (rule_auto true [] [] tri) in
    do_save None export
  end;
  let case_obj = sym_get ("case."^tname) in
  const := case_obj :: !const;
  add_elim o "case" 1 case_obj fNONE 0.0 export;
  add_close_def [0] o export;
  intro_theos

  with e ->
    List.iter (rec_remove false !the_base) !const;
    raise e

let make_case typed export _ (_, intro) co intros objs =
  let cname = get_name co in
  let case_name = "case_" ^ cname in
  let k = mk_Var () in
  let k' = get_safe_kind co in
  let rec fn = function
      KArrow(k,k') -> let a,b = fn k' in KArrow(k,a), b
    | b -> k, KArrow(b,k)
  in
  let a, b = fn k' in
  let case_kind = KArrow (KArrow(a,a),KArrow(b,b)) in
  let case_obj = add_sym case_name case_kind Cst
		 Trivial false export Idtren None in

  let rec decom l = function
      EApp(t,u) ->
	decom (u::l) t
    | EAtom(_,_) -> l
    | _ -> failwith "bug in make_injective"
  in
  let rec fn = function
      EApp(EAtom(o,k),EAbs(s,t,k')) when o == forall_obj ->
	let t = fn t in
	begin
	  try unlift t
	  with Exit -> EApp(EAtom(o,k),EAbs(s, t,k'))
	end
    | EApp(EApp(EAtom(o,k),t),u) when o == arrow_obj ->
	let u = fn u in
	if typed then
	  EApp(EApp(EAtom(o,k),t), u)
	else
	  u
    | EApp(_,t) ->
	let t = mlift 2 t in
	let l = decom [] t in
	let v = List.fold_left (fun acc _ ->
	  EAbs("_", lift acc, mk_Var ())) (EApp(EVar 0,t)) l in
	EApp(aobj forall_obj,EAbs("f",
	  EApp(aobj forall_obj,EAbs("e",
	    EApp(EApp(aobj equal_obj,
	      EApp(EApp(EApp(aobj case_obj, EVar 1), EVar 0), t)),
	      List.fold_left (fun t u ->
		EApp(t,u)) (EApp(EVar 1, v)) l),
	  mk_Var ())),mk_Var ()))
    | _ -> assert false
  in
  let rule = fn intro in
  type_form rule;
  let claim_name = "case_"^cname^"_"^cname in
  do_claim claim_name None rule export;
  let claim = sym_get claim_name in
  add_rewrite 0 claim export;

  let rec md acc intros objs =
    match intros, objs with
      (_::suit), (co'::suit') when co == co' ->
	md acc suit suit'
    | [], [] -> acc
    | ((_, intro')::suit), (co'::suit') ->
	let rec fn = function
	    EApp(EAtom(o,k),EAbs(s,t,k')) when o == forall_obj ->
	      let t = fn t in
	      begin
		try unlift t
		with Exit -> EApp(EAtom(o,k),EAbs(s, t,k'))
	      end
	  | EApp(EApp(EAtom(o,k),t),u) when o == arrow_obj ->
	      let u = fn u in
	      if typed then
		EApp(EApp(EAtom(o,k),t), u)
	      else
		u
	  | EApp(_,t) ->
	      let t = mlift 2 t in
	      EApp(aobj forall_obj,EAbs("f",
	        EApp(aobj forall_obj,EAbs("e",
	          EApp(EApp(aobj equal_obj,
	            EApp(EApp(EApp(aobj case_obj, EVar 1), EVar 0), t)),
	      	    EApp(EVar 0, t)),
	        mk_Var ())),mk_Var ()))
	  | _ -> assert false
	in
	let rule = fn intro' in
	type_form rule;
	let claim_name = "case_"^cname^"_"^(get_name co') in
	do_claim claim_name None rule export;
	let claim = sym_get claim_name in
	add_rewrite 0 claim export;
	md (claim::acc) suit suit'
    | _ -> assert false
  in
  let l = md [claim] intros objs in
  make_th_list "eval" l export


let make_injective typed export tname ((name, lo), intro) = try
  if (List.mem Non_injective lo) then raise Exit;
  let rec decom l = function
      EApp(t,u) ->
	decom (u::l) t
    | EAtom(_,_) -> l
    | _ -> failwith "bug in make_injective"
  in
  let rec fn = function
      EApp(EAtom(o,k),EAbs(s,t,k')) when o == forall_obj ->
	let t, t' = fn t in
	begin
	  try unlift t, unlift t'
	  with Exit ->
	    EApp(EAtom(o,k),EAbs(s, t,k')),
	    EApp(EAtom(o,k),EAbs(s, t',k'))
	end
    | EApp(EApp(EAtom(o,k),t),u) when o == arrow_obj ->
	let u, u' = fn u in
	if typed then
	  EApp(EApp(EAtom(o,k),t), u), EApp(EApp(EAtom(o,k),t), u')
	else
	  u, u'
    | EApp(_,t) ->
	let l = decom [] t in
	if l = [] then raise Not_found;
	let rec gn depth = function
	    EApp(EAtom(o,k),EAbs(s,t,k')) when o == forall_obj ->
	      let t, t' = gn (depth+1) t in
	      begin
		try unlift t, unlift t'
		with Exit ->
		  EApp(EAtom(o,k),EAbs(s, t,k')),
		  EApp(EAtom(o,k),EAbs(s, t',k'))
	      end
	  | EApp(EApp(EAtom(o,k),t),u) when o == arrow_obj ->
	      let u, u' = gn depth u in
	      if typed then
		EApp(EApp(EAtom(o,k),t),u), EApp(EApp(EAtom(o,k),t),u')
	      else
		u,u'
	  | EApp(_,t') ->
	      let l' = decom [] t' in
	      let t = mlift depth t in
	      let l = List.map (mlift depth) l in
	      let hyp =
		List.fold_left2 (fun e a a' ->
		   EApp(EApp(aobj arrow_obj,
			     EApp(EApp(aobj equal_obj, lift a), lift a')), e))
		  (EVar 0) l l' in
	      let right' = EApp(EApp(aobj equal_obj, t), t') in
	      let right =
		EApp(EApp(aobj arrow_obj, lift right'), EVar 0)
	      in
	      EApp(EApp(aobj arrow_obj, right'),
	        List.fold_left2 (fun e a a' ->
		  let t = EApp(EApp(aobj equal_obj, a), a') in
	          if e = FVar "" then t else
		  EApp(EApp(aobj !and_obj, e), t))
		    (FVar "") l l'),
	      EApp(aobj forall_obj,
		   EAbs("X",
			EApp(EApp(aobj arrow_obj, hyp), right) , kForm ))
           | _ -> failwith "bug1 in make_injective"
	in gn 0 intro
     | _ -> failwith "bug2 in make_injective"
  in
  let rule, rule' = fn intro in
  type_form rule; type_form rule';
  do_claim (name^"_inj."^tname) None rule export;
  let claim = sym_get (name^"_inj."^tname) in
  do_goal rule' (Some (name^"_inj'."^tname)) None export;
  let tri = {nlim = !trdepth; eqlvl = !eqdepth;
             from_trivial = false; first_order = true;
	     auto_elim = true; eqflvl = 0} in
  let _ = do_rule 1 "use" [1] (rule_use true tri "" (aobj claim)) in
  let _ = do_rule 1 "intros" [1] (rule_intro (ref false) tri Default) in
  let gl = match !cur_proof with
      A_proof {remain = [gl,_]; _} -> gl
    | _ -> failwith "bug in Data (proving inj')"
  in
  let (hypname1, _) = List.hd gl.hyp in
  let eform1 = aobj (sym_get hypname1) in
  let (hypname2, _) = List.hd (List.tl gl.hyp) in
  let eform2 = aobj (sym_get hypname2) in
  let (hypnamen, _) = last gl.hyp in
  let eformn = aobj (sym_get hypnamen) in
  let rec count = function
      EApp(EAtom(o,_),EAbs(_,t,_)) when o == forall_obj ->
	1 + count t
    | EApp(EApp(EAtom(o,_),_),u) when o == arrow_obj ->
	1 + count u
    | EAtom(o,k) ->
	(try
	  count (kind_inst o k)
	with Not_found -> 0)
    | _ -> 0
  in
  let pos = count eformn in
  let _ = do_rule 1 "apply" [1] (compose_rule
	    (sort_rule (rule_apply tri "" [pos, OptFl eform1] pos eformn))
	    (orelse_rule (try_rule (rule_trivial true [] [] tri))
            (compose_rule
	       (rule_elim false tri false false false [] 1 eform2)
	       (rule_auto true [] [] tri)))) in
  do_save None export;
  let rule'_obj = sym_get (name^"_inj'."^tname) in
  add_elim equal_obj (name^"_inj") 1 rule'_obj (fINV land fNEC) 0.0 export;
  true

with Exit -> false | Not_found -> true

let make_distinct typed export tname ((name1, _), intro1) ((name2, _), intro2) =
  let rec fn = function
      EApp(EAtom(o,k),EAbs(s,t,k')) when o == forall_obj ->
	let t, t' = fn t in
	begin
	  try unlift t, unlift t'
	  with Exit ->
	    EApp(EAtom(o,k),EAbs(s, t,k')),
	    EApp(EAtom(o,k),EAbs(s, t',k'))
	end
    | EApp(EApp(EAtom(o,k),t),u) when o == arrow_obj ->
	let u, u' = fn u in
	if typed then
	  EApp(EApp(EAtom(o,k),t),u), EApp(EApp(EAtom(o,k),t),u')
	else
	  u, u'
    | EApp(_,t) ->
	let rec gn depth = function
	    EApp(EAtom(o,k),EAbs(s,t,k')) when o == forall_obj ->
	      let t, t' = gn (depth+1) t in
	      begin
		try unlift t, unlift t'
		with Exit ->
		  EApp(EAtom(o,k),EAbs(s, t,k')),
		  EApp(EAtom(o,k),EAbs(s, t',k'))
	      end
	  | EApp(EApp(EAtom(o,k),t),u) when o == arrow_obj ->
	      let u, u' = gn depth u in
	      if typed then
		EApp(EApp(EAtom(o,k),t),u), EApp(EApp(EAtom(o,k),t),u')
	      else
		u,u'
	  | EApp(_,t') ->
	      let t = mlift depth t in
	      EApp(EApp(aobj !diff_obj, t), t'),
	      EApp(EApp(aobj !diff_obj, t'), t)
          | _ -> failwith "bug in make distinct"
	in gn 0 intro2
     | _ -> failwith "bug2 in make distinct"
  in
  let rule, rule' = fn intro1 in
  type_form rule; type_form rule';
  do_claim (name1^"_not_"^name2^"."^tname) None rule export;
  let claim = sym_get (name1^"_not_"^name2^"."^tname) in
  add_elim equal_obj (name1^"_not_"^name2) 1 claim (fINV land fNEC) 0.0 export;
  do_goal rule' (Some (name2^"_not_"^name1^"."^tname)) None export;
  let tri = {nlim = !trdepth; eqlvl = !eqdepth;
             from_trivial = false; first_order = true;
	     auto_elim = true; eqflvl = 0} in
  let _ = do_rule 1 "use" [1] (rule_use true tri "" (aobj claim)) in
  let _ = do_rule 1 "intros" [1] (rule_intro (ref false) tri Default) in
  let _ = do_rule 1 "intros" [1] (try_rule (rule_intro (ref false) tri Default)) in
  let gl = match !cur_proof with
      A_proof {remain = [gl,_]; _} -> gl
    | _ -> failwith "bug in Data (proving inj')"
  in
  let (hypnamen, _) = last gl.hyp in
  let eformn = aobj (sym_get hypnamen) in
  let _ = do_rule 1 "elim+auto" [1]
	    (compose_rule
	       (rule_elim false tri false false false [] 1 eformn)
	       (rule_auto true [] [] tri)) in
  do_save None export;
  let claim' = sym_get (name2^"_not_"^name1^"."^tname) in
  add_elim equal_obj (name2^"_not_"^name1) 1 claim' (fINV land fNEC) 0.0 export;
  ()

let data export name sy kX go le tname intros =

  let all_kind =
    List.map (fun (_, _, e) ->
      let k = mk_Var () in
      type_strong e (KArrow(kX,(KArrow(k,mk_Var ()))));
      k) intros
  in
  let sname = Bytes.of_string tname in
  let first_char = Bytes.get sname 0 in
  if 'A' > first_char || 'Z' < first_char then
    raise (Gen_error ("name of a data type must start with a capital letter"));
  Bytes.set sname 0 (Char.lowercase_ascii first_char);
  let sname = Bytes.to_string sname in
  let lt = ref (0, []) in
  let rec fn t = match norm2 t with
      KArrow(_,t) -> fn t
    | t -> let _ = equal_kind t kForm in ()
  in fn kX;
  let _ = generalize_kind lt kX in
  let _ = List.map (generalize_kind lt) all_kind in
  let arity = (fst !lt) - 1 in
  if arity < 0 then failwith "bug arity neg in data";
  let sort_obj =
    add_sym sname Unknown KCst Trivial false true Idtren (Some arity) in
  let const = ref [sort_obj] in
  try
    let rec kn t =
      let t', u' = filter_arrow t in
      if equal_kind u' kForm then t' else kn u'
    in
    let kZ = kn kX in
    let ptrZ = match norm2 kZ with
	KVar ptr -> ptr
      | _ -> failwith "bug type 1 neg in data"
    in
    let lk = select (fun ptr -> not (ptr == ptrZ)) (List.map fst (snd !lt)) in
    let ksort =
      KAtom(sort_obj, (List.map (fun ptr -> KVar ptr) lk)) in
    if not (equal_kind kZ ksort) then failwith "bug type 2 neg in data";

    let add_constructor ((cname,lo), (s, sy), e) =
      match e with
	EAbs(sX,(EAbs(_,_,ck) as t),kX) ->
	  let co = add_sym s ck Cst sy false true Idtren None in
	  const := co :: !const;
	  let ne = norm_expr (EAbs(sX,EApp(t, aobj co), kX)) in
	  ((cname, Constructor::Invertible::lo), ne), co
      | _ ->
	  assert false
    in
    let nintros, objs = List.split (List.map add_constructor intros) in
    let intro_theos = inductive export name sy go kX le tname nintros in

    let typed = List.mem Typed go in
    let non_disjoint = List.mem Non_disjoint go in
    let rec make_all_distinct lintro_theos lobjs =
      match lintro_theos, lobjs with
	[],[] -> ()
      | intro::suit, obj::suit' ->
          let inj = make_injective typed export tname intro in

	  if not non_disjoint then begin
	    List.iter (make_distinct typed export tname intro) suit
	  end;

	  if not non_disjoint && inj then begin
	    make_case typed export tname intro obj intro_theos objs
	  end;

	  make_all_distinct suit suit'

      | _ -> assert false
    in

    make_all_distinct intro_theos objs

  with e ->
    List.iter (rec_remove false !the_base) !const;
    raise e

let parse_maybe_tname = parser
    [< 'Kwd "["; 'Ident s ; 'Kwd "]" >] -> Some s
  | [< >] -> None

let rec parse_ioptions f = parser
    [< 'Kwd "-"; s = parse_ident; l = parse_ioptions f >] -> (f s)::l
  | [< >] -> []

let parse_global_options =
  let f = function
      "ce" -> Claim_elim
    | "cc" -> Claim_case
    | "nd" -> Non_disjoint
    | "ty" -> Typed
    | name -> raise (Stream.Error ("illegal option "^name^" for Inductive types"))
  in parse_ioptions f

let parse_local_options =
  let f = function
      "ci" -> Claim_intro
    | "ni" -> Non_injective
    | "i"  -> Invertible
    | "t"  -> Totality
    | "c"  -> Constructor
    | name -> raise (Stream.Error ("illegal option "^name^"  for Inductive types"))
  in parse_ioptions f

let rec parse_inductive_suit export o le tname l tstr = match tstr with parser
  [< 'Ident name; lo = parse_local_options; 'Kwd ":" ?? serror ":" tstr;
     e = parse_bound_expr le ?? serror "an expression" tstr >] ->
       parse_inductive_suit' export o le tname (((name, lo), e)::l) tstr

and parse_inductive_suit' export o le tname l tstr = match tstr with parser
  [< 'Kwd "|" >] ->
     parse_inductive_suit export o le tname l tstr
| [< >] ->
     l

let parse_inductive export tstr = match tstr with parser
  [< 'Ident "Inductive";
     tname = parse_maybe_tname;
     s,sy,le = parse_syntax_def false ?? serror "a syntax definition" tstr;
     go = parse_global_options;
     'Kwd "=" >] ->
    let save_compiling = !compiling in
    let save_inductive = !in_inductive in
    compiling := true;
    in_inductive := true;
    if sy <> Trivial && tname = None then
      failwith "one must also give a name when using special syntax";
    let k = mk_Var () in
    let o = add_sym s k Cst sy false true Idtren None in
    let tname =
      match tname with
        Some n -> n
      | None -> s
    in
    try
      let intros = parse_inductive_suit export o le tname [] tstr in
      (* preparation *)
	 let kX = mk_Var () in
	 let fn ((name,lo), e) =
	   try
	     let e = bind_atom "X" o e kX in
	     ((name,lo), e)
	   with Not_found ->
	     raise (Gen_error ("predicate not used in "^name))
	 in
	 let intros = List.map fn (List.rev intros) in
	 let _ = rec_remove false !the_base o in
	 let _ = inductive export s sy go kX le tname intros in
	 in_inductive := save_inductive;
  	 compiling := save_compiling
    with
      e ->
	(try do_abort () with _ -> ());
        (try rec_remove false !the_base o with Not_found -> ());
	compiling := save_compiling;
	in_inductive := save_inductive;
	raise e



let rec parse_data_suit export o le tname l tstr = match tstr with parser
    [<
      cname = parse_maybe_tname;
      s,sy,le' = parse_syntax_def false ?? serror "a syntax definition" tstr;
      lo  = parse_local_options; >] ->
      if sy <> Trivial && cname = None then
	failwith "you must also give a name when using special syntax";
      let k = mk_Var () in
      let co = add_sym s k Cst sy false true Idtren None in
      let cname =
	match cname with
          Some n -> n
        | None -> s
      in
      parse_data_suit2 export o lo le tname l cname (s,sy) le' co tstr

and parse_data_suit' export o le tname l tstr = match tstr with parser
    [< 'Kwd "|" >] ->
      parse_data_suit export o le tname l tstr
  | [< >] ->
      l

and parse_arg_list tstr = match tstr with parser
  [< e = parse_free_expr; l = parse_arg_list_aux >] ->
    e::l

and parse_arg_list_aux tstr = match tstr with parser
  [< 'Ident "and"; l = parse_arg_list >] -> l
| [< >] -> []

and parse_of tstr = match tstr with parser
  [< 'Ident "of"; l = parse_arg_list >] -> l
| [< >] -> []

and head_name  = function
  EApp(t,_) -> head_name t
| EAbs(_,t,_) -> head_name t
| EAtom(o,_) -> get_name o
| FVar s -> s
| _ -> assert false

and parse_data_suit2 export o lo le tname l cname sy le' co tstr =
  let fn le' e =
    let kX = mk_Var () in
    let rec kn l t = match l, t with
      [], t -> t
    | (_,_)::l, EAbs(s,t,k) -> (
	let t = kn l t in
	try unlift t
	with Exit ->
	  EApp(aobj forall_obj, EAbs(s,t,k)))
    | _ -> failwith "bug 1 in parse_data_suit2"
    in
    let rec kn' l t = match l, t with
      [], t -> kn le' t
    | (_,_)::l, EAbs(s,t,k)  -> EAbs(s,kn' l t,k)
    | _ -> failwith "bug 2 in parse_data_suit2"
    in
    let e = bind_atom cname co (kn' le e) kX in
    let _ = rec_remove false !the_base co in
    parse_data_suit' export o le tname (((cname, lo), sy, e)::l) tstr
  in match tstr with parser
    [<'Kwd ":"; e = parse_bound_expr (le@le') >] -> fn le' e
  | [< l = parse_of >] ->
      let le' = if le' <> [] && List.length le' = List.length l then le' else
	List.fold_right (fun e' le' ->
	  let name = head_name e' in
	  let name = String.lowercase_ascii (String.sub name 0 1) in
	  let name = free_name name (List.map fst (le@le')) in
	  let k = mk_Var () in
	  (name,k)::le')
	  l []
      in
      let e0 =
	let rec fn acc = function
	    [] -> acc
	  | (n,_)::l -> fn (EApp(acc,FVar n)) l
	in
	let e1 = fn (aobj co) le' in
	let e0 = fn (aobj o) (liat le) in
	EApp(e0,e1)
      in
      let e =
	List.fold_right2 (fun e' (name,k) e->
	    EApp(aobj forall_obj,EAbs(name,
              EApp(EApp(aobj arrow_obj, EApp(e', FVar name)), e)
	      ,k)))
	  l le' e0
      in
      let rec f e = function
	  [] -> e
	| (s,k)::l -> EAbs(s,f e l, k) in
      let e = bind_free false 0 [] (f e (le@le')) in
      fn le' e

let parse_data export tstr = match tstr with parser
  [< 'Ident ("Data" | "type");
     s,sy,le = parse_syntax_def false ?? serror "a syntax definition" tstr;
     go = parse_global_options;
     'Kwd "=" >] ->
    let le = le@["x",mk_Var ()] in
    let save_compiling = !compiling in
    compiling := true;
    in_inductive := true;
    if sy <> Trivial then
      failwith "no special syntax allowed for data types";
    let k = mk_Var () in
    let o = add_sym s k Cst sy false true Idtren None in
    let tname = s in
       try
	 let intros = parse_data_suit export o le tname [] tstr in
	 (* preparation *)
	 let kX = mk_Var () in
	 let fn ((name,lo), co, e) =
	   try
	     let e = bind_atom "X" o e kX in
	     let _ = type_check e in
	     ((name,lo), co, e)
	   with Not_found ->
	     raise (Gen_error ("predicate not used in "^name))
	 in
	 let intros = List.map fn (List.rev intros) in
	 let _ = rec_remove false !the_base o in
	 data export s sy kX go le tname intros;
	 in_inductive := false;
  	 compiling := save_compiling
       with
	 e ->
	   (try do_abort () with _ -> ());
           (try rec_remove false !the_base o with Not_found -> ());
	   compiling := save_compiling;
	   in_inductive := false;
    	   raise e
