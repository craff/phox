open Basic
open Type.Base
open Type
open Lambda_util
open Af2_basic
open Interact
open Local
open Print
open Typing
open Pattern

module AL = struct

  type formula = expr

  exception Unif_fails

  type substitution = expr Map.t

  let apply_subst r f = norm_lsexpr r f []

  let size = term_size

  type constraints = unit

  let print_constraints _ = ()

  let rename_constraints _ c = c

  let get_renaming_constraints x _ = x

  let empty_constraints _ = ()

  exception Metavar

  let negative_formula f =
    let rec fn b s = function
	EApp(t,u) -> fn b (u::s) t
      | EAbs _ -> assert false
      | EAtom(o,k) ->
	  if o == !not_obj then
	    match s with
	      [u] -> fn (not b) [] u
	    | _ -> assert false
	  else if o == !false_obj then b
	  else if o == !true_obj then not b
	  else if !fis_close o then not b
	  else begin
	    match get_value o with
	      Def _ | Prg _ -> fn b [] (norm_sexpr (get_inst (kind_inst o k)) s)
	    | _ -> not b
	  end
      | UVar (p,_) -> (try fn b s (getuvar p) with Not_found -> raise Metavar)
      | UCst (_,_) -> not b
      | _ -> not b

    in fn true [] f

  let negate_formula f =
    match f with
      EAtom(o,_) when o == !true_obj -> aobj(!false_obj)
    | EAtom(o,_) when o == !false_obj -> aobj(!true_obj)
    | _ -> EApp(aobj !not_obj, f)

  type unif_kind = Contraction of constraints | Unification of (constraints * constraints) | Subsume

  let leqn = ref ([] : (pos_eq * eqns) list)

  let unif uk e1 e2 =
    let (s1,_,_,_ as save) = get_ulocal () in
    try
      let l = umatch !leqn !cur_local e1 e2 in
      let (s2,_,_,_) = get_ulocal () in
      let s = Map.fold (fun n e a ->
	if Map.mem n s1 then a else a + size e) s1 0 in
      set_ulocal save;
      s, s2, uk, (), apply_subst s2 e1, List.map negate_formula l
    with
      Fail_matching ->
	set_ulocal save;
	raise Unif_fails

  let is_true _ = false

  let elim_all_neg f =
    let rec fn s = function
	EApp(t,u) -> fn (u::s) t
      | EAbs _ -> assert false
      | EAtom(o,k) as e ->
	  if o == !not_obj then
	    match s with
	      [u] -> fn [] u
	    | _ -> assert false
	  else if o == !false_obj then norm_sexpr (aobj !true_obj) s
	  else if o == !true_obj then norm_sexpr (aobj !true_obj) s
	  else if !fis_close o then norm_sexpr e s
	  else begin
	    match get_value o with
	      Def _ | Prg _ -> fn [] (norm_sexpr (get_inst (kind_inst o k)) s)
	    | _ -> norm_sexpr e s
	  end
      | UVar (p,_) -> (try fn s (getuvar p) with Not_found -> raise Metavar)
      | e -> norm_sexpr e s

    in fn [] f

  type renaming = expr Map.t

  let empty_renaming () =
    let (u,_,_,_) = get_ulocal () in
    u

  let add_renaming n k r =
    if Map.mem n r then r else
    begin
      let p = new_uvar () in
      let e = UVar(p,k) in
      Map.add n e r
    end

  let not_norm_info = ref (FVar "")

  let not_norm_atom o t0 =
    match get_value o with
      Prg e -> not_norm_info := e; true
    | Fun _ -> not_norm_info := t0; true
    | Def e -> not_norm_info := e; is_capsule o
  | _ -> false

  let get_renaming_formula r f =
    let rec g acc stack = function
	EApp (t,t') ->
	  g acc (t'::stack) t
      | EAbs (_,t,_) as t0 ->
	  if stack <> [] then g acc [] (norm_sexpr t0 stack) else g acc [] t
      | EAtom (o,_) as t0 when not_norm_atom o t0 ->
	  g acc [] (norm_sexpr !not_norm_info stack)
      | UCst _ | Syntax _ | EVar _ | EAtom _ ->
	  List.fold_left (fun x t -> g x [] t) acc stack
      | UVar (p,k)  -> (try g acc stack (getuvar p) with Not_found ->
	  List.fold_left (fun x t -> g x [] t) (add_renaming p k acc) stack)
      | _ ->
	  List.fold_left (fun x t -> g x [] t) acc stack
    in g r [] f

  let rename_formula r f =
    norm_lsexpr r f []

  let sequent_to_rules old_hyp ll gl =
    let gn x =
      if equal_expr x (aobj !true_obj) then [] else
      List.map (fun l -> x::l) ll
    in
    List.fold_left (fun l (name,(e,_,_,_,_)) ->
      if name = "H#" || List.mem_assoc name old_hyp then l else (gn e) @ l)
      (gn (negate_formula gl.concl)) gl.hyp

  let sequents_to_rules old_hyp ll gls =
    List.fold_left (sequent_to_rules old_hyp) ll gls

  let selflatrevmap f g l =
    let rec fn acc = function
	x::l ->
	  begin try
	    fn (f x @ acc) l
	  with
	    _ ->
	      g(); fn acc l
	  end
      | [] ->acc
    in
    fn [] l

  let get_rules c f pos =
    let tri =
      {nlim = 4; eqlvl = !Flags.eqdepth; from_trivial = false; first_order = false;
       auto_elim = false; eqflvl = !Flags.eqflvl}
    in
    let gl0 =
      match !cur_proof with
	A_proof ({ remain = (gl0, _)::_ ; _}) -> gl0
      | _ -> raise Not_found
    in
    let size_f = term_size_rec f in
    if not pos then begin
      let gl = { gl0 with concl = f } in
      let st = Fin 0 in
      let intros =
        let b, l = get_intros (tri.nlim < 0)
	    gl.eqns gl.local true gl.concl in
        if b then fst (List.split l)@[""] else fst (List.split l)
      in
      let save = get_ulocal () in
      selflatrevmap
	(fun x ->
          let nr, cond =
	    let p = ref [] in
	    from_resol := Some p;
	    try
	      let nr, _ =
		rule_intro (ref false) tri (Names [x,None]) gl st  in
	      from_resol := None;
	      nr, !p
	    with
	      e ->
		from_resol := None;
		raise e
	  in
	  let (subst,_,_,_) = get_ulocal () in
	  set_ulocal save;
	  let clauses = sequents_to_rules gl0.hyp [cond] (List.map fst nr) in
	  let clauses = List.map (List.map (apply_subst subst)) clauses in
	  let result = List.map
	      (fun cl ->
		let poids = List.fold_left (fun p g ->
		  let size_g = term_size_rec (elim_all_neg g) in
		  if size_g >= size_f then p+1 else p) 1 cl
		in
		(x,poids,subst,c,cl)) clauses
	  in
	  result)
	(fun () -> set_ulocal save)
	intros
    end else begin
      let hypname = "H#" in
      let h = (hypname, (f,0,Hypo,Dont_know [], (false, []))) in
      let gl = { gl0 with hyp = h::gl0.hyp; concl = aobj !false_obj } in
      let lefts =
	let _, _, _, _, lefts =
	  get_lefts None tri.from_trivial Default hypname gl in
	List.map fst (fst (List.split lefts))
      in
      let st = Fin 0 in
      let save = get_ulocal () in
      selflatrevmap
	(fun x ->
	  set_ulocal save;
          let nr, cond =
	    let p = ref [] in
	    from_resol := Some p;
	    try
	      let nr, _ =
		 rule_left tri hypname  (Names [x,None]) None gl st in
	      from_resol := None;
	      nr, !p
	    with
	      e ->
		from_resol := None;
		raise e
	  in
	  List.iter (fun (gl,_) -> print_goal false false 0 0 gl) nr;
	  let (subst,_,_,_) = get_ulocal () in
	  set_ulocal save;
	  let clauses = sequents_to_rules gl0.hyp [cond] (List.map fst nr) in
	  let clauses = List.map (List.map (apply_subst subst)) clauses in
	  let result = List.map
	      (fun cl ->
		let poids = List.fold_left (fun p g ->
		  let size_g = term_size_rec (elim_all_neg g) in
		  if size_g >= size_f then p+1 else p) 1 cl
		in
		(x,poids,subst,c,cl)) clauses
	  in
	  result)
	(fun () -> set_ulocal save)
	lefts
    end


  let print_formula = print_expr

  let equal_formula = equal_expr

  let indice_regle _ = 0

  type head_symbol_type = af2_obj

  module FormHashType = struct
    type t = head_symbol_type * bool
    let equal (h,b) (h',b') = h == h' && b = b'
    let hash = Hashtbl.hash
  end

  let head_symbol f =
    let _,h,_ = head_kind f in
    h

  type varset = Set.t

  let empty_varset = Set.empty

  let union_varset = Set.union

  let is_empty_inter_varset s1 s2 =
    Set.is_empty (Set.inter s1 s2)

  let vars_of_formula = list_uvar

  let vars_to_constants s =
    Set.fold
      (fun v m ->
	let k = mk_Var () in
 	let n = new_const () in
	Map.add v (UCst (n,k)) m)
      s
      Map.empty
end

let rule_resolve methode gl st =
  let module Prv = Prover.Prover(AL) in
  try
    let hyps = List.map (fun (_,(e,_,_,_,_)) ->
      e, None, (), 2) gl.hyp
    in
    Ptypes.timemax := 0;
    Ptypes.pause := false;
    AL.leqn := gl.eqns;
    Prv.prove ~methode hyps gl.concl;
    AL.leqn := [];
    let r = rule_claim gl st in
    r
  with
    Ptypes.Prove_fails ->
      AL.leqn := [];
      raise (Ill_rule "Resol failed.")
  | e ->
      AL.leqn := [];
      raise e
