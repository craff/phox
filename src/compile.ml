(*######################################################*)
(*			compile.ml			*)
(*######################################################*)

open Format
open Basic
open Type
open Lambda_util
open Af2_basic
open Typing
open Print
open Type_check
open Lambda_exp
open Parse_lambda
open Bindlib
open Option

let rec compile_proof o a =

  let rec f env = function
      EVar p ->
	let r = List.nth env p in
	begin
	  match r with
	    None -> raise (Failure "bug -1 in compile_proof.");
	  | Some x -> x
	end

(* Constructor with 0 argument *)
    | EAtom (o1,_) ->
      if o1 == claim_obj then
	let name = get_name o in
        begin
	  try
            unit (get_def name)
          with Not_found ->
	    print_endline ("warning: compiling claim: "^name);
	    add_def name (bSVar name);
	    unit (get_def name);
	end
      else raise (Failure "bug 0 in compile_proof")

(* Constructor with 1 argument *)
  | EApp(EAtom (o1,_),a1) ->

(* forall intro *)
      if (o1 == forall_intro_obj) then (
        match a1 with
          EAbs(_,p,_) ->
              f (None::env) p
        | _ -> raise (Failure "bug 1 in compile_proof"))

(* use theorem *)
      else if o1 == use_theorem_obj then (
      let oo = match a1 with
        EAtom(o,_) -> o
      | _ -> raise (Failure "bug 2 bis in compile_proof") in
      match get_inst a1 with
        EApp(EApp(EAtom(o',_),_),_) ->
          if o' != theorem_obj then raise (Failure "bug 2 in compile_proof");
          (try unit (get_def (get_name oo)) with Not_found ->
              unit (compile oo))
      | _ -> raise (Failure "bug 3 in compile_proof"))

      else raise (Failure "bug 4 in compile_proof")

(* Constructor with 2 arguments *)
  | EApp(EApp(EAtom (o1,_),a1),a2) ->

(* arrow intro *)
      if o1 == arrow_intro_obj then (
        match a2 with
          EAbs(_,p,_) ->
            bLam (fun x -> (f ((Some x)::env) p))
        | _ -> raise (Failure "bug 5 in compile_proof"))

(* arrow elim *)
      else if o1 == arrow_elim_obj then
	bApp (f env a1) (f env a2)

(* cut rule *)
      else if o1 == cut_rule_obj then (
       match a2 with
         EAbs(_,p,_) ->
           bApp (bLam (fun x -> f ((Some x)::env) p)) (f env a1)
        | _ -> raise (Failure "bug 5* in compile_proof"))

(* forall elim *)
      else if (o1 == forall_elim_obj) then
        f env a1

(* devlopment of a definition *)
      else if o1 == devl_def_obj then f env a2

      else raise (Failure "bug 6 in compile_proof")

(* Constructor with 3 arguments *)
  | EApp(EApp(EApp(EAtom (o1,_),_),a2),a3) ->

(* left-right equation *)
      if o1 == lr_eqn_obj then
	let (path,a2) = match a2 with
            Path(path,a2) ->
              path,a2 | _ -> raise (Failure "bug 17 in compile_proof") in
	let env' = it_path None env path in
	bApp (f env' a2) (f env a3)

(* right-left equation *)
      else if o1 == rl_eqn_obj then
	let (path,a2) = match a2 with
            Path(path,a2) ->
              path,a2 | _ -> raise  (Failure "bug 27 in compile_proof") in
	let env' = it_path None env path in
	bApp (bApp (f env' a2) (bLam (fun x -> x))) (f env a3)

      else if o1 == fact_def_obj then f env a3

      else if o1 == local_def_obj then f env (norm_expr (EApp(a3,a2)))

      else raise (Failure "bug 7 in compile_proof")

  | _ -> raise (Failure "bug 1 in compile_proof")

  in
  start_term (f [] a)

and compile o =
  if not keep_proof then
    raise (Gen_error "\"-f\" is required to use \"compile\".");
  open_hbox ();
  let e = match (get_value o) with
    Def e -> e
  | _ -> raise (Gen_error "This is not a theorem") in
  let p = match (get_inst e) with
    EApp(EApp(EAtom(o,_),_),e) ->
      if o == theorem_obj then e
      else raise (Gen_error "This is not a theorem")
  | _ -> raise (Gen_error "This is not a theorem") in
  let s = get_name o in
  try
    get_def s
  with Not_found ->
    print_string "Compiling ";
    print_string s;
    print_string " .... ";
    print_newline ();
    let t = compile_proof o p in
    add_def s t;
    get_def s

let rec translate lam app o =
  let rec f env = function
      EAbs(_,t,_) ->
	bLam (fun x -> (f (x::env) t))
    | EApp(EAtom(o,_), EAbs(_,t,_)) when o == lam ->
	bLam (fun x -> (f (x::env) t))
    | EApp(EAtom(o,_), t) when o == lam ->
	bLam (fun x -> f (x::env) (EApp (lift t, EVar 0)))
    | EApp(EApp(EAtom(_,_), t1), t2) ->
	bApp (f env t1) (f env t2)
    | EApp(t1, t2) ->
	bApp (f env t1) (f env t2)
    | EVar n ->
	List.nth env n
    | EAtom(o,_) ->
	unit(translate lam app o)
    | t ->
	print_expr t; print_newline ();
	failwith "Error: not a lambda-term"
  in
  let s = get_name o in
  try
    get_def s
  with Not_found ->
    match get_value o with
      Def t ->
	add_def s (start_term (f [] t));
	get_def s
    | _ ->
	print_string ("Warning: translating constant: "^s);
	print_newline ();
	add_def s (bSVar s);
	get_def s
