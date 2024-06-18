(* $State: Exp $ $Date: 2006/02/24 17:01:54 $ $Revision: 1.6 $ *)
(*######################################################*)
(*			type_check.ml			*)
(*######################################################*)


open Print
open Flags
open Format
open Type.Base
open Type
open Lambda_util
open Af2_basic
open Typunif
open Typing
open Local



exception Bad_proof of int

let rec it_path dum env = function
  [] -> env
| (PAbs _)::l -> it_path dum (dum::env) l
| _::l -> it_path dum env l

let next_gen, reset_gen =
  let c = ref 0 in
  (fun () -> incr c; !c),
  (fun () -> c:=0)

let rec fn env = function
(* axiome *)
    EVar n -> List.nth env n

(* Constructor with 1 argument *)
  | EApp(EAtom (o1,k1),a1) ->

(* forall intro *)
      if o1 == forall_intro_obj then (
        match a1 with
          EAbs(s,_,k) ->
            let n = new_const () in
            EApp(EAtom(forall_obj, k1),
                 bind_cst s n (fn env
                  (norm_expr (EApp(a1, UCst (n,k))))) k)
        | _ -> raise (Bad_proof 1))

(* use theorem *)
      else if o1 == use_theorem_obj then (
      match get_inst a1 with
        EApp(EApp(EAtom(o,_),f),_) ->
          if o != theorem_obj then raise (Bad_proof 3);
          f
        | _ -> raise (Bad_proof 4))

(* claim *)
      else if o1 == lclaim_obj then (
	print_string "Warning: proof using claim";
	print_newline ();
	a1
       )

      else raise (Bad_proof 5)

(* Constructor with 2 arguments *)
  | EApp(EApp(EAtom (o1,k1),a1),a2) ->

(* arrow intro *)
      if o1 == arrow_intro_obj then (
        match a2 with
          EAbs(_,p,_) -> EApp(EApp(aobj (arrow_obj), a1), fn (a1::env) p)
        | _ -> raise (Bad_proof 6))

(* arrow elim *)
      else if o1 == arrow_elim_obj then (
      let f1 = fn env a1 and f2 = fn env a2 in
      match f1 with
        EApp(EApp(EAtom (o,_),arg),res) ->
          if o != arrow_obj then (raise (Bad_proof 7));
          if not (equal_expr arg f2) then begin
	    print_expr arg;
	    print_newline ();
	    print_expr f2;
	    print_newline ();
	    print_expr res;
	    print_newline ();
            raise (Bad_proof 8)
          end;
          res
      | _ -> raise (Bad_proof 9))

(* cut_rule *)
      else if o1 == cut_rule_obj then (
      match a2 with
        EAbs(_,p,_) ->
          let f1 = fn env a1 in
          fn (f1::env) p
      | _ -> raise (Bad_proof 9))

(* forall elim *)
      else if o1 == forall_elim_obj then (
      let f1 = fn env a1 in
      match k1, f1 with
        [k1], EApp(EAtom (o,[k]),(EAbs _ as f)) ->
          if o != forall_obj then (raise (Bad_proof 10));
          unif k1 k;
          norm_expr (EApp(f,a2))
      | _ -> raise (Bad_proof 12))

(* devlopment of a definition *)
      else if o1 == devl_def_obj then (
      let f1 = fn env a2 in
      let (path,a1,o,k) = match a1 with
        Path(path,(EAtom (o,k) as a1)) ->
          path,a1,o,k | _ -> raise (Bad_proof 17) in
      let v = try kind_inst o k
      with Not_found | Clash -> raise (Bad_proof 18) in
      if not (path_test path f1 a1 f1) then raise (Bad_proof 20);
      path_subst path f1 v)


      else raise (Bad_proof 16)

(* Constructor with 3 arguments *)
  | EApp(EApp(EApp(EAtom (o1,_),a1),a2),a3) ->

(* left-right equation *)
      if o1 == lr_eqn_obj then (
      let f1 = fn env a3 in
      let (_,context) = match a1 with
        Path(path,context) ->
          path,context | _ -> raise (Bad_proof 23) in
      let (path,a2) = match a2 with
        Path(path,a2) ->
          path,a2 | _ -> raise (Bad_proof 23) in
      let env' = it_path (EVar (-1)) env path in
      let eq = fn env' a2 in
      let (o,e1,e2) = match get_inst eq with
        EApp(EApp(EAtom(o,_),e1),e2) -> (o,e1,e2)
      | _ -> raise (Bad_proof 21) in
      if o != equal_obj then raise (Bad_proof 22);
      if not (path_test path f1 (norm_expr (EApp(context,e1))) f1) then
	raise (Bad_proof 24);
      path_subst path f1 (norm_expr (EApp(context,e2))))

(* right-left equation *)
      else if o1 == rl_eqn_obj then (
      let f1 = fn env a3 in
      let (_,context) = match a1 with
        Path(path,context) ->
          path,context | _ -> raise (Bad_proof 27) in
      let (path,a2) = match a2 with
        Path(path,a2) ->
          path,a2 | _ -> raise (Bad_proof 23) in
      let env' = it_path (EVar (-1)) env path in
      let eq = fn env' a2 in
      let (o,e1,e2) = match get_inst eq with
        EApp(EApp(EAtom(o,_),e1),e2) -> (o,e1,e2)
      | _ -> raise (Bad_proof 25) in
      if o != equal_obj then raise (Bad_proof 26);
      if not (path_test path f1 (norm_expr (EApp(context,e2))) f1) then
	raise (Bad_proof 28);
      path_subst path f1 (norm_expr (EApp(context,e1))))

(* factorization of a definition *)
      else if o1 == fact_def_obj then (
      let f1 = fn env a3 in
      let (o,k) = match a2 with
        EAtom (o,k) -> (o,k) | _ -> raise (Bad_proof 30) in
      let (path,a1) = match a1 with
        Path(path,a1)-> path,a1
      | _ -> raise (Bad_proof 41) in
      let v = try kind_inst o k
      with Not_found | Clash -> raise (Bad_proof 31) in
      if not (path_test path f1 (norm_expr (EApp(a1,v))) f1)
        then raise (Bad_proof 33);
      path_subst path f1 (norm_expr (EApp(a1,a2))))

(* local definition *)
      else if o1 == local_def_obj then
      let sy = match a1 with Syntax sy -> sy | _ -> raise (Bad_proof 34) in
      let o = match a3 with EAbs (s,_,kind) ->
        capsule_object s
           {fkind = kind; fvalue = Def a2; syntax = sy;
            poly = 0; exported = false; origin = Idtren}
           (next_gen ())
        | _ -> raise (Bad_proof 35) in
      let p = norm_expr (EApp(a3,EAtom(o,[]))) in
      fn env p

      else raise (Bad_proof 29)

  | _ -> raise (Bad_proof 100)

let new_var name k =
  let o =
    {fkind = k; fvalue = Cst; syntax = Trivial;
     poly = 0; exported = false; origin = Local_hyp} in
  capsule_object name o 0

let rec fnd pos namel env = function
(* axiome *)
    EVar n ->
      let hname = List.nth namel n in
      let hyp = List.nth env n in
      print_int pos; print_newline ();
      print_string "- axiom: ";
      print_string hname;
      print_string " = ";
      print_expr hyp;
      print_newline ();
      hyp

(* Constructor with 1 argument *)
  | EApp(EAtom (o1,k1),a1) ->

(* forall intro *)
      if o1 == forall_intro_obj then (
        match a1 with
          EAbs(s,_,k) ->
            let name = free_name s namel in
            print_int pos; print_newline ();
            print_string "> forall introduction, introducing ";
            print_string name;
            print_string " : ";
            print_kind k;
            print_newline ();
            let o = new_var name k in
            let n = aobj o in
            let r = EApp(EAtom(forall_obj, k1),
                 bind_atom s o (fnd pos (name::namel) env
                  (norm_expr (EApp(a1, n)))) k) in
            print_int pos; print_newline ();
            print_string "< forall introduction: ";
            print_expr r;
            print_newline ();
            r

        | _ -> raise (Bad_proof 1))

(* use theorem *)
      else if o1 == use_theorem_obj then (
      match get_inst a1 with
        EApp(EApp(EAtom(o,_),f),_) ->
          if o != theorem_obj then raise (Bad_proof 3);
          print_int pos; print_newline ();
          print_string "- theorem: ";
          print_expr f;
          print_newline ();
          f
        | _ -> raise (Bad_proof 4))

      else raise (Bad_proof 5)

(* Constructor with 2 arguments *)
  | EApp(EApp(EAtom (o1,k1),a1),a2) ->

(* arrow intro *)
      if o1 == arrow_intro_obj then (
        match a2 with
          EAbs(s,p,_) ->
            let name = free_name s namel in
            print_int pos; print_newline ();
            print_string "> arrow introduction: hypothesis ";
            print_string name;
            print_string " = ";
            print_expr a1;
            print_newline ();
            let r = EApp(EApp(aobj (arrow_obj), a1),
              fnd (pos+1) (name::namel)(a1::env) p) in
            print_int pos; print_newline ();
            print_string "< arrow introduction: ";
            print_expr r;
            print_newline ();
          r
        | _ -> raise (Bad_proof 6))

(* arrow elim *)
      else if o1 == arrow_elim_obj then (
      let f1 = fnd (pos+1) namel env a1 and f2 = fnd (pos+1) namel env a2 in
      match f1 with
        EApp(EApp(EAtom (o,_),arg),res) ->
          if o != arrow_obj then (raise (Bad_proof 7));
          print_int pos; print_newline ();
          print_string "< arrow_elim: ";
          print_newline ();
          print_string "recall: ";
          print_expr f1;
          print_newline ();
          print_expr res;
          print_newline ();
          if not (equal_expr arg f2) then (raise (Bad_proof 8));
          res
      | _ -> raise (Bad_proof 9))

(* cut_rule *)
      else if o1 == cut_rule_obj then (
      match a2 with
        EAbs(s,p,_) ->
          let f1 = fnd (pos+1) namel env a1 in
          print_int pos; print_newline ();
          print_string "> cut: ";
          print_newline ();
          let name = free_name s namel in
          print_string "we have proved: ";
          print_string name;
          print_string " = ";
          print_expr f1;
          print_newline ();
          let r = fnd (pos+1) (name::namel) (f1::env) p in
          print_int pos; print_newline ();
          print_string "< cut: ";
          print_expr r;
          print_newline ();
	  r
      | _ -> raise (Bad_proof 9))

(* forall elim *)
      else if o1 == forall_elim_obj then (
      let f1 = fnd (pos+1) namel env a1 in
      match k1, f1 with
        [k1], EApp(EAtom (o,[k]),(EAbs _ as f)) ->
          if o != forall_obj then (raise (Bad_proof 10));
          (try unif k k1
          with Clash -> raise (Bad_proof 11));
          let r = norm_expr (EApp(f,a2)) in
          print_int pos; print_newline ();
          print_string "< forall elimination: ";
          print_expr r;
          print_newline ();
	  r
      | _ -> raise (Bad_proof 12))

(* devlopment of a definition *)
      else if o1 == devl_def_obj then (
      let f1 = fnd (pos+1) namel  env a2 in
      let (path,a1,o,k) = match a1 with
        Path(path,(EAtom (o,k) as a1)) ->
          path,a1,o,k | _ -> raise (Bad_proof 17) in
      let v = try kind_inst o k
      with Not_found | Clash -> raise (Bad_proof 18) in
      if not (path_test path f1 a1 f1) then raise (Bad_proof 20);
      let r = path_subst path f1 v in
      print_int pos; print_newline ();
      print_string "< developpement of definition: ";
      print_string (get_name o);
      print_newline ();
      print_expr r;
      print_newline ();
      r)

(* left-right equation *)
      else if o1 == lr_eqn_obj then (
      let f1 = fnd (pos+1) namel env a2 in
      print_int pos; print_newline ();
      print_string "> left-right equation: ";
      print_expr f1;
      print_newline ();
      let (path,a1) = match a1 with
        Path(path,a1) ->
          path,a1 | _ -> raise (Bad_proof 23) in
      let env' = it_path (EVar (-1)) env path in
      let eq = fnd (pos+1) namel env' a1 in
      let (o,e1,e2) = match get_inst eq with
        EApp(EApp(EAtom(o,_),e1),e2) -> (o,e1,e2)
      | _ -> raise (Bad_proof 21) in
      if o != equal_obj then raise (Bad_proof 22);
      if not (path_test path f1 e1 f1) then raise (Bad_proof 24);
      let r = path_subst path f1 e2 in
      print_int pos; print_newline ();
      print_string "< left-right equation: recall:";
      print_expr f1;
      print_newline ();
      print_expr r;
      print_newline ();
      r)

(* right-left equation *)
      else if o1 == rl_eqn_obj then (
      let f1 = fnd (pos+1) namel env a2 in
      print_int pos; print_newline ();
      print_string "> right-left equation: ";
      print_expr f1;
      print_newline ();
      let (path,a1) = match a1 with
        Path(path,a1) ->
          path,a1 | _ -> raise (Bad_proof 27) in
      let env' = it_path (EVar (-1)) env path in
      let eq = fnd (pos+1) namel env' a1 in
      let (o,e1,e2) = match get_inst eq with
        EApp(EApp(EAtom(o,_),e1),e2) -> (o,e1,e2)
      | _ -> raise (Bad_proof 25) in
      if o != equal_obj then raise (Bad_proof 26);
      if not (path_test path f1 e2 f1) then raise (Bad_proof 28);
      let r = path_subst path f1 e1 in
      print_int pos; print_newline ();
      print_string "< right-left equation: recall:";
      print_expr f1;
      print_newline ();
      print_expr r;
      print_newline ();
      r)

      else raise (Bad_proof 16)

(* Constructor with 3 arguments *)
  | EApp(EApp(EApp(EAtom (o1,_),a1),a2),a3) ->

(* factorization of a definition *)
      if o1 == fact_def_obj then (
      let f1 = fnd (pos+1) namel env a3 in
      let (o,k) = match a2 with
        EAtom (o,k) -> (o,k) | _ -> raise (Bad_proof 30) in
      let (path,a1) = match a1 with
        Path(path,a1)-> path,a1
      | _ -> raise (Bad_proof 41) in
      let v = try kind_inst o k
      with Not_found | Clash -> raise (Bad_proof 31) in
      if not (path_test path f1 (norm_expr (EApp(a1,v))) f1)
        then raise (Bad_proof 33);
      let r = path_subst path f1 (norm_expr (EApp(a1,a2))) in
      print_int pos; print_newline ();
      print_string "< factorisation of definition: ";
      print_string (get_name o);
      print_newline ();
      print_string "with arguments: ";
      print_expr a1;
      print_newline ();
      print_expr r;
      print_newline ();
      r)

(* local definition *)
      else if o1 == local_def_obj then
      let sy = match a1 with Syntax sy -> sy | _ -> raise (Bad_proof 34) in
      let o,_ = match a3 with EAbs (s,_,kind) ->
        capsule_object s
           {fkind = kind; fvalue = Def a2; syntax = sy;
            poly = 0; exported = false; origin = Idtren}
           (next_gen ()), kind
        | _ -> raise (Bad_proof 35) in
      let p = norm_expr (EApp(a3,EAtom(o,[]))) in
      print_string "> local definition: ";
      print_expr (EAtom(o,[]));
      print_string "=";
      print_expr a2;
      fnd (pos+1) namel env p

      else raise (Bad_proof 29)

  | _ -> raise (Bad_proof 100)




let proof_check p =
  reset_gen ();
  (if !debug_proof_check then fnd 0 [] else fn) [] p
