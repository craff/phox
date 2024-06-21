(* $State: Exp $ $Date: 2006/02/24 17:01:52 $ $Revision: 1.30 $ *)
(*######################################################*)
(*			af2_basic.ml			*)
(*######################################################*)

(*
  Contient la definition des constantes de base utilisees par AF2:
    implication, quantification, regle etc ...
*)

(* ce fichier n'a pas d'interface ! *)

open Format
open Basic
open Data_base.Object
open Type.Base
open Type
open Parse_base
open Lambda_util
open Typunif
open Typing
open Safe_add
open Print
open Local
open Option
open Data

(*
let rec lArrow = function
  [x] -> x
| t::l -> KArrow(t, lArrow l)
| _ -> failwith "bug in lArrow"
 *)

let init_data_af2 b =
  the_base := b;

  let oForm = add_sym "prop"
		Unknown KCst Trivial true true Kernel (Some 0) in
  let oProof = add_sym "proof"
		 Unknown KCst Trivial true true Kernel (Some 0) in
  let oTheorem = add_sym "theorem"
		   Unknown KCst Trivial true true Kernel (Some 0) in
  let oNum = add_sym "num"
	       Unknown KCst Trivial true true Kernel (Some 0) in
  let oString = add_sym "string"
			   Unknown KCst Trivial true true Kernel (Some 0) in
  let oSyntax = add_sym "syntax"
		  Unknown KCst Trivial true true Kernel (Some 0) in
  let oUnit = add_sym "unit"
		Unknown KCst Trivial true true Kernel (Some 0) in
  let _iOption = add_sym "option"
		  Unknown KCst Trivial true true Kernel (Some 1) in
  let iList = add_sym "list"
		Unknown KCst Trivial true true Kernel (Some 1) in
  let _iPair = add_sym "product"
		Unknown KCst Trivial true true Kernel (Some 2) in
  let _iSum = add_sym "sum"
	       Unknown KCst Trivial true true Kernel (Some 2) in


  let kForm = KAtom(oForm, []) in
  let kProof = KAtom(oProof, []) in
  let kTheorem = KAtom (oTheorem, []) in
  let kNum = KAtom(oNum, []) in
  let kString = KAtom(oString, []) in
  let kSyntax = KAtom(oSyntax, []) in
  let kUnit = KAtom(oUnit, []) in
  let kTheorem_list = KAtom (iList, [kTheorem]) in

  let _ = add_sym "→"
        (KArrow(kForm,KArrow(kForm,kForm)))
        Cst
        (snd (syntax_of_string false "rInfix[9] x \"→\" y ;"))
        true true Kernel None in
  let _ = add_sym "∀"
        (KArrow(KArrow(mk_Var (),kForm),kForm))
        Cst
        (snd (syntax_of_string false
          "Prefix[6] \"∀\" \\A,(λR,x(R x)):$→ \\ A ;"))
        true true Kernel None in
  let _ = add_sym "="
        (let v = mk_Var () in KArrow(v,KArrow(v,kForm)))
        Cst
        (snd (syntax_of_string false "Infix[5] x \"=\" y ;"))
        true true Kernel None in
  let _ = add_sym "theorems"
        (KArrow(kForm, KArrow(kProof, kTheorem)))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "arrow_intro"
        (KArrow(kForm,KArrow(KArrow(kProof,kProof),kProof)))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "arrow_elim"
        (KArrow(kProof,KArrow(kProof,kProof)))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "cut_rule"
        (KArrow(kProof,KArrow(KArrow(kProof,kProof),kProof)))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "forall_intro"
        (KArrow(KArrow(mk_Var (),kProof),kProof))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "forall_elim"
        (KArrow(kProof,KArrow(mk_Var (),kProof)))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "devl_def"
        (let v = mk_Var () in
        KArrow(v,KArrow(kProof,kProof)))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "fact_def"
        (let v = mk_Var () and w = mk_Var () in
        KArrow(KArrow(v,w),KArrow(v,KArrow(kProof,kProof))))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "local_def"
        (let v = mk_Var () in
        KArrow(kSyntax,KArrow(v,(KArrow(KArrow(v,kProof),kProof)))))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "lr_eqn"
        (let v = mk_Var () in
        KArrow(v,KArrow(kProof,KArrow(kProof,kProof))))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "rl_eqn"
        (let v = mk_Var () in
        KArrow(v,KArrow(kProof,KArrow(kProof,kProof))))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "use_theorem"
        (KArrow(kTheorem,kProof))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "comment"
        (KArrow(kString,kProof))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "lclaim"
        (KArrow(kForm,kProof))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "claim"
        kProof
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "imported"
        (KArrow(kTheorem_list,kProof))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "proofs"
        kProof
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "equal.reflexive"
        kTheorem
        (let t = (EApp(EApp(aobj (sym_get "theorems"),
           EApp(aobj (sym_get "∀"),
             EAbs("x",EApp(EApp(aobj (sym_get "="),EVar 0),EVar 0),mk_Var()))),
               aobj (sym_get "claim"))) in type_strong t kTheorem; Def t)
        Trivial true true Kernel None in
  let _ = add_sym "undef"
        (mk_Var())
        Cst
        Trivial true true Kernel None in
  let _ = let v = mk_Var() in
        add_sym "start_match"
        (KArrow(v,v))
        (Def (EAbs("match",EVar 0,v)))
        Trivial true true Kernel None in
  let _ = add_sym "theorem_list_cons"
        (KArrow(kTheorem, KArrow(kTheorem_list,kTheorem_list)))
        Cst
        Trivial true true Kernel None in
  let _ = add_sym "theorem_list_nil"
        kTheorem_list
        Cst
        Trivial true true Kernel None in
(* basic functions *)
  let decode_int a1 = match a1 with
    EData (EInt n) -> n
  | _ -> raise Exit
  in
  let cont_stack n cont l =
    let rl = ref [] in
    if List.length l < n then raise Exit else
    let rec fn n l = match n, l with
      0, _ -> rl := l; []
    |  n, ((a1,e1,d1)::l)  -> (cont [] e1 d1 a1)::(fn (n-1) l)
    | _ ->  failwith "bug in cont_stack"
    in
    let l0 = fn n l in !rl, l0
  in
  let eval_bin_int f _ cont ret stack _ =
    match cont_stack 2 cont stack with
      [], [a1; a2] ->
	ret [] (EData (EInt (f (decode_int a1) (decode_int a2))))
    | _ -> failwith "bug in eval_bin_int" in
  let fun_add_obj = add_sym "add_num"
      	(KArrow(kNum,KArrow(kNum,kNum)))
	(Fun 0)
        Trivial true true Kernel None in
  let _ = add_fun (eval_bin_int ( Num.(+/) ) fun_add_obj) in
  let fun_sub_obj = add_sym "sub_num"
      	(KArrow(kNum,KArrow(kNum,kNum)))
	(Fun 1)
        Trivial true true Kernel None in
  let _ = add_fun (eval_bin_int ( Num.(-/) ) fun_sub_obj) in
  let fun_mul_obj = add_sym "mul_num"
      	(KArrow(kNum,KArrow(kNum,kNum)))
	(Fun 2)
        Trivial true true Kernel None in
  let _ = add_fun (eval_bin_int ( Num.( */) ) fun_mul_obj) in
  let fun_div_obj = add_sym "div_num"
      	(KArrow(kNum,KArrow(kNum,kNum)))
	(Fun 3)
        Trivial true true Kernel None in
  let _ = add_fun (eval_bin_int ( Num.(//) ) fun_div_obj) in
(* constant needed for tex generation *)
  let _ = add_sym ":="
        (KArrow(mk_Var (),KArrow(mk_Var (),kUnit)))
        Cst
        (snd (syntax_of_string false
           "Infix[10] x \":=\" y ;"))
        true true Kernel None in
  ()


let _ = the_base :=
  if !compiling || base_name = ""
    then begin
      let b = new_base () in
      init_data_af2 b;
      b
    end else
      fst (load_base [""] (Filename.concat dirname base_name))


let tsym_get s =
  try sym_get s
  with Not_found ->
    open_hbox (); print_string "\"";
    print_string s; print_string "\" not in the base !";
    print_newline (); raise Error


let oForm = tsym_get "prop"
let kForm = KAtom(oForm, [])

let oProof = tsym_get "proof"
let kProof = KAtom(oProof, [])

let oTheorem = tsym_get "theorem"
let kTheorem = KAtom (oTheorem, [])
let _ = fkTheorem := kTheorem

let oNum = tsym_get "num"
let kNum = KAtom(oNum, [])
let oString = tsym_get "string"
let kString = KAtom(oString, [])
let oSyntax = tsym_get "syntax"
let kSyntax = KAtom(oSyntax, [])
let oUnit = tsym_get "unit"
let kUnit = KAtom(oUnit, [])

let iOption = tsym_get "option"
let iList = tsym_get "list"
let iPair = tsym_get "product"
let iSum = tsym_get "sum"

let kTheorem_list = KAtom (iList, [kTheorem])

let arrow_obj  = tsym_get "→"
let _ = farrow_obj := arrow_obj
let forall_obj = tsym_get "∀"
let equal_obj = tsym_get "="
let theorem_obj = tsym_get "theorems"
let _ = ftheorem_obj := theorem_obj
let arrow_intro_obj = tsym_get "arrow_intro"
let arrow_elim_obj = tsym_get "arrow_elim"
let cut_rule_obj = tsym_get "cut_rule"
let forall_intro_obj = tsym_get "forall_intro"
let forall_elim_obj = tsym_get "forall_elim"
let devl_def_obj = tsym_get "devl_def"
let fact_def_obj = tsym_get "fact_def"
let local_def_obj = tsym_get "local_def"
let lr_eqn_obj = tsym_get "lr_eqn"
let rl_eqn_obj = tsym_get "rl_eqn"
let use_theorem_obj = tsym_get "use_theorem"
let comment_obj = tsym_get "comment"
let claim_obj = tsym_get "claim"
let lclaim_obj = tsym_get "lclaim"
let _ = fclaim_obj := claim_obj
let imported_obj = tsym_get "imported"
let proof_obj = tsym_get "proofs"
let equal_reflexive_obj = tsym_get "equal.reflexive"
let default_object = tsym_get "undef"
let match_object = tsym_get "start_match"
let theorem_list_cons_obj = tsym_get "theorem_list_cons"
let _ = ftheorem_list_cons_obj := theorem_list_cons_obj
let theorem_list_nil_obj = tsym_get "theorem_list_nil"
(*
let fun_unit_obj = tsym_get "UNIT"
let fun_add_obj = tsym_get "#+"
let fun_sub_obj = tsym_get "#-"
let fun_mul_obj = tsym_get "#*"
let fun_div_obj = tsym_get "#/"
let fun_eq_obj = tsym_get "#="
let fun_less_obj = tsym_get "#<"
let fun_lesseq_obj = tsym_get "#<="
let fun_gt_obj = tsym_get "#>"
let fun_gteq_obj = tsym_get "#>="
let fun_if_obj = tsym_get "IF"
let fun_raise_obj = tsym_get "RAISE"
let fun_catch_obj = tsym_get "CATCH"
let fun_call_obj = tsym_get "CALL"
let fun_none_obj = tsym_get "NONE"
let fun_some_obj = tsym_get "SOME"
let fun_nil_obj = tsym_get "NIL"
let fun_cons_obj = tsym_get "#:"
let fun_fix_obj = tsym_get "FIX"
let fun_new_elim_obj = tsym_get "NEW_ELIM"
let fun_new_intro_obj = tsym_get "NEW_INTRO"
let fun_close_def_obj = tsym_get "CLOSE_DEF"
let fun_def_obj = tsym_get "DEF"
let fun_elim_after_intro_obj = tsym_get "ELIM_AFTER_INTRO"
let fun_fun_obj = tsym_get "FUN"
let fun_new_rewrite_obj = tsym_get "NEW_REWRITE"
let fun_save_obj = tsym_get "SAVE"
let fun_quit_obj = tsym_get "QUIT"
let fun_cst_obj = tsym_get "CST"
let fun_local_obj = tsym_get "LOCAL"
let fun_goal_obj = tsym_get "GOAL"
let fun_intro_num_obj = tsym_get "INTRO_NUM"
let fun_intro_names_obj = tsym_get "INTRO_NAMES"
let fun_intro_objs_obj = tsym_get "INTRO_OBJS"
let fun_match_obj = tsym_get "MATCH"
let fun_trivial_obj = tsym_get "TRIVIAL"
let fun_auto_obj = tsym_get "AUTO"
let fun_use_obj = tsym_get "USE"
let fun_rmh_obj = tsym_get "RMH"
let fun_slh_obj = tsym_get "SLH"
let fun_axiom_obj = tsym_get "AXIOM"
let fun_pair_obj = tsym_get "#,"
let fun_fst_obj = tsym_get "FST"
let fun_snd_obj = tsym_get "SND"
let fun_inl_obj = tsym_get "INL"
let fun_inr_obj = tsym_get "INR"
*)
(*
let fun__obj = tsym_get "#"
let fun__obj = tsym_get "#"
let fun__obj = tsym_get "#"
*)

let type_form e =
    let k = type_check e in
    try
      unif k kForm
    with
      Clash -> failwith "This is not a formula !"


let rewrite_rules = get_table "equation"
let tbl_rewrite = get_Equations (get_ext_tbl rewrite_rules)

let intro_ext = get_table "intro"
let tbl_intro = get_Rules (get_ext_tbl intro_ext)

let elim_ext = get_table "elim"
let tbl_elim = get_Rules (get_ext_tbl elim_ext)

let elim_after_intro =  get_table "elim_after_intro"
let tbl_elim_after_intro = get_Trivial_Hacks (get_ext_tbl elim_after_intro)

let close_def =  get_table "closed"
let tbl_close_def = get_Trivial_Hacks (get_ext_tbl close_def)
let _ = fis_close := function o ->
  try
    let _ = symhash_find tbl_close_def o in true
  with Not_found -> false

let tex_syntax = get_table "tex"
let tbl_tex_syntax = get_Tex_syntax (get_ext_tbl tex_syntax)
let _ = ftbl_tex_syntax := tbl_tex_syntax

let and_obj = ref dummy_obj
let let_obj = ref dummy_obj
let or_obj = ref dummy_obj
let false_obj = ref dummy_obj
let true_obj = ref dummy_obj
let diff_obj = ref dummy_obj
let not_obj = ref dummy_obj
let exists_obj = ref dummy_obj
let exists_one_obj = ref dummy_obj
let and_elim_l_obj = ref dummy_obj
let and_elim_r_obj = ref dummy_obj
let peirce_law_obj = ref dummy_obj
let absurd_obj = ref dummy_obj
let contradiction_obj = ref dummy_obj
let false_elim_obj = ref dummy_obj

let after_pervasives () =
  if not init then begin
    and_obj := tsym_get "∧";
    let_obj := tsym_get "Let";
    or_obj := tsym_get "∨";
    diff_obj := tsym_get "≠";
    not_obj := tsym_get "¬";
    false_obj := tsym_get "False";
    true_obj := tsym_get "True";
    exists_obj := tsym_get "∃";
    exists_one_obj := tsym_get "∃!";
    and_elim_l_obj := tsym_get "conjunction.left.elim";
    and_elim_r_obj := tsym_get "conjunction.right.elim";
    peirce_law_obj := tsym_get "peirce_law";
    absurd_obj := tsym_get "absurd";
    contradiction_obj := tsym_get "contradiction";
    false_elim_obj := tsym_get "false.elim"
  end

let decom force t =
  let rec fn acc = function
      EApp(t,a) -> fn (a::acc) t
    | EAtom(o,k) -> (
	try
	  if !fis_close o && not force then None
    	  else Some (kind_inst o k)
    	with Not_found -> None)
        , o, k, acc
    | UVar(n,_) -> fn acc (getuvar n)
    | _ -> raise Not_found
  in fn [] t

let decom' t =
  let rec fn acc = function
    EApp(t,a) -> fn (a::acc) t
  | EAtom(o,k) -> (try if !fis_close o then None
                                           else Some (kind_inst o k)
                       with Not_found -> None)
                       , Oneq o, k, acc
  | UVar(n,_) -> fn acc (getuvar n)
  | UCst(n,k) -> None, Uneq n, [k], acc
  | EData(Data.EInt _) -> None, Alleq, [kNum], acc
  | EData(Data.EString _) -> None, Alleq, [kString], acc
  | _ -> raise Not_found
  in fn [] t

let decom'' t =
  let rec fn acc = function
    EApp(t,a) -> fn (a::acc) t
  | EAtom(o,k) ->
      (try if !fis_close o then None
                                           else Some (kind_inst o k)
                       with Not_found -> None)
                       , Oneq o, k, acc
  | UVar(n,_) -> fn acc (getuvar n)
  | UCst(n,k) -> None, Uneq n, [k], acc
  | EData(Data.EInt _) -> None, Alleq, [kNum], acc
  | EData(Data.EString _) -> None, Alleq, [kString], acc
  | EAbs(_,t,_) -> fn acc t
  | _ -> raise Not_found
  in fn [] t


let fNONE = lnot 0x00
let fALLE = lnot 0x01
let fTOT =  lnot 0x02   (* -t option *)
let fNEC  = lnot 0x04  (* -n option *)
let fINV  = lnot 0x1000       (* invertible rule *)
let fREM  = lnot 0x4000       (* remove hyp in trivial for invertible *)

let isALLE x = x land 0x01 = 0
let isTOT x = x land 0x02 = 0
let isNEC x = x land 0x04 = 0
let isINV x = x land 0x1000 = 0
let isREM x = x land 0x4000 = 0

let add_intro constructor total nec inv s e order exported =
  let head_fun = ref None in
  let head_pred = ref None in
  let e1, (b, n, pat) = match (Data_base.Object.get_value e).fvalue with
    Def(EApp(EApp(EAtom _,e),_)) ->
      let rec fn de d = function
        EApp(EAtom(o',_),(EAbs (_,_,k) as e))
       	      when o' == forall_obj ->
            fn (de+1) (d+1) (norm_expr (EApp(e,UCst(de,k))))
      | EApp(EApp(EAtom(o',_),_),e)
	      when o' == arrow_obj ->
            fn de (d+1) e
      | e ->
          let k, _ = head e in
          (match k with
            Oneq o -> head_pred := Some o
          | _ -> ());
          let b = ref true in
          for i = 0 to (de - 1) do
            b:= occur i e
          done;
          if total then begin
            match e with
              EApp(_,ea) -> (
                match fst (head ea) with
                  Oneq o -> head_fun := Some o
                | _ -> raise (Gen_error "This is not a totality theorem"))
            | _ -> raise (Gen_error "This is not a totality theorem")
          end;
          !b, d, make_pattern e
      in e, fn 0 0 e
  | _ -> failwith "This is not a valid introduction rule (1)" in
  if !head_pred = None && !head_fun = None then
    failwith "This is not a valid introduction rule (2)";
  let opt =
    (if b then fALLE else fNONE) land
    (if nec then fNEC else fNONE) land
    (if inv then fINV else fNONE)
  in
  (match !head_pred with
    Some o when !head_fun = None || constructor ->
      add_Rules intro_ext o s e1 e pat n (Intro_opt (opt, None)) order exported
  | _ -> ());
  (match !head_fun with
    Some o ->
      let l = match !head_pred with
                None -> (Intro_opt (opt land fTOT, None))
              | Some o -> (Intro_opt (opt land fTOT land fINV, Some o)) in
      add_Rules intro_ext o s e1 e pat n l order exported
  | None -> ())

let fLEFT = lnot 0x01       (* left rule *)
let fDND =  lnot 0x08        (* end by a vairable *)
let fTRM =  lnot 0x10        (* must match the goal (-t option)*)
let fCTD =  lnot 0x20        (* uses intro *)

let isLEFT x = x land 0x01 = 0
let isDND x = x land 0x08 = 0
let isTRM x = x land 0x10 = 0
let isCTD x = x land 0x20 = 0

let add_elim o abbrev n e opti order exported =
  let isdnd = ref false in
  let e1, n, las, pat = match (Data_base.Object.get_value e).fvalue with
    Def(EApp(EApp(EAtom _,e),_)) ->
      let rec fn acc n d = function
        EApp(EAtom(o',_),(EAbs(_,_,k) as e))
            when o' == forall_obj ->
          fn (EVar (-1)::acc) n (d+1) (norm_expr (EApp(e, (UCst(d,k)))))
      | EApp(EApp(EAtom(o',_),ea),e)
            when o' == arrow_obj ->
          let _, o'' = head ea in
          if o'' == o then
            if n = 1 then begin
              match e with
                  UCst(cn,_) ->
		    (List.rev acc), (d+1), (Some cn), (make_pattern ea)
              	| e ->
		    let rec is_false = function
   	      	        EApp(EAtom(o,_),EAbs(_,EVar 0,_))
		      	  when o == forall_obj ->
			    (List.rev acc), (d+2), Some d, (make_pattern ea)
		      | e -> (
			  try
			    let f,_,_,args = decom true e in
			      match f with
				  Some f ->
				    let e = norm_sexpr f args in
				    is_false e
				| None -> raise Not_found
			  with Not_found ->
			    match fst (head e) with
				Uneq cn -> isdnd := true;
                                  (List.rev acc), (d+1),
				  Some cn, (make_pattern ea)
                               | _ -> [], (d+1), None, (make_pattern ea))
		    in is_false e
            end else fn (ea::acc) (n-1) (d+1) e
          else fn (ea::acc) n (d+1) e
      | e ->
	  try
	    let f,_,_,args = decom true e in
	    match f with
		Some f ->
		  let e = norm_sexpr f args in
		    fn acc n d e
	      | None -> raise Not_found
	  with Not_found ->
            raise (Gen_error "Illegal elimination for this predicate")
      in
      let las, d, cn, pat = fn [] n 0 e in
      let opti = if cn = None then opti else opti land fLEFT in
      let opti = if !isdnd then opti land fDND else opti in
      if isINV opti && (not (isLEFT opti) || (isDND opti)) then
        raise (Gen_error "option \"-i\" illegal here (not left rule)");
      if isREM opti && (not (isINV opti)) then
        raise (Gen_error "option \"-rm\" need option \"-i\"");
      let ctd = ref true in
      let las =
        match cn with
          None -> [opti]
        | Some cn ->
          let rec gn d = function
            EApp(EAtom(o',_),EAbs(_,e,_)) ->
              if o' == forall_obj then
                gn (d+1) e
              else
                -1
          | EApp(EApp(EAtom(o',_),ea),e) ->
              if o' == arrow_obj then begin
                if !ctd && Set.mem cn (list_ucst ea) then ctd:=false;
                gn (d+1) e
              end else
                -1
          | EVar (-1) -> -4
          | e when fst(head e) = Uneq cn ->
              d
          | _ -> -1
          in
          let l = List.map (gn 0) las in
          let ctd = !ctd && List.for_all (fun x -> x < 0) l in
          (if ctd then (opti land fCTD) else opti)::l

      in e, d, las, pat
  | _ -> failwith "This is not a valid elimination rule" in
  add_Rules elim_ext o abbrev e1 e pat n (Elim_opt las) order exported

let add_elim_after_intro o n exported =
  add_Trivial_Hacks elim_after_intro o n exported

let fdo_add_close = ref (fun _ -> failwith "fdo_add_close not ready")
let add_close_def goal_num o exported =
  begin
    if is_capsule o then begin
      if exported then failwith "Can't export local symbol";
      !fdo_add_close goal_num o
    end else add_Trivial_Hacks close_def o 0 exported
  end;
  print_endline ("Symbol \""^(get_name o)^"\" added to \"close_def\" list.")

let fdo_add_syntax = ref (fun _ -> failwith "fdo_add_syntax not ready")
let add_tex_syntax goal_num o name sy exported =
  if is_capsule o then begin
      if exported then failwith "Can't export local symbol";
    !fdo_add_syntax goal_num o name sy
    end else add_Tex_syntax tex_syntax o name sy exported

let add_basic_tex () =
  let n,sy = (syntax_of_string true "rInfix[8] x \"\\\\rightarrow\" y ;") in
  add_tex_syntax [0] arrow_obj n sy false;
  let n,sy = (syntax_of_string true
          "Prefix[6] \"\\\\forall\" \\A,(λR,x(R x)):$→ \\ A ;") in
  add_tex_syntax [0] forall_obj n sy false;
  let n,sy = (syntax_of_string true "Infix[5] x \"=\" y ;") in
  add_tex_syntax [0] equal_obj n sy false

exception Dont_Know_Eq

let decompose_eq ad e =
  (* REMARQUE: e est-il normal ?  on le suppose *)
  let find_var = ref false in
  let rec fn nc acc cl = function
    EApp(EAtom(o1,_),EAbs(s,a1,k)) when o1 == forall_obj ->
      let l = fn nc [] cl (get_inst a1) in
      let l = List.map (function e1,e2,nl,cl,nc,keq ->
        (EAbs(s,e1,k)),(EAbs(s,e2,k)),(nl+1),cl,nc,keq) l in
      l @ acc
  | EApp(EApp(EAtom(o1,k1),a1),a2) when o1 == equal_obj ->
      let cl = List.rev cl in
      if List.mem cl ad then acc
      else if fst (head a1) = Uveq || fst (head a2) = Uveq
        then (find_var:=true; acc)
      else
      (a1,a2,0,cl,nc,List.hd k1)::acc
  | EApp(EApp(EAtom(o1,_),_),a2) when o1 == arrow_obj ->
      fn (nc+1) acc cl a2
  | EApp(EApp(EAtom(o1,_),a1),a2) when o1 == !and_obj ->
      fn nc (fn nc acc (Left_and::cl) a1) (Right_and::cl) a2
  | UVar (n,_) -> (try fn nc acc cl (getuvar n)
                  with Not_found -> find_var:= true; acc)
  | e ->
      try
	let (f, o, k, u) = decom false e in
	match f with
	  None -> raise Not_found
	| Some f ->
            let _, fe = build_subterm o k u in
            let ne = norm_expr (EApp(fe,f)) in
	    fn nc acc (Open_def::cl) ne
      with Not_found -> acc

  in let r = fn 0 [] [] e in
     if r = [] then
       (if !find_var then
         raise Dont_Know_Eq
       else
         raise (Gen_error "Not_an_equation"));
     r, !find_var

let add_rewrite opt e0 exported =
  let e = match (Data_base.Object.get_value e0).fvalue with
    Def(EApp(EApp(EAtom(o,_),e),_)) ->
      if o == theorem_obj then e
      else raise (Gen_error "Not an equation")
  | _ -> raise (Gen_error "Not an equation") in
  let l = fst (decompose_eq [] e) in
  let fn (e1,e2,nl,cl,nc,keq) =
    let v = mk_Var() in
    (try
      type_strong e1 v;
      type_strong e2 v
    with
      Clash -> failwith "bug: Ill_types equation");
    let _,_,t1,t2 = saturate e1 e2 nl v keq [] in
    let _,_,t'1,t'2 = saturate e1 e2 nl v keq [] in
    let sy = uni_expr (Map.empty, (norm_expr t1), (norm_expr t2))
                      (Map.empty, (norm_expr t'2), (norm_expr t'1))
    in
    let o1,_ = head e1 and o2,_ = head e2 in
    if (o1 == Alleq && opt <> 1) || (o2 == Alleq && opt <> 0) then
      raise (Gen_error "Invalid equation");
    if o1 <> Alleq && opt <> 1 then
      add_Equations rewrite_rules o1 o2 true e1 e2 nl (Eq_theo e0)
                    v cl sy nc exported;
    if o2 <> Alleq && opt <> 0 then
      add_Equations rewrite_rules o2 o1 false e2 e1 nl (Eq_theo e0)
                    v cl sy nc exported

  in
    if l = [] then raise (Gen_error "Invalid equation")
              else List.iter fn l

let delete_special s o =
  try
    let tbl = get_table s in
    try
      Base.ext_remove tbl [o]
    with Not_found ->
      raise (Gen_error ("No symbol `"^(get_name o)^"' in table "^s))
  with
    Not_found -> raise (Gen_error ("Unknown table : \""^s^"\"."))

let rec default_of t = match norm2 t with
  KArrow(t1,t2) -> EAbs("x",default_of t2, t1)
| _ -> EAtom(default_object, [t])

let print_theo = function
      [goal;_] ->
           goal
    | _ -> raise Not_found

let _ = print_sp  := (theorem_obj,print_theo)::!print_sp

let print_proof s =
    try
      let v = get_value (sym_get s) in
      match v with
        Def (EApp(EApp(EAtom(o,_),_),prf)) when o == theorem_obj ->
          let pr sy =
            open_hovbox 0;
            print_string s;
            print_string " ="; print_break 1 3;
            print_expr_sy sy prf; print_cut ();
            print_newline ()
          in
          print_pipe_and_stdout pr
      | _ -> raise Exit
    with _ ->
      raise (Gen_error (s^" is not a theorem"))
