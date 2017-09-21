(* $State: Exp $ $Date: 2000/10/12 09:58:26 $ $Revision: 1.1.1.1 $ *)
(*######################################################*)
(*			eval.ml				*)
(*######################################################*)

open Format
open Basic
open Lexer
open Local
open Types.Base
open Types
open Parser
open Print
open Typing
open Safe_add
open Af2_basic
open Files
open Lambda_util
open Type_check
open Interact
open Rewrite
open Pattern
open Flags
open Module
open Data_info
open Sys
open Tex

let decode_int a1 = match a1 with
    EInt n -> n
  | EVar _ -> raise Exit
  | _ -> failwith "bug in decode_int"

let decode_string a1 = match a1 with
    EString s -> s
  | EVar _ -> raise Exit
  | _ -> failwith "bug in decode_string"

let decode_bool a1 = match a1 with
    EAtom(o,_) when o == fun_true_obj -> true
  | EAtom(o,_) when o == fun_false_obj -> false
  | EVar _ -> raise Exit
  | _ -> failwith "bug in decode_bool"

let decode_option f a1 = match a1 with
    EAtom(o,_) when o == fun_none_obj -> None
  | EApp(EAtom(o,_), e) when o == fun_some_obj -> Some (f e)
  | EVar _ -> raise Exit
  | _ -> failwith "bug in decode_option"

let rec decode_list f a1 = match a1 with
    EAtom(o,_) when o == fun_nil_obj -> []
  | EApp(EApp(EAtom(o,_), e), l) when o == fun_cons_obj -> 
      (f e)::(decode_list f l)
  | EVar _ -> raise Exit
  | _ -> failwith "bug in decode_list"

let rec decode_pair df ds a1 = match a1 with
    EApp(EApp(EAtom(o,_), f), s) when o == fun_pair_obj -> 
      (df f), (ds s)
  | EVar _ -> raise Exit
  | _ -> failwith "bug in decode_list"

type ('a,'b) sum =
  Inl of 'a
| Inr of 'b

let rec decode_sum dl dr a1 = match a1 with
    EApp(EAtom(o,_), l) when o == fun_inl_obj -> 
      Inl (dl l)
  | EApp(EAtom(o,_), r) when o == fun_inr_obj -> 
      Inr (dr r)
  | EVar _ -> raise Exit
  | _ -> failwith "bug in decode_list"

let decode_obj a1 = match a1 with
    EAtom(o,_) -> o
  | EVar _ -> raise Exit
  | _ -> failwith "Invalid argument: wait for object"

let decode_syntax a1 = match a1 with
    Syntax sy -> sy
  | EVar _ -> raise Exit
  | _ -> failwith "bug in decode_syntax"

let decode_cst a1 = match a1 with
    UCst(p,_) -> p
  | EVar _ -> raise Exit
  | _ -> failwith "Invalid argument: wait for constant"

let cont_stack n cont l =
  let rl = ref [] in
  if List.length l < n then raise Exit else
  let rec fn n l = match n, l with
     0, _ -> rl := l; []
  |  n, ((a1,e1,d1)::l)  -> (cont [] e1 d1 a1)::(fn (n-1) l)
  | _ ->  failwith "bug in cont_stack"
  in 
  let l0 = fn n l in !rl, l0

let eval_bin_int f h cont ret stack _ =
  match cont_stack 2 cont stack with 
    [], [a1; a2] ->
  ret [] (EInt (f (decode_int a1) (decode_int a2)))
  | _ -> failwith "bug in eval_bin_int"

let _ = add_fun (eval_bin_int ( + ) fun_add_obj)                (* 0 *)
let _ = add_fun (eval_bin_int ( - ) fun_sub_obj)                (* 1 *)
let _ = add_fun (eval_bin_int ( * ) fun_mul_obj)                (* 2 *)
let _ = add_fun (eval_bin_int ( / ) fun_div_obj)                (* 3 *)

let ftrue = aobj fun_true_obj
let ffalse = aobj fun_false_obj

let eval_bin_test f h cont ret stack _ =
  match cont_stack 2 cont stack with 
    [], [a1; a2] ->
  if f a1 a2 then ret [] ftrue else ret [] ffalse
  | _ -> failwith "bug in eval_bin_test"

let _ = add_fun (eval_bin_test equal_expr fun_eq_obj)           (* 4 *) 
let _ = add_fun (eval_bin_test (fun x y -> cmp_expr x y < 0) fun_less_obj)   
                                                                (* 5 *) 
let _ = add_fun (eval_bin_test (fun x y -> cmp_expr x y <= 0) fun_lesseq_obj)
                                                                (* 6 *) 
let _ = add_fun (eval_bin_test (fun x y -> cmp_expr x y > 0) fun_gt_obj)
                                                                (* 7 *) 
let _ = add_fun (eval_bin_test (fun x y -> cmp_expr x y >= 0) fun_gteq_obj)
                                                                (* 8 *) 

let ifthenelse cont ret stack _ = 
  match stack with 
    [] | [_] | [_;_] -> raise Exit
  | (a1,e1,d1):: (a2,e2,d2):: (a3,e3,d3):: l ->
  let a1 = decode_bool (cont [] e1 d1 a1) in
  if a1 then cont l e2 d2 a2 else cont l e3 d3 a3

let _ = add_fun ifthenelse                                      (* 9 *)

let fixpoint cont ret stack _ = 
  match stack with 
    [] -> raise Exit
  | (a1,e1,d1)::l ->
  let nstack = (EApp(aobj fun_fix_obj, a1), e1, d1)::l in 
  cont nstack e1 d1 a1

let _ = add_fun fixpoint                                        (* 10 *)

let fraise cont ret stack _ =
  match stack with
    [] -> raise Exit
  | (a1,e1,d1)::_ ->
  let a1 = decode_string (cont [] e1 d1 a1) in
  raise (Efun_error a1)
  
let catch cont ret stack _ =
  match stack with
    [] | [_]  -> raise Exit
  | (a1,e1,d1)::(a2,e2,d2)::l ->
  try
    cont l e1 d1 a1
  with
    e ->
      let exn = match e with 
        Ill_rule _ -> EString "rule failed"
      | Fail_matching -> EString "matching failed"
      | Efun_error s -> EString s
      | e -> raise e 
      in
      cont ((exn,[],0)::l) e2 d2 a2

let call cont ret stack odepth =
  match stack with
    [] | [_]  -> raise Exit
  | (a1,e1,d1)::(a2,e2,d2)::l ->
    let a2 = cont l e2 d2 a2 in
    cont ((a2,[],odepth)::l) e1 d1 a1

let _ = add_fun fraise                                          (* 11 *)
let _ = add_fun catch                                           (* 12 *)
let _ = add_fun call                                            (* 13 *)

let funit = aobj fun_unit_obj

let fun_new_elim cont ret stack odepth =
  match cont_stack 7 cont stack with
    [], [e; abbrev; pos; theo; opti; optn; export] ->
      add_elim
        (decode_obj e)
        (decode_string abbrev)
	(decode_int pos)
	(decode_obj theo)
	(if (decode_bool opti) then fINV else fNONE land 
         if (decode_bool optn) then fNEC else fNONE)
        (decode_bool export);
      ret [] funit
  | _ -> failwith "bug in #new_elim"

let _ = add_fun fun_new_elim                                     (* 14 *)

let decode_tri tri =
  match decode_option 
    (fun x -> decode_pair 
       decode_int 
       (fun x -> decode_pair 
          decode_int (fun x -> decode_pair 
             decode_bool decode_bool x) x) x) tri with
    None -> 
      {nlim = !trdepth; eqlvl = !eqdepth; 
       	from_trivial = false; first_order = false;
      	auto_elim =true; eqflvl = !eqflvl}
  | Some (nlim,(eqlvl,(from_trivial,first_order))) ->
      {nlim = nlim; eqlvl = eqlvl; 
       	from_trivial = from_trivial; first_order = first_order;
	auto_elim =true; eqflvl = !eqflvl}

let fun_new_intro cont ret stack odepth =
  match cont_stack 6 cont stack with
    [], [abbrev; e; optc; optt; optn; opti; export] ->
      add_intro
        (decode_bool optc)
        (decode_bool optt)
        (decode_bool optn)
        (decode_bool opti)
        (decode_string abbrev)
	(decode_obj e)
        (decode_bool export);
      ret [] funit
  | _ -> failwith "bug in #new_intro"

let _ = add_fun fun_new_intro                                     (* 15 *)

let fun_close_def cont ret stack odepth =
  match cont_stack 2 cont stack with
    [], [e; export] ->
      add_close_def
        (sym_get (decode_string e))
        (decode_bool export);
      ret [] funit
  | _ -> failwith "bug in #close_def"

let _ = add_fun fun_close_def                                     (* 16 *)

let fun_elim_after_intro cont ret stack odepth =
  match cont_stack 2 cont stack with
    [], [e; export] ->
      add_elim_after_intro
        (sym_get (decode_string e))
        0
        (decode_bool export);
      ret [] funit
  | _ -> failwith "bug in #elim_after_intro"

let _ = add_fun fun_elim_after_intro                              (* 17 *)

let fun_tex_syntax cont ret stack odepth =
  match cont_stack 4 cont stack with
    [], [e; sn; sy; export] ->
      (try 
        let o = decode_obj e in
        add_tex_syntax
          o
          (decode_string sn)
          (decode_syntax sy)
          (decode_bool export);
        ret [] funit
      with Failure "Invalid argument: wait for object" ->
        do_rule 0 "tex_syntax" (do_add_csyntax
          (decode_cst e)
          (decode_string sn)
          (decode_syntax sy));
        ret [] funit)
  | _ -> failwith "bug in #add_tex_syntax"

let _ = add_fun fun_tex_syntax                              (* 18 *)

let fun_def cont ret stack odepth =
  match cont_stack 4 cont stack with
    [], [s; e; sy; export] ->
      add_sym
      	(decode_string s)
        (type_check e)
        (Def e)
        (decode_syntax sy)
        false
        (decode_bool export)
        Idtren None;
      ret [] funit
  | _ -> failwith "bug in #def"

let _ = add_fun fun_def                                           (* 19 *)

let fun_fun cont ret stack odepth =
  match cont_stack 4 cont stack with
    [], [s; e; sy; export] ->
      add_sym
      	(decode_string s)
        (type_check e)
        (Prg e)
        (decode_syntax sy)
        false
        (decode_bool export)
        Idtren None;
      ret [] funit
  | _ -> failwith "bug in #fun"

let _ = add_fun fun_fun                                           (* 20 *)


let fun_new_rewrite cont ret stack odepth =
  match cont_stack 4 cont stack with
    [], [lr; rl; e; export] ->
      add_rewrite
        (if (decode_bool lr) then 
           if (decode_bool rl) then 2 else 0 
         else
           if (decode_bool rl) then 1 
                               else failwith "bad options for #new_rewrite")
        (decode_obj e)
        (decode_bool export);
      ret [] funit
  | _ -> failwith "bug in #new_rewrite"

let _ = add_fun fun_new_rewrite                                   (* 21 *)

let fun_save cont ret stack odepth =
  match cont_stack 2 cont stack with
    [], [s; export] ->
      do_save
      	(decode_option decode_string s)
        (decode_bool export);
      ret [] funit
  | _ -> failwith "bug in #save"

let _ = add_fun fun_save                                         (* 22 *)

let fun_quit cont ret stack odepth =
  raise Quit

let _ = add_fun fun_quit                                         (* 23 *)

let fun_cst cont ret stack odepth =
  match cont_stack 3 cont stack with
    [], [s; sty; sy] ->
      let cstr = Stream.of_string (decode_string sty ^ ";")  in
      let str = stream_map next_token cstr in
      let k = parse_kind str in
      add_sym
      	(decode_string s)
	k
        (Cst)
        (decode_syntax sy)
        false
	true
        Idtren None;
      ret [] funit
  | _ -> failwith "bug in #fun_cst"

let _ = add_fun fun_cst                                           (* 24 *)

let fun_local cont ret stack odepth =
  match cont_stack 3 cont stack with
    [], [s; e; sy] ->
      do_add_rlocal
      	(decode_string s)
        (type_check e)
        (Def e)
        (decode_syntax sy);
      ret [] funit
  | _ -> failwith "bug in #local"

let _ = add_fun fun_local                                         (* 25 *)

let fun_goal cont ret stack odepth =
  match cont_stack 1 cont stack with
    [], [e;s;ts;b] ->
      do_goal e (decode_option decode_string s)
	(decode_option decode_string ts) (decode_bool b); 
      ret [] funit
  | _ -> failwith "bug in #goal"

let _ = add_fun fun_goal                                          (* 26 *)

let fun_intro_num cont ret stack odepth =
  match cont_stack 2 cont stack with
    [], [tri; n] ->
      let n = do_rule 0 "intros" (rule_intro (ref false) (decode_tri tri) 
                                           (Num (decode_int n))) in
      ret [] (EInt n)
  | _ -> failwith "bug in #intro_num"

let _ = add_fun fun_intro_num                                     (* 27 *)

let fun_intro_names cont ret stack odepth =
  match cont_stack 2 cont stack with
    [], [tri; ln] ->
      let l = decode_list decode_string ln in
      let n = do_rule 0 "intros" (rule_intro (ref false) (decode_tri tri) (Names l)) in
      ret [] (EInt n)
  | _ -> failwith "bug in #intro_names"

let _ = add_fun fun_intro_names                                   (* 28 *)

let fun_intro_objs cont ret stack odepth =
  match cont_stack 2 cont stack with
    [], [tri; ln] ->
      let l = decode_list (fun s -> sym_get (decode_string s)) ln in
      let n = do_rule 0 "intros" (rule_intro (ref false) (decode_tri tri) (Auth l)) in
      ret [] (EInt n)
  | _ -> failwith "bug in #intro_objs"

let _ = add_fun fun_intro_objs                                   (* 29 *)

let fun_match cont ret stack odepth =
  match cont_stack 2 cont stack with
    [], [e1; e2] ->
      smatch !cur_local e1 e2;
      ret [] funit
  | _ -> failwith "bug in #match"

let _ = add_fun fun_match                                        (* 30 *)

let fun_trivial cont ret stack odepth =
  match cont_stack 4 cont stack with
    [], [min; l1; l2; tri] ->
      let min = decode_bool min in
      let l1 = decode_list decode_string l1 in 
      let l2 = decode_list decode_string l2 in 
      let tri = decode_tri tri in
      let n = do_rule 0 "trivial" (rule_trivial min l1 l2 tri) in      
      ret [] (EInt n)
  | _ -> failwith "bug in #trivial"

let _ = add_fun fun_trivial                                        (* 31 *)

let fun_auto cont ret stack odepth =
  match cont_stack 4 cont stack with
    [], [min; l1; l2; tri] ->
      let min = decode_bool min in
      let l1 = decode_list decode_string l1 in 
      let l2 = decode_list decode_string l2 in 
      let tri = decode_tri tri in
      let n = do_rule 0 "auto" (rule_auto min l1 l2 tri) in      
      ret [] (EInt n)
  | _ -> failwith "bug in #auto"

let _ = add_fun fun_auto                                          (* 32 *)

let fun_use cont ret stack odepth =
  match cont_stack 3 cont stack with
    [], [tri; s; e] ->
      let s = decode_string s in
      let n = do_rule 0 "use" (rule_use (decode_tri tri) s e) in      
      ret [] (EInt n)
  | _ -> failwith "bug in #use"

let _ = add_fun fun_use                                           (* 33 *)

let fun_rmh cont ret stack odepth =
  match cont_stack 1 cont stack with
    [], [l] ->
      let l = decode_list decode_string l in
      let n = do_rule 0 "rmh" (rule_rm true l) in      
      ret [] (EInt n)
  | _ -> failwith "bug in #rmh"

let _ = add_fun fun_rmh                                           (* 34 *)

let fun_slh cont ret stack odepth =
  match cont_stack 1 cont stack with
    [], [l] ->
      let l = decode_list decode_string l in
      let n = do_rule 0 "slh" (rule_rm false l) in      
      ret [] (EInt n)
  | _ -> failwith "bug in #slh"

let _ = add_fun fun_slh                                           (* 35 *)

let fun_axiom cont ret stack odepth =
  match cont_stack 2 cont stack with
    [], [tri; s] ->
      let s = decode_string s in
      let n = do_rule 0 "axiom" (rule_axiom false (decode_tri tri) s) in      
      ret [] (EInt n)
  | _ -> failwith "bug in #axiom"

let _ = add_fun fun_axiom                                           (* 36 *)

let fun_fst cont ret stack odepth =
  match cont_stack 1 cont stack with
    l, [s] ->
      let c = decode_pair (fun x -> x) (fun x -> x) s in
      if l = [] then ret [] (fst c) else cont l [] 0 (fst c)
  | _ -> failwith "bug in #fst"

let _ = add_fun fun_fst                                             (* 37 *)

let fun_snd cont ret stack odepth =
  match cont_stack 1 cont stack with
    l, [s] ->
      let c = decode_pair (fun x -> x) (fun x -> x) s in
      if l = [] then ret [] (snd c) else cont l [] 0 (snd c)
  | _ -> failwith "bug in #snd"
 
let _ = add_fun fun_snd                                             (* 38 *)
 









