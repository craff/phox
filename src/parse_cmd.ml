(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.41 $ *)
(*######################################################*)
(*			parse_cmd.ml			*)
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
open Compile
open Inductive
open Parse_lambda
open Lambda
open New_cmd
open Option
open Proof_general
open Af2_logic

exception End_of_module

let parse_sym = parser
  [< s = parse_ident >] ->
    (try let _ = sym_get s in s with Not_found -> raise (Not_def s))
| [< 'Dol; 'tok >] -> (match tok with
        Ident s -> (try let _ = sym_get s in s
		    with Not_found -> raise (Not_def s))
      | Kwd s -> (try let _ = sym_get s in s
		  with Not_found -> raise (Not_def s))
      | _ -> raise (Stream.Error ("Wait for a symbol after $, but got " ^
                                (string_of_token tok))))

let parse_syml = parser
  [< s = parse_ident >] ->
    (try let _ = find_local s in s with Not_found ->
     try let _ = sym_get s in s with Not_found -> raise (Not_def s))
| [< 'Dol; 'tok >] -> (match tok with
        Ident s ->
          (try let _ = find_local s in s with Not_found ->
           try let _ = sym_get s in s with Not_found -> raise (Not_def s))
      | Kwd s ->
          (try let _ = find_local s in s with Not_found ->
           try let _ = sym_get s in s with Not_found -> raise (Not_def s))
      | _ -> raise (Stream.Error ("Wait for a symbol after $, but got " ^
                                (string_of_token tok))))

let parse_intd p = parser
  [< 'Num n >] -> Num.int_of_num n
| [< >] -> p

let parse_kindd = parser
  [<k =  parse_kind >] -> k
| [< >] -> mk_Var ()

let parse_symlist =
let rec fn l = parser
  [< s = parse_sym; suit >] ->
    let o = try sym_get s with Not_found -> raise (Not_def s) in
    fn (o::l) suit
| [< >] -> l
in fn []

let rec parse_exprlist tstr = match tstr with parser
    [< 'Kwd "[";
       'Ident str ?? serror "an identifier" tstr;
       lo = parse_with;
       'Kwd "]" ?? serror "]" tstr;
       l = parse_exprlist' >] ->
      (match l with
	l::ls -> (NOptDf(str,lo)::l)::ls
      | [] -> [[NOptDf(str,lo)]])
  | [< e = parse_expr; l = parse_exprlist' >] ->
      let k = type_check e in
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

let parse_boold b = parser
  [< 'Ident "true" >] -> true
| [< 'Ident "false" >] -> false
| [< >] -> b

let parse_value = parser
  [< 'Num n >] -> Vint (Num.int_of_num n)
| [< 'Ident "true" >] -> Vbool true
| [< 'Ident "false" >] -> Vbool false
| [< 'Str s >] -> Vstring s
| [< >] -> Vprint

let parse_option s = parser
  [< 'Kwd "-"; 'Ident s >] -> s
| [< >] -> s

let parse_path =
  let rec fn = parser
    [< 'Num n; l = fn >] -> Num.int_of_num n :: l
  | [< >] -> []
  in parser [< 'Kwd "["; l = fn; 'Kwd "]" >] -> l


let rec parse_rewrite_opt = parser
  [< 'Kwd "-"; s = parse_ident; str >] ->
    (match s with
      "l" -> (match str with parser [< 'Num n >] -> Lim (Num.int_of_num n), true, false)
    | "p" -> (match str with parser [< 'Num n >] -> Once_nth (Num.int_of_num n), true, false)
    | "P" -> (match str with parser [< l = parse_path >] ->
                                                    Once_ipath l, true, false)
    | "r" -> Ad_lib, false, false
    | "nc" -> Ad_lib, true, true
    | "ortho" -> Ortho [], true, true
    | _ ->  raise (Stream.Error "illegal option for rewrite or unfold"))
| [< >] -> Ad_lib, true, false

let parse_evaluate_opt = parser
    [< 'Ident "to"; e = parse_expr >] ->
      let e = norm_expr e in
      type_strong e kForm;
      Until e
  | [< >] -> Ad_lib

let rec parse_string_list = parser
    [< 'Str s; l = parse_string_list >] -> s::l
  | [< >] -> []

let rec parse_depend_opt = parser
  [< 'Kwd "-"; s = parse_ident >] ->
    (match s with
      "a" | "all" -> All
    | "i" | "immediate" -> Immediate
    | _ ->  raise (Stream.Error "illegal option for depend"))
| [< >] -> Axioms

let parse_rewrite_list b0 b1 =
  let rec fn b0 b1 l str =
    let b0, b1 =
      let rec gn b0 b1 =
        match parse_option "" str with
          "" -> b0, b1
        | "r" -> gn false b1
        | "nc" -> gn b0 true
        | _ -> raise (Stream.Error "illegal option for rewrite or unfold")
      in gn b0 b1
    in
    match str with parser
      [< s = parse_sym; suit >] ->
        let o = try sym_get s with Not_found -> raise (Not_def s) in
        fn true false ((b0,b1,o)::l) suit
    | [< >] -> l
  in fn b0 b1 []

let rec parse_options name ls = parser
  [< 'Kwd "-"; s = parse_ident; str >] ->
     if List.mem s ls then
       if s = "o" then
	 match str with parser
	     [< 'Float n; str >] -> (n, snd (parse_options name ls str))
       else
	 let order, l = parse_options name ls str in
	 order, (s::l)
     else
       raise (Stream.Error ("illegal option for " ^ name))
| [< >] -> 0.0, []

let parse_into p s =
  let rec fn l p tstr = match tstr with parser
    [< 'Num n; s >] -> let n = Num.int_of_num n in
    if n < 0 then gn l (-n) (max (-n) p) s else fn l n s
  | [< 'Kwd "-"; 'Ident "n" ?? serror "-n" tstr;
                 'Kwd "[" ?? serror "[" tstr;
                 names = parse_ident_list;
                 'Kwd "]" ?? serror "]" tstr; s >] ->
      fn ((0, OptInt names)::l) p s
  | [< >] -> l,p
  and gn l r p tstr = match tstr with parser
    [< 'Kwd "[";
       'Ident str ?? serror "an identifier" tstr;
       l0,p0 = fn [] 1;
       'Kwd "]" ?? serror "]" tstr; s >] ->
      fn ((r, OptDf (str,l0))::l) p s
  | [< e = parse_atomexpr; s >] -> fn ((r,OptFl e)::l) p s
  in
  let l,d = fn [] p s
  in List.sort (fun (n,_) (p,_) -> if n < p then -1 else 1) l, d

let rec test_opt l w =
  match w with
    [] ->
      let rec fn = function
        (_,OptFl e)::l -> type_strong e (mk_Var ()); fn l
      | (_,OptDf (_,l'))::l -> fn l'; fn l
      | _::l' -> fn l'
      | [] -> ()
      in fn l; l
  | w ->
    if l <> [] then raise
      (Gen_error "`with' is incompatible with other options");
    [0,OptWith w]

let rec parse_identa_list tstr = match tstr with parser
  [< s = parse_ident; l = parse_identa_list >] -> (s,None) :: l
| [< 'Kwd "["; 'Ident s ?? serror "a identifier" tstr; lw = parse_with ;  'Kwd "]" ?? serror "]" tstr;
     l = parse_identa_list  >] -> (s,Some lw)::l
| [< >] -> []

let parse_inta tstr = match tstr with parser
  [< 'Num n >] -> RNum (Num.int_of_num n)
| [< s = parse_ident; l = parse_identa_list >] -> Names ((s,None) :: l)
| [< 'Kwd "["; 'Ident s ?? serror "an identifier" tstr; lw = parse_with ; 'Kwd "]" ?? serror "]" tstr;
     l = parse_identa_list  >] -> Names ((s,Some lw)::l)
| [< >] -> RNum 1

let parse_ints = parser
  [< l = parse_symlist >] -> if l = [] then Default else Auth l

let rec parse_trivial_opts take_int str =
  let default =  {nlim = !trdepth; eqlvl = !eqdepth;
               	from_trivial = take_int; first_order = not take_int;
		auto_elim = true; eqflvl = !eqflvl}
  in
  try
    match Stream.peek str with
      Some (Kwd "[") ->
	(match Stream.npeek 2 str with
	  [ Kwd "["; Ident _ ] -> default
	| _ -> raise Exit)
    | _ -> raise Exit
  with Exit ->
  match str with parser
    [< 'Kwd "[" >] ->
      let nlim = ref !trdepth in
      let eqlvl = ref !eqdepth in
      let fo = ref (not take_int) in
      let ft = ref take_int in
      let rec fn = parser
        [< 'Kwd "-" >] ->
          (match str with parser
            [< 'Ident "lim"; 'Num n >] -> nlim := Num.int_of_num n
          | [< 'Ident "eq"; 'Num n >] -> eqlvl := Num.int_of_num n
          | [< 'Ident "fo" >] -> fo := false
          | [< 'Ident "ft" >] -> ft := false);
          fn str
      | [< 'Kwd "+" >] ->
          (match str with parser
            [< 'Ident "fo" >] -> fo := true
          | [< 'Ident "ft" >] -> ft := true);
          fn str
      | [< 'Kwd "]" >] -> {nlim = !nlim; eqlvl = !eqlvl;
                           from_trivial = !ft; first_order = !fo;
			   auto_elim = true; eqflvl = !eqflvl}
      in fn str
  | [< 'Num n when take_int >] ->
       {nlim = Num.int_of_num n; eqlvl = !eqdepth;
        from_trivial = true; first_order = false;
	auto_elim = true; eqflvl = !eqflvl}

  | [< >] -> default

let rec parse_trivial_options = parser
  [< 'Kwd "-"; l = parse_ident_list; b,le,lm,lp = parse_trivial_options >] ->
    b,le,l@lm,lp
| [< 'Kwd "+"; l = parse_ident_list; b,le,lm,lp = parse_trivial_options >] ->
    b,le,lm,l@lp
| [< 'Kwd "="; l = parse_ident_list; b,le,lm,lp = parse_trivial_options >] ->
    false, l@le,lm,lp
| [< >] -> true, [], [], []

let test_del () =
  if !cur_proof <> No_proof then
    raise (Gen_error "Can not use delete commands in proof mode")

let maybe_str = parser
    [< 'Str str >] -> Some str
  | [< >] -> None

let maybe_ident = parser
    [< ident = parse_ident >] -> Some ident
  | [< >] -> None

let rec parse_defrec acc tstr  = match tstr with parser
  [< 'Ident s; l = parse_args; 'Kwd "=";
     e = parse_free_expr >] ->
       parse_defrec_aux ((s,l,e)::acc) tstr

and parse_defrec_aux acc tstr  = match tstr with parser
  [< 'Ident "and" >] ->  parse_defrec acc tstr
| [< >] -> acc

let parse_goal_number tstr =
  let min = ref max_int in
  let l =
    match tstr with parser
      [< 'Kwd "[" >] ->
	let rec fn tstr = match tstr with parser
	  [< 'Num n; l = fn >] ->
	    let n = Num.int_of_num n in
	    if n < !min then min := n - 1;
	    n::l
	| [< >] -> []
	in
	begin
	  match tstr with parser
	  | [< 'Num n; l = fn; 'Kwd "]"; >] ->
	      let n = Num.int_of_num n in
	      if n < !min then min := n - 1;
	      List.sort (-) (n::l)
	end
    | [< 'Kwd "[*]" >] ->
	min := 0;
	[0]
    | [< >] ->
	min := 0;
	[1]
  in
  set_local !min;
  l

let parse_export export tstr = match tstr with parser
    [< 'Ident "new_elim";
       order, opts = parse_options "new_elim" ["i";"n";"t";"o";"rm"];
       s = parse_sym ?? serror "a symbol" tstr;
       'Ident st ?? serror "an identifier" tstr;
       n = parse_intd 1;
       o = parse_sym ?? serror "an expression" tstr >] -> fun () -> (
          type_strong (aobj (sym_get o)) kTheorem;
          let opti = (if List.mem "i" opts then fINV else fNONE) land
                   (if List.mem "n" opts then fNEC else fNONE) land
                   (if List.mem "t" opts then fTRM else fNONE) land
	    (if List.mem "rm" opts then fREM else fNONE) in
          add_elim (sym_get s) st n (sym_get o) opti order export;
          print_endline "Theorem added to elimination rules.")
  | [< 'Ident "new_intro";
       order, opts = parse_options "new_intro" ["t";"n";"c";"i";"o"];
       'Ident st ?? serror "an identifier" tstr;
       o = parse_sym ?? serror "an expression" tstr >] -> fun () -> (
          type_strong (aobj (sym_get o)) kTheorem;
          let total = List.mem "t" opts || List.mem "c" opts in
          let constructor = List.mem "c" opts in
          let nec = List.mem "n" opts in
          let inv = List.mem "i" opts in
          add_intro constructor total nec inv st (sym_get o) order export;
          print_endline "Theorem added to introduction rules.")
  | [< 'Ident "elim_after_intro";
       s = parse_sym ?? serror "a symbol" tstr >] -> fun () -> (
          add_elim_after_intro (sym_get s) 0 export;
          print_endline "Symbol added to \"elim_after_intro\" list.")
  | [< 'Ident "def";
       s,sy,le = parse_syntax_def false ?? serror "a syntax definition" tstr;
       'Kwd "=" ?? serror "=" tstr;
       e = parse_bound_expr le ?? serror "an expression" tstr >] -> fun () -> (
          let k = type_check e in
          if k = kTheorem then
            raise (Gen_error "Can't define a theorem: prove it or use claim.");
          let e = norm_expr e in
          let _ = add_sym s k (Def e) sy false export Idtren None in ())
  | [< 'Ident "defrec"; defs = parse_defrec [] >] ->
      let names =
	List.map (fun (s,_,_) -> s, mk_Var ()) defs
      in
      let binds =
	List.map (fun (s,l,e) ->
	  let rec f e = function
	      [] -> e
	    | (s,k)::l -> EAbs(s,f e l, k) in
	  bind_free false 0 [] (f e (names@l))) defs
      in
      fun () ->
      let types =
	List.map (fun (_, k) ->
	  List.fold_left (fun acc (_, k) ->
	    KArrow(k,acc)) k (List.rev names)) names
      in
      let _ =
	List.iter2 (fun e k ->
	  type_strong e k) binds types
      in
      let csts =
	List.map2 (fun e (name, k) ->
	  let o =
	    add_sym name k Cst Trivial false export Idtren None
	  in aobj o) binds names
      in
      let apply t =
	List.fold_left (fun acc e -> EApp(acc,e)) t csts
      in
      let _ =
	List.iter2 (fun e (name, _) ->
	  let v = norm_expr (apply e) in
	  let k = type_check v in
	  let _ =
	    add_sym name k (Def v) Trivial false export Idtren None
	  in ()) binds names
      in
      ()

  | [< 'Ident "fun";
       s,sy,le = parse_syntax_def false ?? serror "a syntax definition" tstr;
       'Kwd "=" ?? serror "=" tstr;
       e = parse_bound_expr le ?? serror "an expression" tstr >] ->  fun () -> (
          let k = type_check e in
          if k = kTheorem then
            raise (Gen_error "Can't define a theorem: prove it or use claim.");
          let _ = add_sym s k (Prg e) sy false export Idtren None in ())
  | [< 'Ident ("new_equation" | "new_rewrite");
       opt = (fun str -> match parse_option "l" str with
                         "l" -> 0 | "r" -> 1 | "b" -> 2
                       | _ -> raise (Stream.Error
                                "Illegal option for new_rewrite"));
       list = parse_symlist ?? serror "a list of expressions" tstr >] -> fun () -> (
          List.iter
	   (fun o ->
	     type_strong (aobj o) kTheorem;
             add_rewrite opt o export) list;
          print_endline "Theorem(s) will be used as equations by unification.")
  | [< 'Ident "def_thlist"; 'Ident name; 'Kwd "=" ?? serror "=" tstr;
       list = parse_symlist ?? serror "a list of expressions" tstr>] -> fun () -> (
      make_th_list name list export)
  | [< 'Ident "save";
       s = maybe_ident >] -> fun () -> (
          do_save s export)
  | [< 'Ident "goal";
       e = parse_expr ?? serror "an expression" tstr >] -> fun () -> (
      do_goal e None None export)
  | [< 'Ident ("prop" | "proposition" |
               "lem"  | "lemma"       |
	       "fact" | "cor" | "corollary" |
	       "theo" | "theorem");
      'Ident th_name;
      tex_name = maybe_str;
      e = parse_expr ?? serror "an expression" tstr >] -> fun () -> (
        do_goal e (Some th_name) tex_name export)
  | [< 'Ident "claim";
      s = parse_ident ?? serror "an identifier" tstr;
      tex_name = maybe_str;
      e = parse_expr ?? serror "an expression" tstr >] -> fun () -> (
        type_form e;
        do_claim s tex_name e export)
 | [< 'Ident "prove_claim";
      s = parse_ident ?? serror "an identifier" tstr >] -> fun () -> (
     prove_claim s export)
 | [< _ = parse_inductive export >] -> fun () ->
      ()
 | [< _ = parse_data export >] -> fun () ->
                                  ()
 | [< 'Ident "cd"; 'Str s >] -> fun () -> Sys.chdir s
(* BUG: should be a rule ! *)
 | [< 'Ident "close_def";
      s = parse_sym ?? serror "a symbol" tstr >] -> fun () -> (
        add_close_def [0] (sym_get s) export)
(* BUG: should be a rule ! *)
 | [< 'Ident "tex_syntax";
      s = parse_syml
        ?? serror "a symbol" tstr;
      n,sy = parse_tex_sym ?? serror "a syntax definition" tstr >] -> fun () -> (
        (try match find_local s with
          UCst(p,_) ->
	    let _ = do_rule !auto_lvl "tex_syntax" [0] (do_add_csyntax p n sy) in
	    ()
        | _ -> failwith "bug in find_local (parse)"
        with Not_found ->
	  let export = export && not (is_local s) in
          add_tex_syntax [0] (sym_get s) n sy export);
        print_endline "Syntax added to \"tex_syntax\" list.")
(*
 | [< _ = parse_type export >] -> fun () ->
      ()
 *)
let do_print f e =
  let k = type_check e in
  open_hvbox 0;
  let e = norm_expr e in
  f e; print_break 1 1;
  let is_sort = ref false in
  (match e with
     EAtom (o,_) -> (
       match (get_value o) with
	 Def e -> print_string "= "; f e; print_break 1 1
       | Prg e -> print_string ":= "; f e; print_break 1 1
       | KCst | KDef _ -> is_sort := true;
       | _ -> ())
   | _ -> ());
  if !is_sort then begin
    print_string " is a sort"
  end else begin
    print_string ": ";
    print_kind k
  end;
  print_newline ()


let parse_one_tactic tstr = match tstr with parser
    [< 'Ident "local";
       s,sy,le = parse_syntax_def false ?? serror "a syntax definition" tstr;
       'Kwd "=" ?? serror "=" tstr;
       e = parse_bound_expr le ?? serror "an expression" tstr >] ->
      let k = type_check e in
      if k = kTheorem then
	raise (Gen_error "Can't define a theorem: prove it or use claim.");
      0, "local", (do_add_rlocal s k (Def e) sy)
  | [< 'Ident "intro";
       tri = parse_trivial_opts false;
       opt = parse_inta >] ->
      !auto_lvl, "intro", (rule_intro (ref false) tri opt)
  | [< 'Ident "intros";
       tri = parse_trivial_opts false;
       opt = parse_ints >] ->
      !auto_lvl, "intros", (rule_intro (ref false) tri opt)
  | [< 'Ident "trivial";
       tri = parse_trivial_opts true;
       b,le,lm,lp = parse_trivial_options >] ->
      let lm = match le,lm with
          [], l -> l
	| l, [] -> l
	| _,_ -> raise (Failure "\"=\" and \"-\" option are incompatible") in
      !auto_lvl, "trivial", (rule_trivial b lm lp tri)
  | [< 'Ident "auto";
       tri = parse_trivial_opts true;
       b,le,lm,lp = parse_trivial_options >] ->
      let lm = match le,lm with
          [], l -> l
	| l, [] -> l
	| _,_ -> raise (Failure "\"=\" and \"-\" option are incompatible") in
      !auto_lvl, "auto", (rule_auto b lm lp tri)
  | [< 'Ident "prove";
       tri = parse_trivial_opts false;
       s = parse_option "";
       e = parse_expr ?? serror "an expression" tstr >] ->
      0, "prove", (rule_use true tri s e)
  | [< 'Ident "use";
       tri = parse_trivial_opts false;
       s = parse_option "";
       e = parse_expr ?? serror "an expression" tstr >] ->
      0, "use", (rule_use false tri s e)
  | [< 'Ident "rmh";
       l = parse_ident_list >] ->
      0, "rmh", (rule_rm true l)
  | [< 'Ident "slh";
       l = parse_ident_list >] ->
      0, "slh", (rule_rm false l)
  | [< 'Ident "rename"; oname = parse_ident; nname = parse_ident >] ->
      0, "rename", (rule_rename oname nname)
  | [< 'Ident "axiom";
       tri = parse_trivial_opts false;
       s = parse_ident ?? serror "an identfier" tstr >] ->
      !auto_lvl, "axiom", (rule_axiom false tri s)
  | [< 'Ident "elim";
       tri = parse_trivial_opts false;
       l,n = parse_into 1;
       e = parse_expr ?? serror "an expression" tstr;
       w = parse_with >] ->
      (* e type_checked by rule_elim *)
      let opt = test_opt l w in
      !auto_lvl, "elim", (rule_elim false tri false false false opt n e)
| [< 'Ident "resolve" >] ->
    let meth = match tstr with parser
      [< 'Ident meth >] -> meth
    | [< >] -> "n"
    in
    !auto_lvl, "resolve", rule_resolve meth
| [< 'Ident "lclaim" >] ->
    !auto_lvl, "lclaim", rule_claim
| [< 'Ident "by_absurd" >] ->
    !auto_lvl, "by_absurd", rule_absurd
| [< 'Ident "by_contradiction" >] ->
      !auto_lvl, "by_contradiction", rule_contradiction
  | [< 'Ident "apply";
       tri = parse_trivial_opts false;
       s = parse_option "";
       l,n = parse_into 1;
       e = parse_expr ?? serror "an expression" tstr;
       w = parse_with >] ->
      (* e type_checked by rule_elim *)
      let opt = test_opt l w in
      !auto_lvl, "apply", (rule_apply tri s opt n e)
  | [< 'Ident "left";
       tri = parse_trivial_opts false;
       'Ident hypname ?? serror "an identfier" tstr;
       opt = parse_inta >] ->
      !auto_lvl, "left", (rule_left tri hypname opt None)
  | [< 'Ident "lefts";
       tri = parse_trivial_opts false;
       'Ident hypname ?? serror "an identfier" tstr;
       opt = parse_ints >] ->
      !auto_lvl, "lefts", (rule_left tri hypname opt None)
  | [< 'Ident "from";
       tri = parse_trivial_opts false;
       e = parse_expr ?? serror "an expression" tstr >] ->
      (* e type_checked by rule_elim *)
      !auto_lvl, "from", (rule_elim false tri false false true [] 0 e)
  | [< 'Ident ("rewrite" | "unfold" as s);
       tri = parse_trivial_opts false;
       opt, b0, b1 = parse_rewrite_opt;
       l = parse_rewrite_list b0 b1 >] ->
      !auto_lvl, s, (rule_rewrite tri l opt (s = "unfold") true)
  | [< 'Ident ("rewrite_hyp" | "unfold_hyp" as s);
       'Ident hypname;
       tri = parse_trivial_opts false;
       opt, b0, b1 = parse_rewrite_opt;
       l = parse_rewrite_list b0 b1 >] ->
      !auto_lvl, s, (rule_rewrite_hyp tri l hypname opt (s = "unfold_hyp") true)
  | [< 'Ident "evaluate";
       opt = parse_evaluate_opt;
       tri = parse_trivial_opts false >] ->
      !auto_lvl, "evaluate", (rule_rewrite tri [true, false, sym_get "eval"] opt false false)
  | [< 'Ident "evaluate_hyp";
       'Ident hypname;
       opt = parse_evaluate_opt;
       tri = parse_trivial_opts false >] ->
      !auto_lvl, "evaluate", (rule_rewrite_hyp tri [true, false, sym_get "eval"] hypname opt false false)
  | [< 'Ident "idt" >] ->
      !auto_lvl, "idt", (fun gl st -> [gl, st], [])

let rec parse_next_tactic (auto_lvl1, name1, rl1 as rl) tstr =
  match tstr with parser
  | [< 'Kwd "@|@"; (auto_lvl2, name2, rl2) = parse_tactic >] ->
      max auto_lvl1 auto_lvl2,
      (name1 ^" @|@ "^name2),
      orelse_rule rl1 rl2
  | [< 'Kwd ";;"; (auto_lvl2, name2, rls) = parse_dispatch_list >] ->
      max auto_lvl1 auto_lvl2,
      (name1 ^" ;; "^name2),
      dispatch_rule rl1 rls
(*
  | [< 'Kwd ";;"; (auto_lvl2, name2, rl2) = parse_tactic >] ->
	max auto_lvl1 auto_lvl2,
	(name1 ^" ;; "^name2),
	compose_rule rl1 rl2
*)
    | [< >] -> rl

and parse_dispatch_list tstr =
  match tstr with parser
  | [< (auto_lvl1, name1, rl1) = parse_tactic; (auto_lvl2, name2, rls) = parse_dispatch_list' >] ->
      max auto_lvl1 auto_lvl2,
      (name1 ^" @+@ "^name2),
      rl1::rls

and parse_dispatch_list' tstr =
  match tstr with parser
  | [< 'Kwd "@+@"; r = parse_dispatch_list >] -> r
  | [< >] -> !auto_lvl, "", []

and parse_tactic tstr =
  match tstr with parser
    | [< rl = parse_one_tactic; rl' = parse_next_tactic rl >] -> rl'
    | [< 'Ident "Try"; (auto_lvl1, name1, rl1) = parse_tactic>] ->
	auto_lvl1,
	("Try "^name1),
	try_rule rl1
    | [< 'Lpar; rl = parse_tactic;
	 'Rpar ?? serror ")" tstr ; rl' = parse_next_tactic rl >] ->
	rl'
    | [< ncmd = parse_newcmd false >] ->
        !auto_lvl, "newcmd", interpret_newcmd ncmd


let parse_cmd cstrm tstr = (try match tstr with parser
(* commande globale *)
  [< 'Dot >] ->
       ()
| [< 'Ident "quit"; 'Dot ?? terror Dot tstr >] ->
        raise Quit
| [< 'Ident "restart"; 'Dot ?? terror Dot tstr >] ->
        raise Restart
| [< 'Ident "flag"; 'Ident s ?? serror "an identifier" tstr;
     v = parse_value ?? serror "aflag value" tstr;
    'Dot ?? terror Dot tstr >] ->
        set_flag s v
| [< 'Ident "end"; 'Dot ?? terror Dot tstr >] ->
    raise End_of_module
| [< 'Eof >] ->
    raise End_of_file
| [< 'Tex(docs,cstr) >] ->
    if !compiling then do_tex docs cstr else comment cstr
| [< 'Ident "tex" when not !compiling; str >] ->
    parse_tex_header str
| [< 'Ident "include";
     'Str s ?? serror "a string" tstr;
     'Dot ?? terror Dot tstr >] ->
    read_file s
| [< 'Ident "add_path";
     'Str s ?? serror "a string" tstr;
     'Dot ?? terror Dot tstr >] ->
    add_path s
| [< 'Ident "path";
     'Dot ?? terror Dot tstr >] ->
    print_path ()
| [< 'Ident "del";
      s = parse_sym ?? serror "a symbol" tstr;
      'Dot ?? terror Dot tstr >] ->
        test_del (); rec_remove false !the_base (sym_get s)
| [< 'Ident "del_proof";
      s = parse_sym ?? serror "a symbol" tstr;
      'Dot ?? terror Dot tstr >] ->
        make_claim s
| [< 'Ident "edel";
      'Ident s ?? serror "an identifier" tstr;
      ss = parse_sym ?? serror "a symbol" tstr;
      'Dot ?? terror Dot tstr >] ->
        test_del (); delete_special s (sym_get ss)
(* Commande liee aux modules *)
| [< 'Ident "Import";
     'Ident intf_name ?? serror "an identifier" tstr;
     'Dot ?? terror Dot tstr >] ->
        import_intf intf_name
| [< 'Ident "Use";
     _, l = parse_options "Use" ["n"];
     'Ident intf_name ?? serror "an identifier" tstr;
     ren = parse_renaming;
     'Dot ?? terror Dot tstr >] ->
        use_intf (l<>[]) intf_name ren
(* commande de definition *)
| [< 'Ident "Sort"; name, arity, v = parse_sort; 'Dot ?? terror Dot tstr >] ->
    let _ =
      add_sym name Unknown v Trivial false true Idtren (Some arity)
    in ()
| [< 'Ident "Cst";
     s,sy,_ = parse_syntax_def false ?? serror "a syntax definition" tstr;
     'Kwd ":" ?? serror ":" tstr;
     k = parse_kind ?? serror "a kind" tstr;
     'Dot ?? terror Dot tstr >] ->
    let _ = add_sym s k Cst sy false true Idtren None in ()
(* commande de preuves globales (pas des tactiques) *)
| [< 'Ident "instance";
     e1 = parse_atomexpr ?? serror "an expression" tstr;
     e2 = parse_expr ?? serror "an expression" tstr;
     'Dot ?? terror Dot tstr >] ->
    let _ = do_instance !auto_lvl e1 e2 in ()
| [< 'Ident "lock";
     'Uid n ?? serror "an existential variables" tstr;
     'Dot ?? terror Dot tstr >] ->
    add_to_nomatch n
| [< 'Ident "unlock";
     'Uid n ?? serror "an existential variables" tstr;
     'Dot ?? terror Dot tstr >] ->
    remove_from_nomatch true n
| [< 'Ident "next";
     n = parse_intd 0;
     'Dot ?? terror Dot tstr >] ->
        do_next n
| [< 'Ident "after";
     n = parse_intd 1;
     'Dot ?? terror Dot tstr >] ->
        do_next (n - 1)
| [< 'Ident "select";
     'Num n;
     'Dot ?? terror Dot tstr >] ->
        do_next (1 - Num.int_of_num n)
| [< 'Ident "undo";
     nb = parse_intd 1;
     'Dot ?? terror Dot tstr >] ->
        do_undo_cmds nb
| [< 'Ident "abort";
     'Dot ?? terror Dot tstr >] ->
        do_abort ()
| [< 'Ident "goals";
      'Dot ?? terror Dot tstr >] ->
        do_goals ()
(* commande liee a l'extraction de programme *)
| [< 'Ident "compile";
     'Ident s ?? serror "an identifier" tstr;
     'Dot ?? terror Dot tstr >] ->
       (try
	 let o = sym_get s in
	 let _ = compile o in ()
       with Not_found ->
	 raise (Gen_error ("Unbound identifier: \""^ s ^"\"")))
| [< 'Ident "ttrans";
     l = parse_sym ?? serror "an identifier" tstr;
     a = parse_sym ?? serror "an identifier" tstr;
     'Ident s ?? serror "an identifier" tstr;
     'Dot ?? terror Dot tstr >] ->
       (try
	 let lam = sym_get l in
	 let app = sym_get a in
	 let o = sym_get s in
	 let _  = translate lam app o in ()
       with Not_found ->
	 raise (Gen_error ("Unbound identifier: \""^ s ^"\"")))
| [< 'Ident "output";
    order, opts = parse_options "output" ["kvm"];
    l = parse_ident_list ;
    'Dot ?? terror Dot tstr >]
	 -> outputs  ~kvm:(List.mem "kvm" opts) l
| [< 'Ident "eval";
     order, opts = parse_options "eval" ["kvm"];
     t = parse_lambda;
     'Dot ?? terror Dot tstr >] ->
    if List.mem "kvm" opts
    then print_kvm_term (eval t)
    else print_term (eval t)
| [< 'Ident "tdef";
     'Ident s;
     'Kwd "=";
     t = parse_lambda;
     'Dot ?? terror Dot tstr >] ->
    add_def s t
| [< 'Ident "tdel";
     l = parse_ident_list ;
     'Dot ?? terror Dot tstr >] ->
    del_defs l
(* commande d'affichage *)
| [< 'Ident "depend";
     arg = parse_depend_opt;
     s = parse_ident ?? serror "an identifier" tstr;
     'Dot ?? terror Dot tstr >] ->
        do_depend arg s
| [< 'Ident "priority";
      l = parse_symlist;
      'Dot ?? terror Dot tstr >] ->
        do_prior l
| [< 'Ident "objsearch";
     'Str s ?? serror "a string" tstr;
     k = parse_kindd; 'Dot ?? terror Dot tstr >] ->
        do_search s k
| [< 'Ident "print_sort"; e = parse_expr ?? serror "an expression" tstr;
    'Dot ?? terror Dot tstr >] ->
    do_print print_expr_sorted e
| [< 'Ident "eshow";
     'Ident s ?? serror "an identifier" tstr;
     'Dot ?? terror Dot tstr >] ->
        show_special s
| [< 'Ident "constraints";
     'Dot ?? terror Dot tstr >] ->
        print_ctx ()
| [< 'Ident "print"; e = parse_expr ?? serror "an expression" tstr;
    'Dot ?? terror Dot tstr >] ->
    do_print print_expr e
| [< 'Ident "validate"; _ = parse_free_expr ?? serror "an expression" tstr;
    'Dot ?? terror Dot tstr >] ->
      print_string "OK";
      print_newline ();
| [< 'Ident "print_proof"; s = parse_sym;
     'Dot ?? terror Dot tstr >] ->
    print_proof s
| [< 'Ident "is_hypothesis"; 'Num n; 'Str s;
     'Dot ?? terror Dot tstr >] ->
    is_hypothesis (Num.int_of_num n) s
| [< 'Ident "is_definition"; 'Num n; 'Str s;
     'Dot ?? terror Dot tstr >] ->
    is_definition (Num.int_of_num n) s
| [< 'Ident "is_equation"; 'Num n; 'Str s;
     'Dot ?? terror Dot tstr >] ->
    is_equation (Num.int_of_num n) s
| [< 'Ident "is_locked" >] ->
    begin match tstr with parser
      [< 'Uid n; 'Dot ?? terror Dot tstr >] ->
	is_locked n
    | [< 'Unid n; 'Dot ?? terror Dot tstr >] ->
	is_locked (get_uvar_by_name n)
    end
| [< 'Ident "menu_intro"; 'Num n; l = parse_string_list;
     'Dot ?? terror Dot tstr >] ->
    ignore (menu_intro (Num.int_of_num n) l)
| [< 'Ident "menu_evaluate"; 'Num n;
     'Dot ?? terror Dot tstr >] ->
    ignore (menu_evaluate (Num.int_of_num n))
| [< 'Ident "menu_evaluate_hyp"; 'Num n; 'Ident s;
     'Dot ?? terror Dot tstr >] ->
    ignore (menu_evaluate_hyp (Num.int_of_num n) s)
| [< 'Ident "menu_left"; 'Num n; 'Ident s;
     'Dot ?? terror Dot tstr >] ->
    ignore (menu_left s (Num.int_of_num n))
| [< 'Ident "menu_elim"; 'Num n; 'Ident s;
     'Dot ?? terror Dot tstr >] ->
    ignore (menu_elim s (Num.int_of_num n))
| [< 'Ident "menu_apply"; 'Num n; 'Ident s; l = parse_string_list;
     'Dot ?? terror Dot tstr >] ->
    ignore (menu_apply s l (Num.int_of_num n))
| [< 'Ident "menu_rewrite_hyp"; 'Num n; 'Ident s; l = parse_string_list;
     'Dot ?? terror Dot tstr >] ->
    ignore (menu_rewrite_hyp s l (Num.int_of_num n))
| [< 'Ident "menu_rewrite"; 'Num n; l = parse_string_list;
     'Dot ?? terror Dot tstr >] ->
    ignore (menu_rewrite  l (Num.int_of_num n))
| [< 'Ident "test_rule_intro";
     e = parse_expr ?? serror "an expression" tstr;
     'Dot ?? terror Dot tstr>] ->
       let rules = AL.get_rules () e false in
       let fn (str,w,subst,c,cl) =
	 print_string str; print_string " "; print_int w; print_string " : ";
	 List.iter (fun e -> print_expr e; print_string " ; ") cl;
	 print_newline ()
       in
       List.iter fn rules;
       print_string "end";
       print_newline ();
| [< 'Ident "test_rule_elim";
     e = parse_expr ?? serror "an expression" tstr;
     'Dot ?? terror Dot tstr>] ->
       let rules = AL.get_rules () e true in
       let fn (str,w,subst,c,cl) =
	 print_string str; print_string " "; print_int w; print_string " : ";
	 List.iter (fun e -> print_expr e; print_string " ; ") cl;
	 print_newline ()
       in
       List.iter fn rules;
       print_string "end";
       print_newline ();
| [< 'Ident "verbose_resol"; 'Num n;
      'Dot ?? terror Dot tstr>] ->
	Ptypes.verbose :=  Num.int_of_num n
(*
| [< 'Ident "hilbert" >] ->
    match tstr with parser
      [< 'Ident "norm2"; e = parse_expr ?? serror "an expression" tstr;
	 'Dot ?? terror Dot tstr >] ->
	   print_float (Hilbert.norm2 (Hilbert.term_to_vector e));
	   print_newline ();
    | [< 'Ident "distance2"; e = parse_expr ?? serror "an expression" tstr;
	 'Ident "with" ; e' = parse_expr ?? serror "an expression" tstr;
	 'Dot ?? terror Dot tstr >] ->
	   print_float (Hilbert.distance2 (Hilbert.term_to_vector e) (Hilbert.term_to_vector e'));
	   print_newline ();
    | [< 'Ident "angle"; e = parse_expr ?? serror "an expression" tstr;
	 'Ident "with" ; e' = parse_expr ?? serror "an expression" tstr;
	 'Ident "and" ; e'' = parse_expr ?? serror "an expression" tstr;
	 'Dot ?? terror Dot tstr >] ->
	   print_float (Hilbert.angle (Hilbert.term_to_vector e) (Hilbert.term_to_vector e') (Hilbert.term_to_vector e''));
	   print_newline ();
*)
(* command acceptant le prefix Local *)
| [< 'Ident "Local"; fn = parse_export false;
     'Dot ?? terror Dot tstr >] -> fn ()
| [< fn = parse_export true;
     'Dot ?? terror Dot tstr >] -> fn ()
(* tactique *)
| [< gn = parse_goal_number; auto_lvl, name, rule = parse_tactic;
     'Dot ?? terror Dot tstr >] ->
    let _ = do_rule auto_lvl name gn rule in ()
with
    Illegal_char c ->
      let _ = Stream.next tstr in
      open_hbox ();
      print_string "Syntax Error: Illegal char \"";
      print_string (Char.escaped c);
      print_string "\"."; print_newline ();
      raise Error
  | Stream.Failure ->
      let _ = Stream.next tstr in
      reset_lexer cstrm;
      print_endline "Syntax Error: Parse_failure ??";
      raise Error
  | Stream.Error s ->
      let _ = Stream.next tstr in
      reset_lexer cstrm;
      open_hbox ();
      print_string "Syntax Error: ";
      print_string (if s = "" then "??" else s);
      print_newline ();
      raise Error
  | Unbound s ->
      let _ = Stream.next tstr in
      reset_lexer cstrm;
      open_hbox ();
      print_string "Syntax Error: Unbound identifier: \"";
      print_string (String.escaped s);print_string "\"";
      print_newline ();
      raise Error
  | Base_failure s ->
      open_hbox ();
      print_string "Error: ";
      print_string s;print_newline ();
      raise Error
  | Illegal_bind s ->
      open_hbox ();
      print_string "Syntax Error: Illegal binder: \"";
      print_string (String.escaped s);print_string "\"";
      print_newline ();
      raise Error
  | Not_def s ->
      open_hbox ();
      print_string "Syntax Error: Symbol not defined: \"";
      print_string (String.escaped s);print_string "\"";
      print_newline ();
      raise Error
  | Invalid_kwd s ->
      open_hbox ();
      print_string "Syntax Error: Invalid keyword: \"";
      print_string (String.escaped s);print_string "\"";
      print_newline ();
      raise Error
  | Cant_bind (s::_) ->
      open_hbox ();
      print_string "Syntax Error: Unbound identifier: \"";
      print_string (String.escaped s);print_string "\"";
      print_newline ();
      raise Error
  | Dup_arg s ->
      open_hbox ();
      print_string "Syntax Error: Duplicate identifier: \"";
      print_string (String.escaped s);print_string "\"";
      print_newline ();
      raise Error
  | Gen_error s ->
      open_hbox ();
      print_string "Error: ";
      print_string s; print_newline ();
      raise Error
  | Not_normal ->
      print_endline "Error: Not normal";
      raise Error
  | Fail_matching->
      print_endline "Error: Fail match";
      raise Error
  | Bad_proof n ->
      open_hbox ();
      print_string "Error: Bad proof type ";
      print_int n;
      print_newline ();
      raise Error
  | Wrong_path ->
      print_endline "Error: Wrong path";
      raise Error
  | Not_found ->
      print_endline "Not_found";
      raise Error
  | Ill_rule s ->
      open_hbox ();
      print_string "Error: Proof error: ";
      print_string s; print_newline();raise Error
  | Efun_error s ->
      open_hbox ();
      print_string "Error: Program exception: ";
      print_string s; print_newline();raise Error
); flush stdout
