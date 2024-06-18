(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.13 $ *)
(*######################################################*)
(*			parser.ml			*)
(*######################################################*)

open Stream
open Lex
open Type
open Type.Base
open Basic
open Local
open Lambda_util
open Typing
open Flags
open Print

exception Syntax_error
exception Unbound of string
exception Illegal_bind of string
exception Not_def of string
exception Invalid_kwd of string
exception Cant_bind of string list
exception Dup_arg of string

(* parse an expression *)

let sget str = match Stream.peek str with
  Some t -> t
| None -> Eof

let serror s str =
  "Waiting for " ^ s ^ ", but got " ^ (string_of_token (sget str)) ^ "."

let terror t str =
  "Waiting for " ^ (string_of_token t) ^ " but got " ^
  (string_of_token (sget str)) ^ "."

let stream_check f s =
  match Stream.peek s with
    None -> raise Stream.Failure
  | Some x -> if f x then Stream.next s else raise Stream.Failure

let get_kvar,reset_kvar,get_kname =
  let ptr = ref ([]:(string * kind) list) in
  (fun s -> try List.assoc s !ptr with Not_found -> let k = mk_Var () in
            ptr:=(s,k)::!ptr; k),
  (fun () -> ptr:=[]),
  (fun k -> cossa k !ptr)


let is_kind = function
  Ident s ->
    (try
       match get_value (sym_get s) with
	 KCst | KDef _ -> true
       | _ -> false
     with Not_found -> true)
  | _ -> false

let parse_kind_ident s =
  match (stream_check is_kind s) with
    Ident str -> str
  | _ ->  failwith "bug in parse_kind_ident"

let rec parse_kind_atom str = match str with parser
  [< s = parse_kind_ident >] ->
    (try
       let o = sym_get s in
       let l = parse_kind_args (is_poly o) str in
       KAtom (o, l)
    with Not_found -> raise (Unbound s))
| [< 'Kid s >] -> get_kvar s
| [< 'Lpar;
     t = parse_kind_aux ?? serror "a kind" str ;
     'Rpar ?? terror Rpar str >] -> t

and parse_kind_args n str =
  if n = 0 then [] else
  match str with parser
    [< 'Kwd "[";
       k = parse_kind_aux;
       l = parse_kind_argl (n-1);
       'Kwd "]" ?? serror "]" str >] -> k::l

and parse_kind_argl n str =
  if n = 0 then [] else
  match str with parser
    [<  'Kwd ","; k = parse_kind_aux; l = parse_kind_argl (n-1) >] -> k::l

and parse_kind_aux = parser
  [< t = parse_kind_aux2; t' = parse_kind_suit t >] -> t'

and parse_kind_suit t str = match str with parser
  [< 'Kwd "->";
     t' = parse_kind_aux2 ?? serror "a kind" str ;
     t'' = parse_kind_suit t' >] ->
       KArrow(t,t'')
| [< >] -> t

and parse_kind_aux2 = parser
  [< t = parse_kind_atom; t' = parse_kind_suit2 t >] -> t'

and parse_kind_suit2 t str = match str with parser
  [< 'Kwd "*";
     t' = parse_kind_atom ?? serror "a kind" str ;
     t'' = parse_kind_suit2 t' >] ->
       KAtom(sym_get "product",[t;t''])
| [< >] -> t

let parse_kind s = let k = parse_kind_aux s in reset_kvar (); k

type isass =
  Noass
| Ass of kind
| IAss of expr

let set_proof_mode, not_proof_mode, get_goal =
  let not_proof = (function n ->
    failwith ("Can't acces goal $" ^ string_of_int n ^ ": not in proof mode."))
  in
  let parse_goal = ref not_proof in
  (function f -> parse_goal := f),
  (function () -> parse_goal := not_proof),
  (function n -> !parse_goal n)

let reserved = ["with"; "and"; "then"; "let"; "show"; "assume"; "deduce"; "trivial"; "by"; "named"; "begin"; "end";"match"; "of"; "function"; "unknown"; "discover"]

let is_ident = function
  Ident s ->
  (try if (get_syntax (sym_get s)) = Trivial then true else false
   with Not_found -> not (List.mem s reserved))
| _ -> false

let parse_ident s =
  match (stream_check is_ident s) with
    Ident str -> str
  | _ ->  failwith "bug in parse_ident"

let rec parse_ass_ident = parser
  [< s = parse_ident; t = parse_type_sass >] -> s,t

and  parse_type_sass tstr = match tstr with parser
  [< 'Kwd ":<"; t = parse_kind_aux ?? serror "a kind" tstr >] -> t
| [< >] -> mk_Var ()

let last_obj = ref dummy_obj

let is_prefix =
let f s =
  try
    let o = (sym_get s) in
    last_obj := o;
    let sy = get_syntax o in (
    match sy with
      Prefix _ -> true
    | _ -> false)
  with Not_found -> false
in function
  Ident s -> f s
| Kwd s -> f s
| _ -> false

let is_infix ll lr =
  let f s =
    try
      let o = (sym_get s) in
      last_obj := o;
      let sy = get_syntax o in (
          match sy with
            Infix (ll',lr',_,_,_,_) -> (level_leq lr' lr) && (level_leq ll ll')
          | _ -> false)
    with Not_found -> false
  in function
    Ident s -> f s
  | Kwd s -> f s
  | _ -> false

let sy_prefix =
let f _ =
    let sy = get_syntax !last_obj in
    match sy with
      Prefix (sy,perm) -> (sy,!last_obj,perm)
    | _ -> (failwith "bug in sy_prefix")
in function
  Ident s -> f s
| Kwd s -> f s
| _ -> (failwith "bug in sy_prefix")

let sy_infix =
let f _ =
    let sy = get_syntax !last_obj in
    match sy with
      Infix (_,lr,sy,perm,_,_) -> (sy,!last_obj,lr,perm)
    | _ -> (failwith "bug in sy_prefix")
in function
  Ident s -> f s
| Kwd s -> f s
| _ -> (failwith "bug in sy_prefix")

let bind_ident str = match str with parser
  [< 'Ident s >] -> s
| [< 'Joker "" >] -> "_"

type psyn =
  PBind of (string list) * (int * coma * semi) * isass
| PArg of expr

let fPBind (a1,a2,a3) = PBind (a1,a2,a3)

let apply_tperm p l = match p with
  Idtperm -> l
| Perm(_,p2) -> apply_perm p2 l

let cur_env = ref 0

let inlet = ref false

let rec parse_prefix s =
  let tok = stream_check (is_prefix) s in
  let (sy,o,perm) = sy_prefix tok in
  build_prefix o perm (do_bind o (parse_syntax sy s))

and parse_infix lt ll lr s =
  let tok  = stream_check (is_infix ll lr) s in
  let (sy,o,lr,perm) = sy_infix tok in
  (build_prefix o perm (do_bind o ((PArg lt)::(parse_syntax sy s)))), lr

and parse_infix_bind lt s =
  let tok  = stream_check (is_infix min_level max_level) s in
  let (sy,o,_,perm) = sy_infix tok in
  (build_prefix o perm (do_bind o ((PArg lt)::(parse_syntax_bind sy s))))

and parse_syntax sy s = match sy with
  (Bind (a1,a2,a3))::sy ->
    let a = (fPBind (parse_bind (a1,a2,a3) s)) in a::(parse_syntax sy s)
| (Arg lvl)::sy -> let a = (PArg (parse_aux lvl s)) in a::(parse_syntax sy s)
| (Key str)::sy -> (parse_key str s); (parse_syntax sy s)
| (IKey str)::sy -> (parse_ikey str s); (parse_syntax sy s)
| (Space _)::sy -> parse_syntax sy s
| [] -> []

and parse_syntax_bind sy s = match sy with
  (Bind (a1,a2,a3))::sy ->
    let a = (fPBind (parse_bind (a1,a2,a3) s)) in
      a::(parse_syntax_bind sy s)
| [Arg _] -> [PArg (parse_atom s)]
| (Arg lvl)::sy -> let a = (PArg (parse_aux lvl s)) in
    a::(parse_syntax_bind sy s)
| (Key str)::sy -> (parse_key str s); (parse_syntax_bind sy s)
| (IKey str)::sy -> (parse_ikey str s); (parse_syntax_bind sy s)
| (Space _)::sy -> parse_syntax_bind sy s
| [] -> []

and parse_ikey str = parser
  [< 'Ident str' when str = str' >] -> ()
| [< tstr >] -> raise (Stream.Error (serror str tstr))

and parse_key str = parser
  [< 'Kwd str' when str = str' >] -> ()
| [< tstr >] -> raise (Stream.Error (serror str tstr))

and parse_coma coma =
  if coma = Nocoma then raise Stream.Failure else parser
  [< 'Kwd "," >] -> ()

and parse_semi semi =
  if semi = Nosemi then raise Stream.Failure else parser
  [< 'Kwd ":" >] -> ()

and parse_semii semi =
  if semi = Nosemi then raise Stream.Failure else parser
  [< t = (if !inlet then
    fun st -> fst (parse_infix (EVar 0) min_level max_level st) else
    parse_infix_bind (EVar 0)) >] -> t

and parse_type_ass (_,coma,semi as l) str tstr = match tstr with parser
  [< 'Kwd ":<";
     t = parse_kind_aux ?? serror "a kind" tstr >] -> str, Ass t
| [< _ = parse_coma coma;
     s = bind_ident ?? serror "an identifier or \"_\"" tstr;
     r = parse_type_ass l (s::str) >] ->
  if coma = Nocoma then raise Stream.Failure else r
| [< _ = parse_semi semi;
     t = parse_atom ?? serror "an expression" tstr >] ->
      str, IAss t
| [< t = parse_semii semi >] ->
      str, IAss (EAbs("infix_bind",t,mk_Var ()))
| [< >] -> str,Noass

and parse_type_lass str tstr = match tstr with parser
  [< 'Kwd ":<"; t = parse_kind_aux  ?? serror "a kind" tstr >] -> str, Ass t
| [< 'Kwd ","; s = bind_ident ?? serror "an identifier or \"_\"" tstr;
     r = parse_type_lass (s::str)>] -> r
| [< >] -> str,Noass

and parse_bind l = parser
  [< str = bind_ident; strl,a = parse_type_ass l [str] >] -> strl,l,a
| [< tstr >] -> raise (Stream.Error (serror "an identifier" tstr))

and do_bind the_binder l =
  let rec f l = function
    [] -> l
  | PArg _::pl -> f l pl
  | PBind (s,bl,k)::pl -> f (g k s bl 1 l) pl
  and g k s ((p,co,se) as bl) n = function
    [] -> []
  | (PBind _)::pl -> g k s bl n pl
  | (PArg e) as b::pl ->
    if n = p then (
        let tk =  match k with
          Noass | IAss _  -> mk_Var
        | Ass k ->  fun _ -> k in
    let rec fn e = function
      [] -> (failwith "bug in do_bind (parser)")
    | [s] -> let e = match k,se with
                Noass, _ | (Ass _),_-> e
             | IAss f, Semi g -> norm_expr (EApp(EApp(texpr_copy g,EApp(f, FVar s)),e))
             | _,_ -> raise (Stream.Error "") in
             EAbs(s,e,tk ())
    | s::l -> match co with
         Nocoma -> raise (Stream.Error "")
      |  Coma f ->
           let e = match k,se with
             Noass, _ | (Ass _),_-> e
           | IAss f, Semi g ->
                 norm_expr (EApp(EApp(texpr_copy g,EApp(texpr_copy f, FVar s)),e))
           | _,_ -> raise (Stream.Error "") in
           fn (norm_expr (EApp (EApp(texpr_copy f,aobj the_binder),
               EAbs(s,e,tk ())))) l
    in
    let t = fn e s in (PArg t)::pl)
    else b::(g k s bl (n + 1) pl)
  in f l l

and is_normal = ref true

and is_abs = function
  EAbs _ -> is_normal := false
| _ -> ()

and build_app e e' =
  is_abs e;
  EApp (e,e')

and build_prefix o perm l =
  let rec g = function
    [] -> []
  | (PBind _)::l -> g l
  | (PArg e')::l -> e':: g l
  in
  let rec f e = function
    [] -> e
  | e'::l -> f (build_app e e') l
  in f (aobj o) (apply_tperm perm (g l))

and parse_aux lr = parser
  [< t = parse_atom; t' = parse_app t;
     t'' = parse_infix_suit t' min_level lr >] -> t''
| [< tstr >] -> raise (Stream.Error (serror "an expression" tstr))

and treat_pattern stack stack_term tstr  =
  match stack, stack_term with
    [], [] -> EAbs("_fail", parse_right_member tstr, mk_Var ())
  | (k::stack as all), (e::stack_term) ->
      begin
	let get_case o _ =
	  let s = "case_" ^ get_name o in
	  let e = aobj (sym_get s) in
	  let k0 = get_safe_kind o in
	  let rec fn = function
	      KArrow(k,k') -> k::fn k'
	    | _ -> []
	  in
	  e, fn k0
	in
	match e with
	  EApp(e1, e2) -> treat_pattern all (e1::e2::stack_term) tstr
	| EAtom(o,_) ->
	    let e,l = get_case o k in
	    let e' = treat_pattern (l@stack) stack_term tstr in
	    EApp(e,e')
	| FVar s ->
	    begin try
	      let o = sym_get s in
	      let e,l = get_case o k in
	      let e' = treat_pattern (l@stack) stack_term tstr in
	      EApp(e,e')
	    with Not_found ->
	      let e' = treat_pattern stack stack_term tstr in
	      EAbs("_fail",EAbs(s, EApp(e',EApp(EVar 1,EVar 0)), k), mk_Var ())
	    end
	| _ ->
	    raise (Stream.Error ("Syntax error in match "))

      end
  | _ -> assert false

and parse_right_member tstr = match tstr with parser
  [< 'Kwd "->"; e = parse_aux max_level >] -> e

and parse_match tstr = match tstr with parser
  [< e = parse_aux max_level; 'Ident "with"; e' = parse_patmatch (mk_Var ());  >] ->
    EApp(EApp(aobj (sym_get "start_match"), e'),e)

and parse_function tstr = match tstr with parser
  [< e = parse_patmatch (mk_Var ()) >] ->
    EApp(aobj (sym_get "start_match"), e)

and in_left_member = ref false

and parse_aux_match _ str =
  in_left_member := true;
  try
    let r = parse_aux 5.0 str in
    in_left_member := false;
    r
  with e ->
    in_left_member := false;
    raise e

and parse_patmatch k tstr = match tstr with parser
  [< e = parse_aux_match 5.0; r = treat_pattern [k] [e];
     r' = parse_nextmatch k >] ->
       EApp(r,r')

and parse_nextmatch k tstr = match tstr with parser
  [< 'Kwd "|"; e' = parse_patmatch k >] -> e'
| [< >] ->
    aobj (sym_get "undef")

and parse_atom tstr = match tstr with parser
  [< lt = parse_prefix >] ->  lt
| [< 'Kwd "\\"; s = bind_ident ?? serror "an identifier or \"_\"" tstr;
     sl,k = parse_type_lass [s];
     t = parse_atom ?? serror "an expression" tstr>] ->
        let k = match k with Noass | IAss _ -> mk_Var () | Ass k -> k in
        List.fold_left (fun t s -> EAbs (s,t,kind_copy k)) t sl
| [< 'Ident "match"; e = parse_match >] -> e
| [< 'Ident ("function" | "fun"); e = parse_function >] ->  e
| [< s = parse_ident >] -> FVar s
| [< 'Joker "" >] ->
    if not !in_left_member then raise (Stream.Error "Illegal \"_\"");
    FVar "_"
| [< 'Num n >] -> EData(Data.EInt n)
| [< 'Str s >] -> EData(Data.EString s)
| [< 'Dol; 'tok; tstr >] -> (match tok with
        Ident s -> (try let o = sym_get s in aobj o
                    with Not_found -> raise (Not_def s))
      | Kwd s -> (try let o = sym_get s in aobj o
                  with Not_found -> raise (Not_def s))
      | Num _ -> get_goal !cur_env
      | Dol -> (match tstr with parser
          [< 'Ident s >] ->
                (try let o = sym_get s in
                   match get_value o with
                     Cst -> aobj o
                   | Def e -> e
                   | _ -> raise Not_found
                 with Not_found -> raise (Not_def s))
        | [< 'Kwd s >] ->
                (try let o = sym_get s in
                   match get_value o with
                     Cst -> aobj o
                   | Def e -> e
                   | _ -> raise Not_found
                 with Not_found -> raise (Not_def s))
        | [< 'tok >] ->
                raise (Stream.Error ("Wait for a symbol after $$, but got " ^
                             (string_of_token tok))))
      | _ -> raise (Stream.Error ("Wait for a symbol after $, but got " ^
                                (string_of_token tok))))
| [< 'Lpar;
     lt = parse_aux max_level ?? serror "an expression" tstr;
     'Rpar ?? serror ")" tstr >] -> lt
| [< 'Uid n >] -> new_ivar n
| [< 'Unid n >] -> new_ivar (get_uvar_by_name n)

and parse_infix_suit lt ll lr = parser
  [< lt',ll' = parse_infix lt ll lr; t = parse_infix_suit lt' ll' lr >] -> t
| [< >] -> lt

and parse_app t0 = parser
  [< t = parse_atom;  t' = parse_app (build_app t0 t)>] -> t'
| [< >] -> t0


and bind_free tex n l e =
  let rec fn n l = function
    UVar (p,_) as e -> (try fn n l (getuvar p)
                       with Not_found -> e)
  | EApp (e1,e2) -> EApp (fn n l e1, fn n l e2)
  | EAbs (s,e,k) -> EAbs (s, fn (n + 1) ((s,(n + 1))::l) e,k)
  | FVar s -> (try EVar (n - (List.assoc s l))
                   with Not_found ->
                   try find_local s
                   with Not_found ->
                   try let o = sym_get s in aobj o
                   with Not_found ->
                   if tex then begin
                     try List.assoc s !tex_local with Not_found ->
                     let k = mk_Var () in
                     let v =
                       {fkind = KBVar 0; fvalue = Cst; syntax = Free;
                        poly = 1; exported = false; origin = Idtren} in
                     let o = capsule_object s v 0 in
                     let e = EAtom(o, [k]) in
                     tex_local := (s,e)::!tex_local; e
                   end else raise (Unbound s))
  | e -> e
  in fn n l e

let parse_expr s =
  is_normal := true;
  let e = bind_free false 0 [] (parse_aux max_level s)
  in reset_kvar (); if !is_normal then e else
      let _ = type_check e in norm_expr e

let parse_free_expr s =
  is_normal := true;
  let e = parse_aux max_level s in
  reset_kvar (); if !is_normal then e else
  norm_expr e

let parse_tex_expr end_tok s =
  is_normal := true;
  let e = bind_free true 0 [] (parse_aux max_level s) in
  (match s with parser
    [< 'Kwd s when s = end_tok >] -> ()
  | [< str >] -> raise (Stream.Error (serror end_tok str)));
    let _ = type_check e in
  reset_kvar ();
  if !is_normal then e else (norm_expr e)

let parse_atomexpr s =
  is_normal := true;
  let e = bind_free false 0 [] (parse_atom s)
  in reset_kvar (); if !is_normal then e else
      let _ = type_check e in norm_expr e

let parse_bound_expr l s =
  is_normal := true;
  let e = parse_aux max_level s in
  let rec f e = function
    [] -> e
  | (s,k)::l -> EAbs(s,f e l, k) in
  let e = bind_free false 0 [] (f e l) in
  reset_kvar ();
  let _ = type_check e in
  if !is_normal then e else norm_expr e

let parse_bound_atomexpr l s =
  let e = parse_atom s in
  let rec f e = function
    [] -> e
  | s::l -> EAbs(s,f e l, mk_Var ()) in
  let e = bind_free false 0 [] (f e l)
  in reset_kvar (); if !is_normal then e else
      let _ = type_check e in norm_expr e


type sy_def =
  SKwd of string
| SIKwd of string
| SBind of string * int ref * coma * semi
| SArg of string * kind
| SSpace of string * string

type fixity = Left | Right | Nofix

let rec parse_ident_list = parser
  [< s = parse_ident; l = parse_ident_list >] -> s :: l
| [< >] -> []

let rec get_arg_list = function
  [] -> []
| SArg (s,_) :: l -> s :: get_arg_list l
| _ :: l -> get_arg_list l

let build_perm l1 l2 =
  let pos s l =
    let rec fn p = function
      [] -> raise Not_found
    | s'::_ when s = s' -> p
    | _::l -> fn (p + 1) l
    in fn 0 l
  in
  let build l1 l2 =
    let rec fn = function
      [] -> []
    | s::l -> pos s l2::fn l
    in fn l1
  in
  try
    let p1 = build l1 l2 and p2 = build l2 l1 in
    let rec fn p acc = function
      [] -> acc
    | _::l -> fn (p+1) (p::acc) l in
    let l = fn 0 [] p1 in
    if apply_perm p1 (apply_perm p2 l) <> l ||
       apply_perm p2 (apply_perm p1 l) <> l then
    raise (Stream.Error "invalid permutation");
    Perm (p1,p2)
  with Not_found ->
    raise (Stream.Error "invalid permutation")

let check_space _ lvl sy =
  let default_bind = space_of_int !binder_tex_space in
  let default_indent = space_of_int !tex_indent in
  let default =
    let a = float (!min_tex_space) and
        b = float (!max_tex_space - !min_tex_space) in
    let space = (a +. (b *. lvl /. 10.0)) /. 100.0 in
      (string_of_float space)^"em" in
  let sort = function
      SArg _ -> 2
    | SBind _ -> 1
    | _ -> 0 in
  let rec fn bf = function
      [] -> []
    | (SSpace(spb,spa))::sy ->
        (SSpace(spb,spa))::(fn (-1) sy)
    | x::sy ->
	let af = sort x in
        let mf = max af bf in
	if bf = -1 || af = -1 || mf = 0 then
	  x::(fn af sy)
	else if mf <= 1 then
	  (SSpace(default_bind,""))::x::(fn af sy)
	else if af <= 1 then
          (SSpace(default,""))::x::(fn af sy)
	else
	  (SSpace(default, default_indent))::x::(fn af sy)
  in fn (-1) sy

let rec parse_syntax_def b tstr = in_tex_def := b; match tstr with parser
  [< 'Ident "Infix"; lr = parse_lvl max_level;
       (a,b) = parse_ass_ident ?? serror "an identifier" tstr;
       sp = parse_mbspace;
       sn,s = parse_kwd ?? serror "a string" tstr;
       sy = parse_syn;
       perm = parse_perm sn (a::get_arg_list sy) >]
    -> build_syntax perm true Nofix lr ((SArg (a,b))::(cons_option sp (s::sy)))
| [< 'Ident "lInfix"; lr = parse_lvl max_level;
       (a,b) = parse_ass_ident ?? serror "an identifier" tstr;
       sp = parse_mbspace;
       sn,s = parse_kwd ?? serror "a string" tstr;
       sy = parse_syn;
       perm = parse_perm sn (a::get_arg_list sy) >]
    -> build_syntax perm true Left lr ((SArg (a,b))::(cons_option sp (s::sy)))
| [< 'Ident "rInfix"; lr = parse_lvl max_level;
       (a,b) = parse_ass_ident ?? serror "an identifier" tstr;
       sp = parse_mbspace;
       sn,s = parse_kwd ?? serror "a string" tstr;
       sy = parse_syn;
       perm = parse_perm sn (a::get_arg_list sy) >]
    -> build_syntax perm true Right lr ((SArg (a,b))::(cons_option sp (s::sy)))
| [< 'Ident "Postfix"; lr = parse_lvl max_level;
       (a,b) = parse_ass_ident ?? serror "an identifier" tstr;
       _,s = parse_kwd ?? serror "a string" tstr >]
    -> build_syntax Idtperm true Left lr [(SArg (a,b));s]
| [< 'Ident "Prefix"; lr = parse_lvl max_level;
       sn,s = parse_kwd ?? serror "a string" tstr;
       sy = parse_syn;
       perm = parse_perm sn (get_arg_list sy) >]
    -> build_syntax perm false Right lr (s::sy)
| [< s = parse_ident; l = parse_args >] -> (s, Trivial, l)

and build_syntax perm infix fix lr sy =
  let lr = if fix = Left then delta' lr else lr in
  let rec f = function
    [] -> []
  | (SArg (s,c))::l -> let l' = f l in
    if List.mem_assoc s l' then raise (Dup_arg s) else (s,c)::l'
  | _::l -> f l
  in
  let la = f sy in
  let rec g lb n = function
    [] -> raise Not_found
  | (SArg (s,_))::l -> if s = lb then n
                   else g lb (n+1) l
  | _::l -> g lb n l
  in
  let rec h = function
    [] -> ()
  | (SBind (sl, p, _, _))::l ->
          (try p:= g sl 1 sy; h l
          with Not_found -> raise (Cant_bind [sl]))
  | _::l -> h l
  in
  h sy;
  let rec k = function
    [] -> []
  | (SBind (_,lb,co,se))::l -> (Bind (!lb,co,se))::(k l)
  | (SArg _)::l ->
      let lvl =
        if l = [] then
          if fix = Right then lr else delta lr
        else
          max_level
      in (Arg lvl)::(k l)
  | (SKwd s)::l -> (Key s)::(k l)
  | (SIKwd s)::l -> (IKey s)::(k l)
  | (SSpace(spb,spa))::l -> (Space(spb,spa))::(k l)
  in
  let sy = check_space infix lr sy in
  let la = match perm with
    Idtperm -> la
  | Perm (_,p2) -> apply_perm p2 la in
  if infix then
    let lvl = if fix = Left then lr else delta lr
    in match sy with
      (SArg _)::(SSpace (spb,spa))::(SKwd s)::sy ->
	(s, Infix(lvl,lr,k sy,perm,spb,spa), la)
    | (SArg _)::(SSpace (spb,spa))::(SIKwd s)::sy ->
	(s, Infix(lvl,lr,k sy,perm,spb,spa), la)
    | _ -> (failwith "bug in build_syntax")
  else
    match sy with
      (SKwd s)::sy -> (s, Prefix(k sy,perm), la)
    | (SIKwd s)::sy -> (s, Prefix(k sy,perm), la)
    | _ -> (failwith "bug in build_syntax")

and parse_args = parser
  [< s = parse_ass_ident; l = parse_args>] -> s::l
| [< >] -> []

and fl_int = parser
  [< 'Float lvl >] -> lvl
| [< 'Num lvl >] -> Num.float_of_num lvl

and parse_lvl dflt tstr = match tstr with parser
  [< 'Kwd "[";
     lvl = fl_int ?? serror "a number" tstr;
     'Kwd "]" ?? serror "]" tstr >] -> lvl
| [< >] -> dflt

and parse_binder tstr = match tstr with parser
  [< 'Kwd "\\";
     s = bind_ident ?? serror "an identifier or \"_\"" tstr;
     co,se = parse_bargs;
     'Kwd "\\" ?? serror "\\" tstr >] -> s,co,se

and parse_bargs tstr = match tstr with parser
  [< 'Kwd ",";
     co = parse_atomexpr ?? serror "an expression" tstr;
     se = parse_seargs >] -> Coma co,se
| [< 'Kwd ":";
     se = parse_atomexpr ?? serror "an expression" tstr;
     co = parse_coargs >] -> co,Semi se
| [< >] -> Nocoma, Nosemi

and parse_coargs tstr = match tstr with parser
  [< 'Kwd ","; co = parse_atomexpr ?? serror "an expression" tstr>] -> Coma co
| [< >] -> Nocoma

and parse_seargs tstr = match tstr with parser
  [< 'Kwd ":"; se = parse_atomexpr ?? serror "an expression" tstr>] -> Semi se
| [< >] -> Nosemi

and parse_perm _ il tstr = match tstr with parser
  [< 'Kwd "%"; 'Ident "as" ?? serror "%as" tstr;
     'Dol ?? serror ("$xxx") tstr;
     _ = (parser
           [< 'Ident _ >] -> ()
         | [< 'Kwd _ >] -> ()
         ) ?? serror ("$xxx") tstr;
     l = parse_ident_list >] -> build_perm il l
| [< >] -> Idtperm

and in_tex_def = ref false

and parse_kwd = parser
  [< 'Str s >] -> try
    if !in_tex_def then (s, SKwd s) else (
    let cstr = Stream.of_string s in
    let str = stream_map next_token cstr in
    let r = match str with parser
      [< 'Ident s >] -> (s, SIKwd s)
    | [< 'Kwd s >] -> (s, SKwd s)
    | [< >] -> raise (Invalid_kwd s) in
    empty cstr; r)
    with Stream.Failure ->  raise (Invalid_kwd s)

and parse_space =
  parser
    [< 'Kwd "!" >] -> SSpace("0em","")
      | [< 'Kwd "<"; 'Num spb; str >] ->
	  match str with parser
	      [< 'Num spa; 'Kwd ">" >] ->
		SSpace(space_of_num spb,space_of_num spa)
	    | [< 'Kwd ">" >] ->
		SSpace(space_of_num spb,"")

and parse_mbspace = parser
  [< sp = parse_space >] -> Some sp
| [< >] -> None

and parse_syn = parser
  [< b,c = parse_ass_ident; sy = parse_syn >] -> (SArg (b,c))::sy
| [< l,co,se = parse_binder; sy = parse_syn >] -> (SBind (l, ref 0,co, se))::sy
| [< _,k = parse_kwd; sy = parse_syn >] -> k::sy
| [< sp = parse_space; sy = parse_syn >] -> sp::sy
| [< >] -> []

let syntax_of_string b s =
  let cstrm = Stream.of_string s in
  let strm = stream_map next_token cstrm in
  let (s,sy,_) = parse_syntax_def b strm in
  s, sy

let expr_of_string s =
  let cstrm = Stream.of_string s in
  let strm = stream_map next_token cstrm in
  parse_expr strm

let rec parse_renaming str =
  let default = ref "" in
  let local = ref [] in
  let general = ref [] in
  let from = ref [] in
  let rec fn tstr = match tstr with parser
    [< 'Joker "";
       'Kwd "->" ?? serror "->" tstr;
       'Joker s when s <> "" ?? serror "a _.xxx" tstr >] ->
      if !default <> "" then
        failwith "Two suffixes specified in one renaming.";
      default:= "." ^ s; gn str
  | [< 'Ident "from"; 'Ident s ?? serror "an identifier" tstr;
       ren = parse_renaming; 'Dot ?? terror Dot tstr  >] ->
      from := (s, ren)::!from; gn str
  | [< 'Joker s ;
       'Kwd "->" ?? serror "->" tstr;
       'Joker s' ?? serror "a _.xxx" tstr >] ->
       general := (s,s')::!general; gn str
  | [< 'Kwd s; ' Kwd "->" ?? serror "->" tstr;
       (s', sy) = parser [< 'Joker "" >] -> ("", Trivial)
                       | [< (s', sy, _) = parse_syntax_def false >] -> s', sy
                     ?? serror "a syntax definition" tstr >] ->
      local:=(s,(s',sy))::!local; gn str
  | [< 'Ident s; ' Kwd "->" ?? serror "->" tstr;
       (s', sy) = parser [< 'Joker "" >] -> ("", Trivial)
                       | [< (s', sy, _) = parse_syntax_def false >] -> s', sy
                     ?? serror "a syntax definition" tstr >] ->
      local:=(s,(s',sy))::!local; gn str

  and gn = parser
    [< 'Kwd "|"; _ = fn >] -> ()
  | [< >] -> ()
  in

  (match str with parser
    [< 'Ident "with"; _ = fn >] -> ()
  | [< >] -> ());
  let cmp = fun (s,_) (s',_) -> if s < s' then -1 else 1 in
  let local = List.sort cmp !local in
  let general = List.sort cmp !general in
  let from = List.sort cmp !from in
  Used (
   {default = !default; rlocal = local; general = general; from = from},
   Idtren)

let rec parse_kind_vargl str =
  match str with parser
      [<  'Kwd ",";
	  'Kid s;
	  l = parse_kind_vargl >] ->
	(get_kvar s)::l
    | [<>] -> []

let parse_kind_vargs str =
  match str with parser
    [< 'Kwd "["; 'Kid s; l = parse_kind_vargl;
       'Kwd "]" ?? serror "]" str >] ->
      (get_kvar s)::l

let parse_sort_aux name str = match str with parser
    [< 'Num n >] -> name, Num.int_of_num n, KCst
  | [< 'Kwd "="; k = parse_kind >] ->
      let lk = ref (0, []) in
      let k = generalize_kind lk k in
      let n = List.length (snd !lk) in
      if n <> 0 then failwith "Parameter not bound in sort";
      name, 0, KDef k
  | [< l = parse_kind_vargs; str >] -> (
      match str with parser
	  [<'Kwd "="; k = parse_kind >] ->
	    let lk = ref (0, []) in
	    let _ = List.iter
		      (fun v ->
			 let _ = generalize_kind lk v in ())
		      l
	    in
	    let n = List.length l in
	    let k = generalize_kind lk k in
	    let n' = List.length (snd !lk) in
	    if n' <> n then failwith "Parameter not bound in sort";
	    name, n, KDef k
	| [< >] ->
	    let n = List.length l in
	    name, n, KCst)
  | [< >] -> name, 0, KCst

let parse_sort str = match str with parser
    [< name = parse_ident >] -> parse_sort_aux name str
