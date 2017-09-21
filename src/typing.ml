(* $State: Exp $ $Date: 2006/02/24 17:01:54 $ $Revision: 1.7 $ *)
(*######################################################*)
(*			typing.ml			*)
(*######################################################*)

open Format
open Types
open Data_base
open Basic
open Local
open Print
open Lambda_util
open Typunif
open Undo

let subst_obj_kind lk o =
  let k = get_kind o in
  if is_poly o > 0 then
    kind_subst lk k
  else k

let ksym_get s =
  try
    let o = sym_get s in
    KAtom(o,[])
  with
    Not_found -> failwith "bug in ksym_get"

let rec tcheck t l lv =  function 
  EVar i as e -> unify e lv (List.nth l i) t
| EData (Data.EInt _) as e -> unify e lv (ksym_get "num") t
| EData (Data.EString _) as e ->  unify e lv (ksym_get "string") t
| FVar _ -> raise (Failure "bug in type_check")
| UVar (_,k) as e -> unify e lv k t
| UCst (_,k) as e -> unify e lv k t
| Path (path,e) -> 
    let gn (l,lv as c) = function 
      PAbs (s,k) -> (k::l),(s::lv)
    | _ -> c in
    let l,lv = List.fold_left gn (l,lv) path in
    tcheck t l lv e
| Syntax s as e -> unify e lv (ksym_get "syntax") t
| EAtom (o,lk) as e -> unify e lv (subst_obj_kind lk o)  t
| EApp (e1,e2) -> 
    let v = mk_Var () in
    tcheck (KArrow (v,t)) l lv e1;
    tcheck v l lv e2
| EAbs (s,e,k) as e' ->
    let w = mk_Var () in
    unify e' lv (KArrow(k,w)) t;
    tcheck w (k::l) (s::lv) e

let rec fast_type_infer l e =  
  match e with
    EVar i -> List.nth l i 
  | EData (Data.EInt _) -> ksym_get "num"
  | EData (Data.EString _) ->  ksym_get "string"
  | Syntax s ->  ksym_get "syntax"
  | UVar (n,k) -> k
  | UCst (_,k) -> k
  | EAtom (o,lk) -> subst_obj_kind lk o
  | EApp (e1,e2) -> 
      begin
	try
	  let k = fast_type_infer l e1 in
	  let _, v = filter_arrow k in
	  v
	with Clash -> failwith "bug in fast_type_infer"
      end
  | EAbs (s,e,k) ->
      let k' = fast_type_infer (k::l) e in
      KArrow(k,k')
  | _ -> raise (Failure "fast_type_infer")
      
let xcheck e t = 
  let pos = get_undo_pos () in
  try
    tcheck t [] [] e;
    t
  with 
    Type_Clash (e,t,t',lv) ->
      open_hovbox 0;
      print_string "Typing Error: Can not use expression";
      print_break 1 2;
      print_expr_env lv e;
      print_break 1 2;
      print_string "of type";
      print_break 1 2;
      print_kind t; 
      print_break 1 2;
      print_endline "with type";
      print_break 1 2;
      print_kind t'; 
      print_newline ();
      do_undo pos;
      raise Error

(* inferes the type of an expression *)

let rec type_check e = xcheck e (mk_Var ())

let rec type_strong e k = let _ = xcheck e k in ()

type generalize_env = (int * (kind ref * kind) list) ref

let generalize_kind lk k = 
  let rec f t = match norm t with
      KBVar _ | Unknown -> assert false
    | KArrow(k, k') -> KArrow(f k, f k')
    | KAtom (a,l) -> KAtom(a, List.map f l)
    | KVar ptr ->
	let num, lt = !lk in
	try
	  List.assq ptr lt
	with Not_found ->
	  let t = KBVar(num) in
	  lk := (num+1, (ptr, t)::lt);
	  t
  in f k
	   
let generalize_path lk path =
  let rec g = function
      PAbs(s, k) -> PAbs(s, generalize_kind lk k) 
    | c -> c
  in List.map g path

let generalize_expr lk e =
  let rec g = function
    EApp (t,t') -> EApp(g t, g t')
  | EAbs (s,t,k) -> EAbs(s,g t, generalize_kind lk k)
  | Path (path,e) -> Path(generalize_path lk path, g e)
  | EAtom(o,k) -> EAtom(o, List.map (generalize_kind lk) k)
  | UVar (n,k) -> UVar(n, generalize_kind lk k)
  | UCst (n,k) -> UCst(n, generalize_kind lk k)
  | e -> e
  in g e

let kind_inst o lk = 
  let poly = is_poly o in
  let v = (Data_base.Object.get_value o).fvalue in
  match v with
    Def t -> if poly > 0 then kind_subst_expr lk t else t
  | Prg t -> if poly > 0 then kind_subst_expr lk t else t
  | _ -> raise Not_found

let rec get_inst = function
  EAtom(o,lk) as e -> 
    (match get_value o with
      Cst | Fun _ -> e
    | Def _ -> get_inst (kind_inst o lk)
    | Prg _ -> get_inst (kind_inst o lk)
    | _ -> raise (Failure "bug in get_inst"))
| UVar (n,_) as e -> (try get_inst (getuvar n) with Not_found -> e)
| e -> e


let build_subterm oe lk l = 
  let rec fn acc = function
      [] -> acc
    | t::l -> fn (EApp(acc,lift t)) l
  in
  let k = subst_obj_kind lk oe in
    k, EAbs("x",fn (EVar 0) l,k)

