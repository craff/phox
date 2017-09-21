(* $State: Exp $ $Date: 2006/02/24 17:01:54 $ $Revision: 1.6 $ *)
(*######################################################*)
(*			typunif.ml			*)
(*######################################################*)

open Format
open List
open Basic
open Types
open Data_base
open Undo

exception Clash
exception Type_Clash of expr * kind * kind * string list

(* manipulation of kind *)

let rec norm = function
  KVar {contents = Unknown} as t ->
    t
| KVar ({contents = v} as ptr) ->
    let t = norm v in
    if not (t == v) then update ptr t; 
    t
| t -> t


let kind_subst largs t =
  let rec f t = match norm t with
    KVar ptr as t -> t
  | KBVar n -> List.nth largs n
  | KAtom (_,[]) as t -> t
  | KAtom (n,l) -> KAtom(n, List.map f l)
  | KArrow (t1,t2) -> KArrow (f t1, f t2)
  | Unknown -> Unknown
  in f t

let rec norm2 = function
  KVar {contents = Unknown} as t ->
    t
| KVar ({contents = v} as ptr) ->
    let t = norm2 v in
    if not (t == v) then update ptr t; 
    t
| (KAtom (a,l)) as t ->
    begin
      match (Data_base.Object.get_value a).fvalue with
	KDef k -> norm2 (kind_subst l k) 
      | _ -> t
    end
| t -> t

(* unification of two kind *)

let test_occur ptr t =
  let rec f t = match norm t with
  | KAtom (_,l) -> List.iter f l
  | KArrow (t1,t2) -> f t1; f t2
  | KVar ptr' when ptr == ptr' -> raise Clash
  | _ -> ()
  in f t


let rec kind_subst_expr largs =  function 
  EVar i as e -> e
| EData _ as e -> e
| FVar _ -> raise (Failure "bug in kind_subst_expr")
| UVar (_,k) -> raise (Failure "bug in kind_subst_expr")
| UCst (_,k) -> raise (Failure "bug in kind_subst_expr")
| Path (path,e) -> 
    let gn = function 
      PAbs (s,k) -> PAbs (s,kind_subst largs k)
    | c -> c in
    Path(List.map gn path, kind_subst_expr largs e)
| Syntax s as e -> e
| EAtom (o,k) -> 
    EAtom(o, List.map (kind_subst largs) k)
| EApp (e1,e2) -> 
    EApp(kind_subst_expr largs e1, kind_subst_expr largs e2)
| EAbs (s,e,k) ->
    EAbs(s,kind_subst_expr largs e, kind_subst largs k)


let unif t1 t2 = 
  let rec fn t1 t2 = match norm t1, norm t2 with
      (KArrow (t1,t2)), (KArrow (t'1,t'2)) -> 
        fn t1 t'1;
	fn t2 t'2
    | (KAtom (a,l) as t1), (KAtom (a',l') as t2) ->
	let found_def = ref false in
	let t1' = 
	  match (Data_base.Object.get_value a).fvalue with
	    KDef k -> found_def := true; kind_subst l k
	  | _ -> t1
	in
	let t2' = 
	  match (Data_base.Object.get_value a').fvalue with
	    KDef k -> found_def := true; kind_subst l' k
	  | _ -> t2
	in
	if !found_def then
	  fn t1' t2'
	else if a == a' then
	  List.iter2 fn l l' 
	else 
	  raise Clash
    | KBVar(n), KBVar(n') when n = n' -> ()
    | (KVar x), (KVar x') when x == x'-> ()
    | (KVar ptr), t -> test_occur ptr t; update ptr t
    | t, (KVar ptr) -> test_occur ptr t; update ptr t
    | (KAtom (a,l)), t2 ->
	begin
	  match (Data_base.Object.get_value a).fvalue with
	    KDef k -> fn (kind_subst l k) t2
	  | _ -> raise Clash
	end
    | t1, (KAtom (a,l))->
	begin
	  match (Data_base.Object.get_value a).fvalue with
	    KDef k -> fn t1 (kind_subst l k)
	  | _ -> raise Clash
	end
    | _ -> raise Clash  
  in
  let pos = get_undo_pos () in  
  try 
    fn t1 t2 
  with e ->
    do_undo pos; raise e

let rec filter_arrow t =
  match norm2 t with
    KArrow(t, t') -> t, t'
  | KVar ptr ->
      let v = mk_Var () and v' = mk_Var () in
      update ptr (KArrow(v,v'));
      v, v'
  | _ -> raise Clash  

let equal_kind t t' =
  try 
    unif t t';
    true
  with
    Clash -> 
      false

let unify e lv t t' = 
  try 
    unif t t'
  with Clash -> 
    raise (Type_Clash (e,t,t',lv))

