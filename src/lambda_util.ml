(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $ReVision: 1.6 $ *)
(*######################################################*)
(*			lambda_util.ml			*)
(*######################################################*)

open Format
open Data_base.Object
open Types.Base
open Types
open List
open Basic
open Cache
open Local
open Typunif
open Undo

exception Free_match
exception Wrong_path


(* functions use for parsing only *)

let rec last_lvl = function
  [] -> max_level
| [Arg lvl] -> lvl
| _::l -> last_lvl l

let bind s e k =
  let rec f n = function
    EVar _ as e -> e
  | EAtom _ as e -> e
  | EApp (e1,e2) -> let e1 = f n e1 in let e2 = f n e2 in EApp (e1, e2)
  | EAbs (s,e,k) -> EAbs (s, f (n + 1) e,k)
  | FVar s' as e -> if s = s' then EVar n else e
  | Path (path,e) -> Path(path,f (n + path_count path) e)
  | UVar (p,_) as e -> (try f n (getuvar p) with Not_found -> e)
  | e -> e
  in EAbs (s,f 0 e,k)


let bind_cst s p e k =
  let rec f n = function
    EApp (e1,e2) -> EApp (f n e1, f n e2)
  | EAbs (s,e,k) -> EAbs (s, f (n + 1) e,k)
  | Path (path,e) -> Path(path,f (n + path_count path) e)
  | UVar (p,_) as e -> (try f n (getuvar p) with Not_found -> e)
  | UCst (q,_) as e -> if p = q then EVar n else e
  | FVar _  -> raise (Failure "bug in bind")
  | e -> e
  in EAbs (s,f 0 e,k)

let subst_cst p e t =
  let rec f = function
    EApp (e1,e2) -> EApp (f e1, f e2)
  | EAbs (s,e,k) -> EAbs (s, f e,k)
  | Path (path,e) -> Path(path,f e)
  | UVar (p,_) as e -> (try f (getuvar p) with Not_found -> e)
  | UCst (q,_) as e -> if p = q then t else e
  | FVar _  -> raise (Failure "bug in bind")
  | e -> e
  in f e

let bind_atom s o e k =
  let found = ref false in
  let rec f n = function
    EApp (e1,e2) -> EApp (f n e1, f n e2)
  | EAbs (s,e,k) -> EAbs (s, f (n + 1) e,k)
  | Path (path,e) -> Path(path,f (n + path_count path) e)
  | UVar (p,_) as e -> (try f n (getuvar p) with Not_found -> e)
  | EAtom (o',_) as e -> if o == o' then (found:=true; EVar n) else e
  | e  -> e
  in let e = f 0 e in
  if !found then EAbs (s,e,k) else raise Not_found

let evaluable k =
 let rec fn b t = match (norm t) with
   KAtom (n,l) ->
     List.for_all (fn b) l
 | KArrow (t,t') ->
     fn (not b) t && fn b t'
 | _ -> false
 in fn true k

let kind_expr_copy, expr_copy, kind_copy, texpr_copy  =
  let ls = ref [] in
  let rec f t = match norm t with
    KVar ptr  ->
      begin
	try List.assq ptr !ls
	with
	  Not_found ->
	    let t' = mk_Var() in
	    ls := (ptr,t')::!ls; t'
      end
  | KAtom (n,l) -> KAtom(n, List.map f l)
  | KArrow (t1,t2) -> KArrow (f t1,f t2)
  | t -> t
  and g e = match e with
    EAtom (o,k) -> EAtom(o, List.map f k)
  | EApp (t,t') -> EApp(g t,g t')
  | EAbs (s,t,k) -> EAbs(s,g t,f k)
  | UVar (n,_) as e -> (try g (getuvar n) with Not_found -> e)
  | Path (l,e) -> Path (kp l, g e)
  | e -> e
  and h = function
    Def v -> Def (g v)
  | Prg v -> Prg (g v)
  | KDef k -> KDef (f k)
  | v -> v
  and kp = function
    [] -> []
  | (PAbs (s,k))::l -> (PAbs(s,f k))::(kp l)
  | x::l -> x::(kp l)
  in
    (fun (t,k) -> ls:=[];(h t, f k)),
    (fun t -> ls:=[];h t),
    (fun k -> ls:=[];f k),
    (fun k -> ls:=[];g k)

let get_kind o =
  let v = Data_base.Object.get_value o in
  v.fkind

let get_safe_kind o =
  let v = Data_base.Object.get_value o in
  if v.poly > 0 then
    let args = make_args v.poly in
    kind_subst args v.fkind
  else
    v.fkind

let get_value o =
  let v = Data_base.Object.get_value o in
  if v.poly > 0 then
    match v.fvalue with
	Def t -> Def (kind_subst_expr (make_args v.poly) t)
      | Prg t -> Prg (kind_subst_expr (make_args v.poly) t)
      | v -> v
  else
    v.fvalue

let generalize_for_rules o e1 e2 =
  let v = Data_base.Object.get_value o in
  if v.poly > 0 then
    let args = make_args v.poly in
    EAtom(o, args), kind_subst_expr args e1, kind_subst_expr args e2
  else
    EAtom(o, []), e1, e2

let generalize_for_equation (pos, e1, e2, nl, k, sy, eqtl as eq) =
  let poly =
    List.fold_left (fun max (eqt, p, c, d, b ,e) ->
		      match eqt with
			Eq_theo o ->
			  let v = Data_base.Object.get_value o in
			  if v.poly > max then v.poly else max
		      | _ -> max) 0 eqtl
  in
  if poly > 0 then (
    let args = make_args poly in
    let e1 = kind_subst_expr args e1 in
    let e2 = kind_subst_expr args e2 in
    let k = kind_subst args k in
    (pos, e1, e2, nl, k, sy, eqtl))
  else
    eq

let generalize_for_equations = List.map generalize_for_equation

let get_kind_value o =
  let v = Data_base.Object.get_value o in
  if v.poly > 0 then
    let args = make_args v.poly in
    (match v.fvalue with
	Def t -> Def (kind_subst_expr (make_args v.poly) t)
      | Prg t -> Prg (kind_subst_expr (make_args v.poly) t)
      | v -> v),
    kind_subst args v.fkind
  else
    (v.fvalue,v.fkind)

let rec term_size = function
    EApp (e1,e2) -> term_size e1 + term_size e2
  | EAbs (s,e,k) -> term_size e
  | Path (path,e) -> term_size e
  | UVar (p,_) -> (try term_size (getuvar p) with Not_found -> 1)
  | _  -> 1

let fis_close = ref (fun _ -> raise Not_found)

let rec term_size_rec e =
  let rec fn = function
    EApp (e1,e2) ->
      let n = fn e1 in
      n + term_size_rec e2
  | EAbs (s,e,k) -> term_size_rec e
  | Path (path,e) -> term_size_rec e
  | UVar (p,_) -> (try term_size_rec (getuvar p) with Not_found -> raise Exit)
  | EAtom (o,_) -> (match get_value o with
      Def e -> if !fis_close o || is_recursive o then 1 else term_size_rec e
    | Prg e -> term_size_rec e
    | _ -> 1)
  | _  -> 1
  in
  try fn e with Exit -> 1

type env_cell =
  A of expr * env * int
| B of int
and env = env_cell list
type stack = (expr * env * int) list

let lift t =
  let rec g n = function
    EApp (t,t') -> EApp(g n t, g n t')
  | EAbs (s,t,k) -> EAbs(s,g (n+1) t,k)
  | EVar p as e -> if p >= n then EVar (p+1) else e
  | UVar (p,_) as e -> (try g n (getuvar p) with Not_found -> e)
  | Path (path,e) -> Path(path,g (n+path_count path) e)
  | e -> e
  in g 0 t

let mlift k t =
  let rec g n = function
    EApp (t,t') -> EApp(g n t, g n t')
  | EAbs (s,t,k) -> EAbs(s,g (n+1) t,k)
  | EVar p as e -> if p >= n then EVar (p+k) else e
  | UVar (p,_) as e -> (try g n (getuvar p) with Not_found -> e)
  | Path (path,e) -> Path(path,g (n+path_count path) e)
  | e -> e
  in g 0 t

let unlift t =
  let rec g n = function
    EApp (t,t') -> EApp(g n t, g n t')
  | EAbs (s,t,k) -> EAbs(s,g (n+1) t,k)
  | EVar p as e -> if p > n then EVar (p-1) else
                   if p = n then raise Exit else e
  | UVar (p,_) as e -> (try g n (getuvar p) with Not_found -> e)
  | Path (path,e) -> Path(path,g (n+path_count path) e)
  | e -> e
  in g 0 t

let fun_lim = 100

exception Efun_error of string

let efun_table =
  Array.make fun_lim (fun _ -> failwith "Bug: efun not ready")

let add_fun =
  let cur = ref 0 in
  (fun f ->
     let i = !cur in
     if i >= fun_lim then failwith "efun_table too small";
     efun_table.(i) <- f;
     incr cur;
     Fun i)

let rec order t = match norm2 t with
  KArrow(k,k') -> max (1 + order k) (order k')
| _ -> 1

let norm_expr, norm_sexpr, norm_env_expr, norm_st_expr, norm_lexpr, norm_ldexpr, norm_lsexpr, subst_expr =
  let stack = ref [] and env = ref [] and depth = ref 0 and odepth = ref 0 in
  let open_def = ref (fun _ -> false) in
  let open_cst = ref (fun _ -> None) in
  let reset_open () = open_def := (fun _ -> false); open_cst := (fun _ -> None) in
  let getu = ref getuvar in
  let rec f did_red =  function
    EVar n -> (try match nth_try n !env with
      A (e,l,o) -> did_red := true; env:=l; odepth:= o;f did_red e
    | B n -> g did_red (EVar (!depth - n - 1)) !depth !stack
    with Not_found -> g did_red (EVar (n + !depth - !odepth)) !depth !stack)
  | EAtom(o,k) as e -> (
      match get_value o with
        Prg e -> did_red := true; f did_red e
      | Fun i ->
          let de = !depth and ode = !odepth and sa = !stack in
          let cont nstack nenv ndepth e =
            stack := nstack; env := nenv;
            depth := ndepth; odepth := ode;
            f did_red e in
          let ret nstack e =  g did_red e de nstack in
          (try let res = efun_table.(i) cont ret sa ode in did_red := true; res
           with Exit -> g did_red e de sa)
      | Def v when !open_def o ->
	  let ndid_red = ref false in
	  let sd = !depth and ss = !stack in
	  ignore (f ndid_red v);
	  if not !ndid_red then e else (did_red := true; g did_red e sd ss)
      | _ -> g did_red e !depth !stack)
  | EApp (t,t') -> stack:=(t',!env,!odepth)::!stack; f did_red t
  | EAbs (s,t,k) -> (odepth:=!odepth+1; match !stack with
      (ea,la,oa)::l -> did_red := true; env:=(A (ea,la,oa))::!env; stack:=l; f did_red t
    | [] -> env:=(B !depth)::!env; depth:=!depth+1; EAbs(s,f did_red t,k))
  | UCst (n,k) as e ->
      (match !open_cst n with
	None -> g did_red e !depth !stack
      | Some t -> did_red := true; f did_red t)
  | Path (path,e) -> (match !stack with
      [] -> let diff = path_count path in
            odepth:=!odepth+diff;
            let rec id = function
                0 -> ()
              | n -> env := (B !depth)::!env;
                  depth:=!depth+1; id (n-1) in
            id diff;
            Path (path,f did_red e)
    | _ -> raise (Failure "bug in normalisation : argument to path !"))
  | UVar (n,_) as e -> (try let res = f did_red (!getu n) in did_red := true; res
                       with Not_found -> g did_red e !depth !stack)
  | e -> g did_red e !depth !stack
  and g did_red e d = function
    [] -> e
  | (e',l,o)::ls -> stack:=[]; env:= l; depth:=d; odepth:=o;
       let e'' = f did_red e' in g did_red (EApp(e,e'')) d ls
  and f0 e =
    let did_red = ref false in
    let sd = !depth and ss = !stack in
    let res = f did_red e in
    if not !did_red then g did_red e sd ss else res
  in (fun e   -> getu:= getuvar;reset_open ();stack:=[];
                 env:=[];depth:=0;odepth:=0;f0 e),
     (fun e s -> getu:= getuvar;reset_open ();
	         stack:=List.map (fun x -> (x,[],0)) s;
                 env:=[];depth:=0;odepth:=0;reset_open ();f0 e),
     (fun e genv -> getu:= getuvar;reset_open (); stack:=[];
                 env:=List.map (fun x -> A(x,[],0)) genv;
                 depth:=0;odepth:=0;reset_open ();f0 e),
     (fun e s -> getu:= getuvar;reset_open ();
	         stack:=List.map (fun (x,_ (*:kind*)) -> (x,[],0)) s;
                 env:=[];depth:=0;odepth:=0;f0 e),
     (fun ma e -> getu:=(fun n -> Map.find n ma);reset_open ();
	         stack:=[];env:=[];depth:=0;odepth:=0;f0 e),
     (fun ma od oc e -> getu:=(fun n -> Map.find n ma);
                 open_def:=od; open_cst:=oc;
	         stack:=[];env:=[];depth:=0;odepth:=0;f0 e),
     (fun ma e s -> getu:=(fun n -> Map.find n ma);reset_open ();
	         stack:=List.map (fun x -> (x,[],0)) s;
                 env:=[];depth:=0;odepth:=0;f0 e),
     (fun ma e -> getu:=(fun n -> try List.assoc n ma with Not_found -> getuvar n);reset_open ();
	         stack:=[];env:=[];depth:=0;odepth:=0;f0 e)

let rec eta_red = function
  EAbs(_,e',_) as e ->
    let rec gn = function
      EApp(e'',EVar 0) -> (try unlift e'' with Exit -> e)
    | UVar (p,_) as e -> (try gn (getuvar p) with Not_found -> e)
    | _ -> e
    in gn (eta_red e')
| UVar (p,_) as e -> (try eta_red (getuvar p) with Not_found -> e)
| e -> e

let uniform result e1 e2 =
  let env = ref ([] : (int*int) list) in
  let max = ref (-1) in
  let rec fn = function
    EAtom (o,k) -> EAtom(o, k)
  | EApp (t,t') -> EApp(fn t,fn t')
  | EAbs (s,t,k) -> EAbs(s,fn t,k)
  | UVar (n,k) -> (try fn (Map.find n result) with Not_found ->
                   try UVar(List.assoc n !env,k) with Not_found ->
                   let n' = !max in max := !max-1;
                   env:=(n,n')::!env; UVar(n',k))
  | Path (path,e) -> Path(path,fn e)
  | e -> e
  in
     let t = fn e1 in
     let t' = fn e2 in
  (t,t')

let not_norm_info = ref (FVar "")

let not_norm_atom o t0 =
  match get_value o with
    Prg e -> not_norm_info := e; true
  | Fun e -> not_norm_info := t0; true
  | Def e -> not_norm_info := e; is_capsule o
  | _ -> false

let list_uvar t =
  let rec g acc stack = function
    EApp (t,t') ->
     g acc (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g acc [] (norm_sexpr t0 stack) else g acc [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g acc [] (norm_sexpr !not_norm_info stack)
  | UCst _ | Syntax _ | EVar _ | EAtom _ ->
     List.fold_left (fun x t -> g x [] t) acc stack
  | UVar (p,_)  -> (try g acc stack (getuvar p) with Not_found ->
     List.fold_left (fun x t -> g x [] t) (Set.add p acc) stack)
  | _ ->
     List.fold_left (fun x t -> g x [] t) acc stack
  in g Set.empty [] t

let list_ucst t =
  let rec g acc stack = function
    EApp (t,t') ->
     g acc (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g acc [] (norm_sexpr t0 stack) else g acc [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g acc [] (norm_sexpr !not_norm_info stack)
  | Syntax _ | EVar _ | EAtom _ ->
     List.fold_left (fun x t -> g x [] t) acc stack
  | UVar (p,_)  -> (try g acc stack (getuvar p) with Not_found ->
     List.fold_left (fun x t -> g x [] t) acc stack)
  | UCst (p,_) ->
     List.fold_left (fun x t -> g x [] t) (Set.add p acc) stack
  | _ ->
     List.fold_left (fun x t -> g x [] t) acc stack
  in g Set.empty [] t

let list_ucst' t =
  let rec g acc stack = function
    EApp (t,t') ->
     g acc (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g acc [] (norm_sexpr t0 stack) else g acc [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g acc [] (norm_sexpr !not_norm_info stack)
  | Syntax _ | EVar _ | EAtom _ ->
     List.fold_left (fun x t -> g x [] t) acc stack
  | UVar (p,_)  -> (try g acc stack (getuvar p) with Not_found ->
     List.fold_left (fun x t -> g x [] t) acc stack)
  | UCst (p,k) ->
     List.fold_left (fun x t -> g x [] t)
	(if List.mem_assoc p acc then acc else (p,k)::acc) stack
  | _ ->
     List.fold_left (fun x t -> g x [] t) acc stack
  in g [] [] t

let make_pattern e =
  let l = list_ucst' e in
  List.fold_left (fun e (n,k) -> bind_cst "x" n e k) e l

let saturate_pattern e =
  let rec fn = function
      EAbs(_,e,k) -> k::fn e
    | _ -> []
  in
  let rec gn e = function
      [] -> e
    | k::l -> gn (EApp(e,UVar(new_uvar(),k))) l
  in
  gn e (fn e)

let has_uvar subst t =
  let rec g stack = function
    EApp (t,t') ->
     g (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g [] (norm_sexpr t0 stack) else g [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g [] (norm_sexpr !not_norm_info stack)
  | UVar (p,_)  -> (try g stack (Map.find p subst) with Not_found -> true)
  | e ->
     List.exists (g []) stack
  in g [] t

let occur d t =
  let rec g stack = function
    EApp (t,t') ->
     g (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g [] (norm_sexpr t0 stack) else g [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g [] (norm_sexpr !not_norm_info stack)
  | UCst (n,_) -> n = d || List.exists (g []) stack
  | UVar (p,_)  ->
      (try g stack (getuvar p) with Not_found -> List.exists (g []) stack)
  | _ ->
     List.exists (g []) stack
  in g [] t

let occur_uvar d t =
  let rec g stack = function
    EApp (t,t') ->
     g (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g [] (norm_sexpr t0 stack) else g [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g [] (norm_sexpr !not_norm_info stack)
  | UCst (n,_) -> List.exists (g []) stack
  | UVar (p,_)  -> if p = d then true else
      (try g stack (getuvar p) with Not_found -> false)
  | _ ->
     List.exists (g []) stack
  in g [] t

let occur_evar t =
  let rec g depth stack = function
    EApp (t,t') ->
     g depth (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g depth [] (norm_sexpr t0 stack) else g (depth+1)  [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g depth [] (norm_sexpr !not_norm_info stack)
  | EVar n -> n = depth || List.exists (g depth []) stack
  | UVar (p,_)  ->
      (try g depth stack (getuvar p) with Not_found -> List.exists (g depth []) stack)
  | _ ->
     List.exists (g depth []) stack
  in g 0 [] t

let occur' d t =
  let rec g stack = function
    EApp (t,t') ->
     g (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g [] (norm_sexpr t0 stack) else g [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g [] (norm_sexpr !not_norm_info stack)
  | UCst (n,_) -> (
      n = d ||
      try g stack (let (e,_) = List.assoc n !cur_local.cst_eq in e)
      with Not_found -> List.exists (g []) stack)
  | UVar (p,_)  ->
      (try g stack (getuvar p) with Not_found -> List.exists (g []) stack)
  | _ ->
     List.exists (g []) stack
  in g [] t

let occur_set result s t =
  let rec g stack = function
    EApp (t,t') ->
     g (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g [] (norm_sexpr t0 stack) else g [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g [] (norm_sexpr !not_norm_info stack)
  | EAtom (o,_) -> Set.mem (2 * Data_base.Object.get_key o + 1) s
                    || List.exists (g []) stack
  | UCst (n,_) -> Set.mem (2*n) s || List.exists (g []) stack
  | UVar (p,_)  ->
      (try g stack (Map.find p result)
       with Not_found -> List.exists (g []) stack)
  | _ ->
     List.exists (g []) stack
  in g [] t

let depth_uvar subst t =
  let rec g d stack = function
    EApp (t,t') ->
     g d (t'::stack) t
  | EAbs (s,t,k) as t0 ->
     if stack <> [] then g d [] (norm_sexpr t0 stack) else g d [] t
  | EAtom (o,_) as t0 when not_norm_atom o t0 ->
      g d [] (norm_sexpr !not_norm_info stack)
  | UVar (p,_)  -> (try g d stack (Map.find p subst) with Not_found -> d)
  | _ ->
     List.fold_left (fun n x -> min n (g (d+1) [] x)) max_int stack
  in g 0 [] t

let rec linear_uvar t =
  let rec g n = function
    EAbs (s,t,k) -> g (n + 1) t
  | UVar (p,_) as e -> (try g n (getuvar p) with Not_found -> e,0)
  | e -> (e,n) in
  let e,n = g 0 (norm_expr t) in
  let rec f q = function
    EVar p -> (p - q >= 0) && (p - q < n)
  | EAtom (o,k) -> false
  | EApp (t,t') -> (f q  t) || (f q t')
  | EAbs (s,t,k) -> f (q + 1) t
  | Path (path,t) -> f (q + path_count path) t
  | UVar (p,_) -> (try f q (getuvar p) with Not_found -> false)
  | _ -> false in
  if n = 0 then true else f 0 e


let rec equal_path' p1 p2 = match p1,p2 with
  [], [] -> true
| (LApp::l), (LApp::l') -> equal_path' l l'
| (RApp::l), (RApp::l') -> equal_path' l l'
| ((PAbs (_,k))::l), ((PAbs (_,k'))::l') ->
    equal_kind k k' && equal_path' l l'
| _ -> false

let equal_path p1 p2 =
  let pos = get_undo_pos () in
  let r = equal_path' p1 p2 in
  if not r then do_undo pos;
  r

let equal_pos_eq h1 h2 = match h1, h2 with
  Oneq o1, Oneq o2 when o1 == o2 -> true
| Uneq n, Uneq p when n = p -> true
| Uveq, Uveq | Alleq, Alleq -> true
| _ -> false

(* compare expr upto alpha-eta equiv *)

let rec equal_expr' e1 e2 =
  match e1, e2 with
  (EVar n), (EVar m) -> n = m
| (UCst (n,_)), (UCst (m,_)) -> n = m
| (Path (path,e)), (Path (path',e')) -> equal_path' path path' && equal_expr' e e'
| (UVar (n,_) as t1), (UVar (m,_) as t2) ->
    (try equal_expr' (getuvar n) t2 with Not_found ->
    try equal_expr' t1 (getuvar m) with Not_found ->
    n = m)
| (UVar (n,_)), t2 ->
    (try equal_expr' (getuvar n) t2 with Not_found -> false)
| t1, (UVar (m,_)) ->
    (try equal_expr' t1 (getuvar m) with Not_found -> false)
| (EAtom (o,k)), (EAtom (o',k')) ->
    (o == o') && (List.for_all2 equal_kind k k')
| (EApp(t1,t2)), (EApp(t1',t2')) ->
    (equal_expr' t1 t1') && (equal_expr' t2 t2')
| (EAbs (_,t,k)), (EAbs (_,t',k')) -> (equal_kind k k') && (equal_expr' t t')
| (EAbs (_,t,_)), t' ->
    (equal_expr' t (EApp((lift t'),EVar 0)))
| t, (EAbs (_,t',_)) ->
    (equal_expr' (EApp((lift t),EVar 0)) t')
| EData d, EData d' -> Data.eq_data d d'
| _ -> false

let equal_expr e1 e2 =
  let pos = get_undo_pos () in
  let r = equal_expr' e1 e2 in
  if not r then do_undo pos;
  r

let rec equalv_expr' e1 e2 = match e1, e2 with
  (EVar n), (EVar m) -> n = m
| (UCst (n,_)), (UCst (m,_)) -> n = m
| (Path (path,e)), (Path (path',e')) -> equal_path' path path' && equalv_expr' e e'
| (UVar (n,_) as t1), (UVar (m,_) as t2) ->
    (try equalv_expr' (getuvar n) t2 with Not_found ->
    try equalv_expr' t1 (getuvar m) with Not_found ->
    n = m)
| (UVar (n,_)), t2 ->
    (try equalv_expr' (getuvar n) t2 with Not_found -> false)
| t1, (UVar (m,_)) ->
    (try equalv_expr' t1 (getuvar m) with Not_found -> false)
| (EAtom (o,k)), (EAtom (o',k')) ->
    (o == o') && (List.for_all2 equal_kind k k')
| (EApp(t1,t2)), (EApp(t1',t2')) ->
    (equalv_expr' t1 t1') && (equalv_expr' t2 t2')
| (EAbs (s,t,k)), (EAbs (s',t',k')) ->
	s = s' && (equal_kind k k') && (equalv_expr' t t')
| (EAbs (_,t,_)), t' ->
    (equalv_expr' t (EApp((lift t'),EVar 0)))
| t, (EAbs (_,t',_)) ->
    (equalv_expr' (EApp((lift t),EVar 0)) t')
| EData d, EData d' -> Data.eq_data d d'
| _ -> false

let equalv_expr e1 e2 =
  let pos = get_undo_pos () in
  let r = equalv_expr' e1 e2 in
  if not r then do_undo pos;
  r

(* idem but no eta and uses no unification ... *)

let uni_expr (rl,e1,e2) (rl',e1',e2') =
let lst = ref [] in
let rec fn e1 e2 = match e1,e2 with
  (EVar n), (EVar m) -> n = m
| (UCst (n,_)), (UCst (m,_)) -> n = m
| (Path (path,e)), (Path (path',e')) -> equal_path' path path' && fn e e'
| (UVar (n,_) as t1), (UVar (m,_) as t2) ->
    (try fn (Map.find n rl) t2 with Not_found ->
    try fn t1 (Map.find m rl') with Not_found ->
    if n = m then true else
    try List.assoc n !lst = m with Not_found -> lst := (n,m)::!lst; true)
| (UVar (n,_)), t2 ->
    (try fn (Map.find n rl) t2 with Not_found -> false)
| t1, (UVar (m,_)) ->
    (try fn t1 (Map.find m rl') with Not_found -> false)
| (EAtom (o,k)), (EAtom (o',k')) -> (o == o') && (List.for_all2 equal_kind k k')
| (EApp(t1,t2)), (EApp(t1',t2')) ->
    (fn t1 t1') && (fn t2 t2')
| (EAbs (_,t,k)), (EAbs (_,t',k')) -> (equal_kind k k') && (fn t t')
| (EAbs (_,t,_)), t' ->
    (fn t (EApp((lift t'),EVar 0)))
| t, (EAbs (_,t',_)) ->
    (fn (EApp((lift t),EVar 0)) t')
| EData d, EData d' -> Data.eq_data d d'
| _ -> false in
fn e1 e1' && fn e2 e2'


let eqi_expr (rl,e1,e2) (rl',e1',e2') =
let rec fn e1 e2 = match e1,e2 with
  (EVar n), (EVar m) -> n = m
| (UCst (n,_)), (UCst (m,_)) -> n = m
| (Path (path,e)), (Path (path',e')) -> equal_path' path path' && fn e e'
| (UVar (n,_) as t1), (UVar (m,_) as t2) ->
    (try fn (Map.find n rl) t2 with Not_found ->
    try fn t1 (Map.find m rl') with Not_found ->
    n = m)
| (UVar (n,_)), t2 ->
    (try fn (Map.find n rl) t2 with Not_found -> false)
| t1, (UVar (m,_)) ->
    (try fn t1 (Map.find m rl') with Not_found -> false)
| (EAtom (o,k)), (EAtom (o',k')) -> (o == o') && (List.for_all2 equal_kind k k')
| (EApp(t1,t2)), (EApp(t1',t2')) ->
    (fn t1 t1') && (fn t2 t2')
| (EAbs (_,t,k)), (EAbs (_,t',k')) -> (equal_kind k k') && (fn t t')
| (EAbs (_,t,_)), t' ->
    (fn t (EApp((lift t'),EVar 0)))
| t, (EAbs (_,t',_)) ->
    (fn (EApp((lift t),EVar 0)) t')
| EData d, EData d' -> Data.eq_data d d'
| _ -> false in
fn e1 e1' && fn e2 e2'


let rec cmp_kind t1 t2 = match norm t1, norm t2 with
  | Unknown, Unknown ->
      0
  | KVar p1, KVar p2 -> compare p1 p2
  | KAtom (n, ln), KAtom (m, lm) ->
      let r = get_key n - get_key m in
      if r <> 0 then r else
      let rec fn l1 l2 = match l1, l2 with
        [], [] -> 0
      | (k1::l1), (k2::l2) ->
          let r = cmp_kind k1 k2 in
          if r <> 0 then r else fn l1 l2
      | _ -> failwith "bug2 in cmp_kind"
      in fn ln lm
  | (KBVar n), (KBVar m) -> n - m
  | (KArrow (t1,t2)), (KArrow (t1',t2')) ->
       let r = (cmp_kind t1 t1') in if r = 0 then (cmp_kind t2 t2') else r
  | (t1,t2) ->
       let ms = function
         KAtom _ -> 0
       | KBVar _ -> 1
       | KArrow _ -> 2
       | KVar _ -> 3
       | Unknown -> 4
       in ms t1 - ms t2

let rec cmp_path p1 p2 = match p1,p2 with
  [], [] -> 0
| [], _::l -> -1
| _::l, [] -> 1
| (LApp::l), (LApp::l') -> cmp_path l l'
| (RApp::l), (RApp::l') -> cmp_path l l'
| ((PAbs (_,k))::l), ((PAbs (_,k'))::l') ->
    let r = cmp_kind k k' in
    if r = 0 then cmp_path l l' else r
| (p1::_,p2::_) ->
    let ms = function
      LApp -> 0
    | RApp -> 1
    | PAbs _ -> 2
    in  ms p1 - ms p2

let rec cmp_kind_list l1 l2 =
  match l1, l2 with
      [], [] -> 0
    | k1::l1, k2::l2 ->
	let r = cmp_kind k1 k2 in
	if r = 0 then cmp_kind_list l1 l2 else r
    | _ ->  failwith "bug in cmp_kind_list"

(* compare expr upto alpha-eta equiv *)

let rec cmp_expr e1 e2 = match e1, e2 with
  (EVar n), (EVar m) -> n - m
| (UCst (n,_)), (UCst (m,_)) -> n - m
| (EData n), (EData m) -> Data.compare_data n m
| (Path (path,e)), (Path (path',e')) ->
    let r = cmp_path path path' in
    if r = 0 then cmp_expr e e' else r
| (UVar (n,_) as t1), (UVar (m,_) as t2) ->
    (try cmp_expr (getuvar n) t2 with Not_found ->
    try cmp_expr t1 (getuvar m) with Not_found ->
    n - m)
| (UVar (n,_)), t2 ->
    (try cmp_expr (getuvar n) t2 with Not_found -> -1)
| t1, (UVar (m,_)) ->
    (try cmp_expr t1 (getuvar m) with Not_found -> 1)
| (EAtom (o,k)), (EAtom (o',k')) ->
    let r = get_key o - get_key o' in
    if r = 0 then cmp_kind_list k k' else r
| (EApp(t1,t2)), (EApp(t1',t2')) ->
    let r = cmp_expr t1 t1' in
    if r = 0 then cmp_expr t2 t2' else r
| (EAbs (_,t,k)), (EAbs (_,t',k')) ->
    let r = cmp_kind k k' in
    if r = 0 then cmp_expr t t' else r
| (EAbs (_,t,_)), t' ->
    (cmp_expr t (EApp((lift t'),EVar 0)))
| t, (EAbs (_,t',_)) ->
    (cmp_expr (EApp((lift t),EVar 0)) t')
| t,t' ->
    let ms = function
      EVar _ -> 0
    | UCst _ -> 1
    | Path _ -> 2
    | EAtom _ -> 3
    | EApp _ -> 4
    | EAbs _ -> 5
    | EData _ -> 6
    | _ -> failwith "bug in cmp_expr"
    in ms t - ms t'

let _ = fcmp_expr := cmp_expr

let rec hash_kind d k =
  let hashval = ref 0 in
  let combine_small x = hashval := abs (!hashval * 7 + x)
  and combine_big x = hashval := abs (!hashval * 65599 + x) in
  let rec fn d t = match norm t with
      KVar _ ->
	combine_big (Random.int 65599)
    | Unknown -> combine_small 3
    | KAtom (n, l) ->
	combine_small 4; combine_small (get_key n); List.iter (fn (d-1)) l
    | (KBVar n) ->
	combine_small 5; combine_small n
    | (KArrow (t1,t2)) ->
	combine_small 6;
      if d > 0 then (fn (d - 1) t1; fn (d - 1) t2)
  in fn d k; !hashval

let rec hash_path d p =
  let hashval = ref 0 in
  let combine_small x = hashval := abs (!hashval * 7 + x)
  and combine_big x = hashval := abs (!hashval * 65599 + x) in
  let rec fn d =  function
    [] -> ()
  | LApp::l -> combine_small 1; if d > 0 then fn (d-1) l
  | RApp::l -> combine_small 2; if d > 0 then fn (d-1) l
  | PAbs(_,k)::l ->
     combine_small 3; if d > 0 then (
       combine_big (hash_kind (d - 1) k); fn (d - 1) l)
  in fn d p; !hashval

let rec hash_expr d e =
  let hashval = ref 0 in
  let combine_small x = hashval := abs (!hashval * 7 + x)
  and combine_medium x = hashval := abs (!hashval * 11 + x)
  and combine_big x = hashval := abs (!hashval * 65599 + x) in
  let rec fn d =  function
    (EVar n) -> combine_small 1; combine_small n
  | (Path (l,e)) -> if d > 0 then (combine_big (hash_path (d - 1) l);
                                   fn (d - 1) e)
  | (UCst (n,_)) -> combine_small 2; combine_small n
  | (UVar (n,_)) -> (try fn d (getuvar n)
                    with Not_found -> combine_small 3; combine_small n)
  | (EAtom(o,k)) -> combine_small 4;
      let rec hash_kind_list d = function
	  [] -> ()
	| k::l ->
	    if d > 0 then begin
	      combine_big (hash_kind (d-1) k);
	      hash_kind_list (d-1) l
	    end
      in
      combine_big (Data_base.Object.get_key o);
      hash_kind_list (d-1) k
  | (EApp(t1,t2)) -> combine_small 5;
                     if d > 0 then (fn (d - 1) t1; fn (d - 1) t2)
  | (EAbs (_,t1,_)) ->
                    combine_small 6;
                    if d > 0 then fn (d-1) t1
  | (Syntax s) -> combine_small 7
  | (EData n) -> combine_medium 8; combine_big (Hashtbl.hash n)
  | (FVar _) -> raise (Failure "bug: illegal argument hash_expr")
  in fn d e;
  !hashval

let rec hashv_expr d e =
  let hashval = ref 0 in
  let combine_small x = hashval := abs (!hashval * 7 + x)
  and combine_medium x = hashval := abs (!hashval * 11 + x)
  and combine_big x = hashval := abs (!hashval * 65599 + x) in
  let rec fn d =  function
    (EVar n) -> combine_small 1; combine_small n
  | (Path (l,e)) -> if d > 0 then (combine_big (hash_path (d - 1) l);
                                   fn (d - 1) e)
  | (UCst (n,_)) -> combine_small 2; combine_small n
  | (UVar (n,_)) -> (try fn d (getuvar n)
                    with Not_found -> combine_small 3; combine_small n)
  | (EAtom(o,k)) -> combine_small 4;
      let rec hash_kind_list d = function
	  [] -> ()
	| k::l ->
	    if d > 0 then begin
	      combine_big (hash_kind (d-1) k);
	      hash_kind_list (d-1) l
	    end
      in
      combine_big (Data_base.Object.get_key o);
      hash_kind_list (d-1) k
  | (EApp(t1,t2)) -> combine_small 5;
                     if d > 0 then (fn (d - 1) t1; fn (d - 1) t2)
  | (EAbs (s,t1,_)) ->
                    combine_small 6; combine_big (Hashtbl.hash s);
                    if d > 0 then fn (d-1) t1
  | (Syntax s) -> combine_small 7
  | (EData n) -> combine_medium 8; combine_big (Hashtbl.hash n)
  | (FVar _) -> raise (Failure "bug: illegal argument hash_expr")
  in fn d e;
  !hashval

let rec hashi_expr d e =
  let hashval = ref 0 in
  let combine_small x = hashval := abs (!hashval * 7 + x)
  and combine_medium x = hashval := abs (!hashval * 11 + x)
  and combine_big x = hashval := abs (!hashval * 65599 + x) in
  let lst = ref [] in
  let max = ref 1 in
  let rec fn d =  function
    (EVar n) -> combine_small 1; combine_small n
  | (Path (l,e)) -> if d > 0 then (combine_big (hash_path (d-1) l);
                                   fn (d-1) e)
  | (UCst (n,_)) -> combine_small 2; combine_small n
  | (UVar (n,_)) -> (try combine_small (List.assoc n !lst)
                    with Not_found -> lst:= (n,!max)::!lst;
                        combine_small !max; max:=!max+1)
  | (EAtom(o,k)) -> combine_small 4;
      let rec hash_kind_list d = function
	  [] -> ()
	| k::l ->
	    if d > 0 then begin
	      combine_big (hash_kind (d-1) k);
	      hash_kind_list (d-1) l
	    end
      in
      combine_big (Data_base.Object.get_key o);
      hash_kind_list (d-1) k
  | (EApp(t1,t2)) -> combine_small 5;
                     if d > 0 then (fn (d-1) t1; fn (d-1) t2)
  | (EAbs(_,t1,_)) -> (match eta_red e with
                       EAbs(_,t1,_) ->
                         combine_small 6;
                         if d > 0 then fn (d-1) t1
                     | e -> fn d e)
  | (Syntax s) -> combine_small 7
  | (EData n) -> combine_medium 8; combine_big (Hashtbl.hash n)
  | (FVar _) -> raise (Failure "bug: illegal argument hash_expr")
  in fn d e;
  !hashval


let path_subst p t u =
  let rec fn d st l e = match l,e with
  [], _ -> norm_sexpr u st
| (LApp::p), (EApp(t1,t2)) ->
     fn d (t2::st) p t1
| (RApp::p), (EApp(t1,t2)) ->
     gn (EApp(t1,fn d [] p t2)) st
| ((PAbs _)::p), (EAbs(s,e,k)) ->
     gn (EAbs(s, fn (d + 1) [] p e,k)) st
| ((PAbs (s,k))::p), e ->
     gn (EAbs(s, fn (d + 1) [] p (EApp(lift e,EVar 0)),k)) st
| _ -> raise Wrong_path
  and gn t = function
  [] -> t
| e::ls -> gn (EApp(t,e)) ls
  in
    fn 0 [] p (norm_expr t)

let path_test p t u v =
  let res = equal_expr v (path_subst p t u) in
  if not res then begin
    !fprint_expr Basic.Map.empty v; print_newline ();
    !fprint_expr Basic.Map.empty (path_subst p t u); print_newline ();
  end;
  res

let rec path_diff k k' =
  if equal_kind k k' then 0
  else match norm2 k with
    KArrow(_,k) ->
      1 + (path_diff k k')
  | _ -> failwith "bug in path_diff"

let expr_local s =
  let rec f = function
      [] -> raise Not_found
    | (b,c)::l -> if equal_expr s c then b else f l
  in f !cur_local.cst_def

let rec head  = function
  EApp(t,_) -> head t
| EAbs(_,t,_) -> head t
| EAtom(o,k) -> (Oneq o,o)
| UVar (p,_) -> (try head (getuvar p) with Not_found -> (Uveq,dummy_obj))
| UCst (p,_) -> (Uneq p,dummy_obj)
| _ -> (Alleq,dummy_obj)

let rec assoc_eq o l = match o, l with
  (_, []) -> raise Not_found
| Uneq n, (Uneq n',x)::l when n == n' -> x
| Oneq o, (Oneq o',x)::l when o == o' -> x
| Alleq, (Alleq,x)::l -> x
| Uveq, (Uveq,x)::l -> x
| _, _:: l -> assoc_eq o l

let rec count_lambdas =  function
  EAbs(_,t,_) -> 1 +  count_lambdas t
| UVar (p,_) -> (try count_lambdas (getuvar p) with Not_found -> 0)
| _ -> 0

let rec advance_in_arrow n k =
 match n, norm2 k with
    0, k -> k
  | n, KArrow(_,k) -> advance_in_arrow (n-1) k
  | _ -> failwith "bug in advance_in_arrow"

let rec head_length  = function
  EApp(t,_) -> head_length t - 1
| EAbs(_,t,_) -> head_length t + 1
| EAtom(o,k) -> 0
| UVar (p,_) -> (try head_length (getuvar p) with Not_found -> 0)
| UCst (p,_) -> 0
| _ -> 0

let rec head_kind  = function
  EApp(t,_) -> head_kind t
| EAbs(_,t,_) -> head_kind t
| EAtom(o,k) -> (Oneq o,o,k)
| UVar (p,k) -> (try head_kind (getuvar p) with Not_found -> (Uveq,dummy_obj,[k]))
| UCst (p,k) -> (Uneq p,dummy_obj,[k])
| _ -> (Alleq,dummy_obj,[mk_Var()])

module Ekey = struct
  type key = expr
  let hash = hashv_expr 7
  let eq = equalv_expr
end

module ECache = Cache (Ekey)

let expr_cache = ECache.create 1000

let rec equal_kind_no_unif t1 t2 = match norm2 t1, norm2 t2 with
    (KVar ptr), (KVar ptr') ->
      ptr == ptr'
  | KAtom (n, ln), KAtom (m, lm) ->
      n == m && List.for_all2 equal_kind_no_unif ln lm
  | (KBVar n), (KBVar m) -> n = m
  | (KArrow (t1,t2)), (KArrow (t1',t2')) ->
       equal_kind_no_unif t1 t1' && equal_kind_no_unif t2 t2'
  | Unknown, Unknown -> true
  | _ -> false

module Kkey = struct
  type key = kind
  let hash = hash_kind 7
  let eq = equal_kind_no_unif
end

module KCache = Cache (Kkey)

let kind_cache = KCache.create 1000

module Pkey = struct
  type key = path list
  let hash = hash_path 7
  let eq = equal_path
end

module PCache = Cache (Pkey)

let path_cache = PCache.create 2000

let ckind_expr_copy, cexpr_copy, ckind_copy, ctexpr_copy  =
  let ls = ref [] in
  let rec f t = match norm t with
    KVar ptr  ->
      begin
	try List.assq ptr !ls
	with
	  Not_found ->
	    let t' = mk_Var () in
	    ls := (ptr,t')::!ls; t'
      end
  | KBVar _ as t -> KCache.cache kind_cache t
  | KAtom (_,[]) as t -> KCache.cache kind_cache t
  | KAtom (n,l) -> KCache.cache kind_cache (KAtom (n, List.map f l))
  | KArrow (t1,t2) -> KCache.cache kind_cache (KArrow (f t1,f t2))
  | Unknown as t -> KCache.cache kind_cache t
  and g e = ECache.cache expr_cache (match e with
    EAtom (o,k) -> EAtom(o, List.map f k)
  | EApp (t,t') -> EApp(g t,g t')
  | EAbs (s,t,k) -> EAbs(s,g t,f k)
  | UVar (n,_) as e -> (try g (getuvar n) with Not_found -> e)
  | Path (l,e) -> Path (kp l, g e)
  | e -> e)
  and h = function
    Def v -> Def (g v)
  | Prg v -> Prg (g v)
  | v -> v
  and kp = function
    [] -> []
  | (PAbs (s,k))::l -> PCache.cache path_cache ((PAbs(s,f k))::(kp l))
  | (p::l) -> PCache.cache path_cache (p::kp l)

  in
    (fun (t,k) -> ls:=[];(h t, f k)),
    (fun t -> ls:=[];h t),
    (fun k -> ls:=[];f k),
    (fun k -> ls:=[];g k)

let clear_cache () =
  ECache.clear expr_cache;
  KCache.clear kind_cache;
  PCache.clear path_cache

let mod_kind_copy, mod_copy =
  let ls = ref [] in

  let rec f copy t = match norm t with
    KVar ptr  ->
      begin
	try List.assq ptr !ls
	with
	  Not_found ->
	    let t' = mk_Var () in
	    ls := (ptr,t')::!ls; t'
      end
    | KAtom (n,l) -> KAtom(copy n, List.map (f copy) l)
    | KArrow (t1,t2) -> KArrow (f copy t1,f copy t2)
    | t -> t

  and g copy e = ECache.cache expr_cache (match e with
    EAtom (o,k) -> EAtom(copy o, List.map (f copy) k)
  | EApp (t,t') -> EApp(g copy t,g copy t')
  | EAbs (s,t,k) -> EAbs(s,g copy t, f copy k)
  | UVar (n,_) as e -> (try g copy (getuvar n) with Not_found -> e)
  | Path (l,e) -> Path (kp copy l, g copy e)
  | e -> e)

  and kp copy = function
    [] -> []
  | (PAbs (s,k))::l -> (PAbs(s,f copy k))::(kp copy l)
  | x::l -> x::(kp copy l)

  in
  f, g

exception Fail_saturate

let lArrow l k =
  let rec kn = function
      [] -> k
    | k'::l -> KArrow(k',kn l)
  in
  kn l

let saturate t t' nl k k' env =
(*
  !fprint_expr Basic.Map.empty t;
  print_newline ();
  !fprint_expr Basic.Map.empty t';
  print_newline ();
  !fprint_kind k;
  print_newline ();
  !fprint_kind k';
  print_newline ();
*)
  let nv env k =
    if env = [] then UVar(new_uvar (), k)
    else
      let k = lArrow env k in
      let v = UVar(new_uvar (), k) in
      let rec an t n = function
        [] -> t
      | _::l -> an (EApp(t,EVar n)) (n+1) l
      in
      an v 0 env
  in

  let rec fn nl l t t' ty =
    if nl <= 0 && equal_kind ty k' then (-nl,l,t,t')
    else
      match norm2 ty with
	KArrow(ka,ty) ->
	  let v = nv env ka in
	  fn (nl - 1) ((v,ka)::l) (EApp(t,v)) (EApp(t',v)) ty
      | KVar _ ->
	  let _ = equal_kind ty (KArrow(mk_Var (),mk_Var ())) in
	  fn nl l t t' ty
      | _ ->
	  raise Fail_saturate
  in fn nl [] t t' k

let simpl_match umax e1 e2 =
let subst = ref [] in
let rec fn e1 e2 =
  match e1, e2 with
  (EVar n), (EVar m) -> n = m
| (EData n), (EData m) -> Data.eq_data n m
| (UCst (n,_)), (UCst (m,_)) -> n = m
| (Path (path,e)), (Path (path',e')) ->
    raise (Failure "bug in simpl match")
| (UVar (n,_) as t1), (UVar (m,_) as t2) ->
    (try fn (getuvar n) t2 with Not_found ->
    try fn t1 (getuvar m) with Not_found ->
    try fn (List.assoc n !subst) t2 with Not_found ->
    try fn t1 (List.assoc m !subst) with Not_found ->
      if n <> m then
      	if n < 0 && n > umax then (subst:=(n,t2)::!subst; true)
	else if m < 0 && m > umax then (subst:=(m,t1)::!subst; true)
	else false
      else true)
| (UVar (n,_)), t2 ->
    (try fn (getuvar n) t2 with Not_found ->
    try fn (List.assoc n !subst) t2 with Not_found ->
    if n < 0 && n > umax && not (occur_uvar n t2) then
      (subst:=(n,t2)::!subst; true) else false)
| t2, (UVar (n,_)) ->
    (try fn (getuvar n) t2 with Not_found ->
    try fn (List.assoc n !subst) t2 with Not_found ->
    if n < 0 && n > umax && not (occur_uvar n t2) then
      (subst:=(n,t2)::!subst; true) else false)
| (EAtom (o,k)), (EAtom (o',k')) -> o == o'
| (EApp(t1,t2)), (EApp(t1',t2')) ->
    (fn t1 t1') && (fn t2 t2')
| (EAbs (_,t,k)), (EAbs (_,t',k')) -> fn t t'
| (EAbs (_,EApp(t,t''),_)), t' ->
    (fn t'' (EVar 0)) && (fn t (lift t'))
| t', (EAbs (_,EApp(t,t''),_)) ->
    (fn t'' (EVar 0)) && (fn t (lift t'))
| _ -> false
in if fn e1 e2 then !subst else raise Not_found

let eqcmp e1 e2 e3 e4 =
  let rec fn d = function
    EAbs(_,e,k) ->
      UVar(d, k)::fn (d-1) e
  | _ -> []
  in
  let n0 = new_uvar() in
  let lu = fn n0 e1 in
  let n1 = n0 - List.length lu in
  let rec check e l = match e,l with
    EAbs(_,e,k), (UVar(d, k')::l) ->
      UCst(n0-d,k)::check e l
  | (EAbs _, _) | (_, (_::_)) -> raise Not_found
  | _, [] -> []
  in
  let lc = check e3 lu in
  let e1 = norm_sexpr e1 lu in
  let e2 = norm_sexpr e2 lu in
  let e3 = norm_sexpr e3 lc in
  let e4 = norm_sexpr e4 lc in
  let l = simpl_match n1 (EApp(e1,e2)) (EApp(e3,e4)) in
  let rec perm d =
    try
      let n = match (List.assoc d l) with
        UCst(n,_) -> n
      | _ -> failwith "bung in eqncmp"
      in n::perm (d-1)
    with Not_found -> []
  in perm n0

let add_Equations sym rf o2 ld e1 e2 nl e3 k cl sy ncond exported =
  let rec mk_perm d = function
    EAbs(_,e,_) -> d::(mk_perm (d+1) e)
  | _ -> [] in
  let e3 = match e3 with
    Eq_theo e3 -> Eq_theo e3
  | _ ->
    print_endline "Def. Error: Can't add a local equation as a rewrite rule";
    raise Error in
  let e1 = ctexpr_copy e1 and e2 = ctexpr_copy e2 in
  let old = get_Equations (get_ext_tbl sym) in
  try
    let l = eqhash_find old rf in
    let rec add acc = function
      (o2',e1',e2',nl',k',sy',eqtl as tpl)::l ->
        if sy <> sy' || o2 != o2' || not (equal_kind k k')
          then add (tpl::acc) l
        else (try
          let perm = eqcmp e1 e2 e1' e2' in
	  if exists (fun
	    (e3',_,_,_,_,_) ->
	      match e3, e3' with
		Eq_theo th, Eq_theo th' -> th == th'
	      |	_ -> false) eqtl then raise Exit;
          let rec insert x l = match x,l with
            _, [] -> [x]
          | (_,_,_,_,ncond,_), (_,_,_,_,ncond',_ as y)::l' ->
              if ncond < ncond' then x::l else y::insert x l'
          in
          let neqtl = insert (e3,perm,cl,ld,ncond,exported) eqtl in
          eqhash_remove old rf;
          eqhash_add old rf (rev_append acc ((o2',e1',e2',min nl nl',k',sy',neqtl)::l))
        with Not_found -> add (tpl::acc) l)
    | [] ->
        eqhash_remove old rf;
        let perm = mk_perm 0 e1 in
        eqhash_add old rf
          (snoc (o2,e1,e2,nl,k,sy,[e3,perm,cl,ld,ncond,exported]) l)
    in add [] l
  with
    Not_found ->
      let perm = mk_perm 0 e1 in
      eqhash_add old rf [o2,e1,e2,nl,k,sy,[e3,perm,cl,ld,ncond,exported]];
      update_ext_link sym
  | Exit ->
      print_string "Warning: equation already exists"; print_newline ()

let equal_rule_option o1 o2 =
  match o1, o2 with
    Elim_opt l1, Elim_opt l2 -> l1 = l2
  | Intro_opt(n1,None), Intro_opt(n2,None) -> n1 = n2
  | Intro_opt(n1,Some o1), Intro_opt(n2,Some o2) -> o1 == o2
  | _ -> false

let add_Rules sym rf s expr expr' pat n ln order exported =
  let expr = ctexpr_copy expr in
  let old = get_Rules (get_ext_tbl sym) in
  (try
    let l = symhash_find old rf in
    symhash_remove old rf;
    try
      let oexpr,oexpr',opat,on,oln,order,oex = List.assoc s l in
      if not
         (oexpr' == expr' &&
          n = on && equal_rule_option ln oln && (oex || not exported)) then
	begin
          print_string "Error: Can't add the rule \"";
	  print_string (get_name expr');
          print_endline "\".";
          print_string "There is allready a rule (\"";
	  print_string (get_name oexpr');
	  print_string "\") for the connective \"";
          print_string (get_name rf);
          print_string "\"  with the abbreviation \"";
          print_string s;
          print_endline "\".";
          raise Error
      	end

    with Not_found ->
      symhash_add old rf ((s,(expr,expr',pat,n,ln,order,exported))::l)
  with
    Not_found ->
      symhash_add old rf [s,(expr,expr',pat,n,ln,order,exported)]);
  update_ext_link sym

let add_Trivial_Hacks sym rf n exported =
  if is_capsule rf then failwith "Can not add a local object to a table";
  let old = get_Trivial_Hacks (get_ext_tbl sym) in
  (try
    symhash_remove old rf;
    symhash_add old rf (n,exported)
  with
    Not_found -> symhash_add old rf (n,exported));
  update_ext_link sym

let add_Tex_syntax sym rf name n exported =
  if is_capsule rf then failwith "Can not add a local object to a table";
  let old = get_Tex_syntax (get_ext_tbl sym) in
  (try
    symhash_remove old rf;
    symhash_add old rf (name,n,exported)
  with
    Not_found -> symhash_add old rf (name,n,exported));
  update_ext_link sym

let apply_perm p l =
  let rec fn = function
    [] -> []
  | n::p ->
      (try List.nth l n with e -> failwith "bug nth 2")::fn p
  in fn p

let rec add_to_tbl ctxt maxvar tbl e1 e2 =
  let rec gn tbl (e01, e02) =
    let rec fn acc tbl e1 e2 = match e1, e2 with
      (EVar n), (EVar m) when n = m ->
         List.fold_left gn tbl acc
    | (EData n), (EData m) when Data.eq_data n m ->
         List.fold_left gn tbl acc
    | (UCst (n,_)), (UCst (m,_)) when n = m ->
         List.fold_left gn tbl acc
    | (UVar (n,_)), (UVar (p,_)) when n = p && acc = [] ->
         List.fold_left gn tbl acc
    | (UVar (n,_)), t2 ->
         (try fn acc tbl (Map.find n ctxt) t2
          with Not_found ->
            if match maxvar with None -> true | Some (p,q) ->
              (n < 0 && n > p) || (n > 0 && n < q)
            then
              try
                let l = Map.find n tbl in
                Map.add n ((e01,e02)::l) tbl
              with Not_found -> Map.add n [e01,e02] tbl
            else tbl)
    | t1, (UVar (m,_)) ->
         (try fn acc tbl t1 (Map.find m ctxt)
          with Not_found ->
            if match maxvar with None -> true | Some (p,q) ->
              (m < 0 && m > p) || (m > 0 && m < q)
            then
              try
                let l = Map.find m tbl in
                Map.add m ((e01,e02)::l) tbl
              with Not_found -> Map.add m [e01,e02] tbl
            else tbl)
    | (EAtom (o,k)), (EAtom (o',k')) when
        (o == o') && (!fis_close o || get_value o = Cst) ->
         List.fold_left gn tbl acc
    | (EAtom (o,k)), _ when
        (match get_value o with
           Def _ -> not (!fis_close o) && not (is_recursive o)
         | Prg _ -> true
         | _ -> false) ->
         let ne1 = match get_value o with
           Def ne1 -> ne1
         | Prg ne1 -> ne1
         | _ -> raise Exit in
         fn acc tbl ne1 e2
    | _, (EAtom (o,k)) when
        (match get_value o with
           Def _ -> not (!fis_close o)  && not (is_recursive o)
         | Prg _ -> true
         | _ -> false) ->
         let ne2 = match get_value o with
           Def ne2 -> ne2
         | Prg ne2 -> ne2
         | _ -> raise Exit in
         fn acc tbl e1 ne2
    | (EApp(t1,t2)), (EApp(t1',t2')) ->
        fn ((t2,t2')::acc) tbl t1 t1'
    | (EAbs _, _) | (_, EAbs _) when acc <> [] ->
        fn [] tbl (norm_lsexpr ctxt e1 (List.map fst acc))
                  (norm_lsexpr ctxt e2 (List.map snd acc))
    | (EAbs (_,t,k)), (EAbs (_,t',k')) ->
        fn []  tbl t t'
    | t, (EAbs (_,t',_)) ->
        fn [] tbl (EApp((lift t),EVar 0)) t'
    | (EAbs (_,t',_)), t ->
        fn [] tbl t' (EApp((lift t),EVar 0))
    | _ -> raise Exit
    in fn [] tbl e01 e02
  in gn tbl (e1, e2)

let _ =
  fadd_to_tbl := add_to_tbl

let space_of_int n =
  (string_of_float (float n /. 100.0))^"em"
let space_of_num n =
  (string_of_float (Num.float_of_num n /. 100.0))^"em"
