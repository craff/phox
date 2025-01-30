(*######################################################*)
(*			pattern.ml			*)
(*######################################################*)

open Format
open Type.Base
open Type
open Flags
open Local
open Lambda_util
open Print
open Typunif
open Typing
open Af2_basic
open Basic
open Undo

exception Not_normal
exception Fail_matching
exception Ill_rule of string

type trinfo = {
    nlim : int;
    eqlvl : int;
    from_trivial : bool ;
    first_order : bool;
    auto_elim : bool;
    eqflvl : int
  }

type rrule =
  Req of path list * expr * state_c option * expr * expr * state_c * state list * bool
| Rdef of path list * state_c option * obj * kind list * expr list * bool
| Insert of state_c

let poly_idt () =
  let k = mk_Var () in
  EAbs("x",EVar 0,k)

let defgoal = { gref = -1; hyp = []; oldhyp = [];
                eqns = []; concl = EVar(-1); ax_test = true; left_test = true;
                local = empty_local; done_list = [], [], Exprmap.empty }

let match_local = ref empty_local

let deftri =
  {nlim = 0; eqlvl = 0; from_trivial = true; first_order = true;
   auto_elim = true; eqflvl = 0},
  (fun _ -> failwith "bug: call_trivial not ready"),
  (defgoal,Fin 0,[])

let cur_ref = ref 1
let new_ref () =
  let p = !cur_ref in cur_ref := p + 1; p
let reset_ref () = cur_ref := 0

let cur_fin = ref 1
let new_fin () =
  let p = !cur_fin in cur_fin := p + 1; p
let reset_fin () = cur_fin := 0

module Adone_key = struct
  type key = expr Map.t * expr * expr

  let hash (rl,x,y) =
    abs ((hashi_expr 6 (norm_lexpr rl x)) + (hashi_expr 6 (norm_lexpr rl y)))

  let eq (rl,x,y as c) c' = uni_expr c c' || uni_expr (rl,y,x) c'
end

module Adone_hash = Myhashtbl.Hashtbl (Adone_key)

let adone = ref (Adone_hash.create 401)

let find_adone = Adone_hash.find !adone
let clear_adone = Adone_hash.clear
let badd_adone = Adone_hash.badd !adone
let fast_remove_adone = Adone_hash.fast_remove !adone

let push_adone, pop_adone =
  let adstack = ref [] in
  (fun () ->
     adstack := !adone::!adstack;
     adone := Adone_hash.create 401),
  (fun () ->
     match !adstack with
       [] -> failwith "bug in pop adone"
     | a::s -> adone := a; adstack := s)

exception Fail_match of path list

let rec make_args t l = match norm2 t, l with
  _, [] -> []
| (KArrow(ka,kr)), (a::l) -> (a,ka)::(make_args kr l)
| (KVar _ as t), l ->
    unif t (KArrow(mk_Var (), mk_Var ()));
    make_args t l
| _ -> raise (Failure "bug3 in make_args")

let sub_kind k k'  =
  let rec fn k' =
    if equal_kind k k' then [] else begin
      match norm2 k' with
	KArrow(k,k') -> k::fn k'
      | _ -> raise Not_found
    end
  in fn k'

let rec make_path path  = function
  [] -> path
| _::l -> make_path (LApp::path) l

let cross_var = ref false

let term_to_eqn e0 result env =
  let lst = ref [] and nb = ref 0 in
  let kt = fast_type_infer env e0 in
  let rec fn e = match e with
  EApp(t,t') -> lst:=t'::!lst; nb := !nb + 1; fn t
| EAtom (o,k) ->
      {head=e; args = make_args (subst_obj_kind k o) !lst;
       nbargs = !nb; order = 0; allt = e0; kind = kt}
| UCst (_,k) ->
    {head=e; args = make_args k !lst;
       nbargs = !nb; order = 0; allt = e0; kind = kt}
| EVar n ->
      {head=e; args = make_args (List.nth env n) !lst;
       nbargs = !nb; order = 0; allt = e0; kind = kt}
| EAbs _ ->
      if !lst <> [] then let l = !lst in lst:=[]; nb:=0;
      fn (norm_lsexpr result e l) else
      {head=e; args = [];
       nbargs = 0; order = 0; allt = e0; kind = kt}
| UVar (n,k) -> (
      cross_var := true;
      try fn (Map.find n result)
      with Not_found ->
      {head=e; args = make_args k !lst;
       nbargs = !nb; order = order k; allt = e0; kind = kt})
| EData _ ->
      {head=e; args = make_args kNum !lst;
       nbargs = !nb; order = 0; allt = e0; kind = kt}
| Path _ | FVar _ | Syntax _ -> raise (Failure "bug in term_to_eqn")

  in fn e0


let print_eqn e = print_expr_tr e.allt

let rec _print_eqns = function
  [] -> print_newline ()
| (e1,e2,_,_,_,_,(_,lvl,bl,br))::l ->
     open_hvbox 0;
     print_int lvl; if bl then print_string "l"; if br then print_string "r";
     print_eqn e1; print_string " ="; print_break 1 2;
     print_eqn e2; print_newline (); _print_eqns l

let build_getrwt leqn key =
  let l1 = try eqhash_find tbl_rewrite key
           with Not_found -> [] in
  let l2 = try List.assoc key leqn
           with Not_found -> [] in
  l1@l2

let getrwt = ref (fun _ -> failwith "getrwt undefined")

(* generic k [k1...kp] produit
   ?1 x_0 ... x_{p-1}
  x_0 : k1 ... x_{p-1} : kp
  ?1  : k1 -> ... -> kp -> k
*)
let generic k kl =
  let p = List.length kl in
  let kt = lArrow (List.map snd kl) k in
  let head = UVar(new_uvar (),kt) in
  let rec fn n t = match n with
    0 -> t
  | _ -> fn (n-1) (EApp(t, EVar(n-1)))
  in fn p head

(* pi n [t1...tp]  [k1...kq]
   \x1:k1 ... \xp:kp (xn (?1 x1 ... xp) ... )
*)
let pi n args kl =
  let p = List.length args in
  if not ((1 <= n) && (n <= p)) then raise (Invalid_argument "pi");
  let rec gn = function
    [] -> EVar (p - n)
  | k::l -> EApp(gn l, generic k args)
  and fn = function
    [] -> gn (List.rev kl)
  | (_,k)::ls -> EAbs("x",fn ls,k)
  in fn args

let cste t0 args =
  let rec fn = function
    [] -> t0
  | (_,k)::ls -> EAbs("x",fn ls,k)
  in fn args

let pid cst args kl =
  let rec gn = function
    [] -> cst
  | (_,k)::l -> EApp(gn l, generic k args)
  and fn = function
    [] -> gn (List.rev kl)
  | (_,k)::ls -> EAbs("x",fn ls,k)
  in fn args

let eta_expand result u k0 n args  =
  let rec fn l = function
    EAbs(s,e,k) -> fn ((s,k)::l) e
  | UVar(n,_) -> (try fn l (Map.find n result) with Not_found -> l)
  | _ -> l
  in
  let sl = fn [] u in
  let kt = lArrow (List.map snd args) k0 in
  let rec gn v = function
    0 -> v
  | n -> let n = n - 1 in gn (EApp(v,EVar n)) n
  in
  let rec hn t = function
    [] -> t
  | ((s,k)::l) -> hn (EAbs(s,t,k)) l
  in
  let rec kn t = function
    [] -> t
  | ((_,k)::l) -> kn (EAbs("x",t,k)) l
  in
  let t = UVar(new_uvar (), kt) in
  kn (hn (gn t (n + List.length sl)) sl) args

let rec result_kind k n = match norm2 k, n with
  k, 0 -> k
| (KArrow(_,k)), n -> result_kind k (n - 1)
| _, _ -> raise (Failure "bug in result_kind")

let rev_path p =
  let rec fn l = function
	[] -> l
  | (Req(a1,a2,a3,a4,a5,a6,a7,b))::ls -> fn ((Req(a1,a2,a3,a5,a4,a6,a7,not b))::l) ls
  | (Rdef(a1,a2,a3,a4,a5,b))::ls -> fn ((Rdef(a1,a2,a3,a4,a5,not b))::l) ls
  | x::ls -> fn (x::l) ls
  in fn [] p

let rec count_eq = function
	[] -> 0
  | (Req _)::ls -> 1 + count_eq ls
  | _::ls -> count_eq ls

let did_match = ref false
let no_match = ref false
let muvar = ref 0 and mvvar = ref 0
let dm_stack = ref []
let push_dm () =
  dm_stack:=(!no_match,!did_match,!muvar,!mvvar)::!dm_stack
let pop_dm () =
  match !dm_stack with
    (n,x,y,z)::s ->
      no_match:=n; did_match:= x; muvar := y; mvvar:= z; dm_stack := s
  | _ -> failwith "bug in pop_dm"
let reset_dm () =
  dm_stack:=[]; muvar := 0; mvvar:= 0; no_match := false

let nomatch_set = ref Set.empty

let reset_nomatch_set () =
  nomatch_set := Set.empty

let rec sublist p1 p2 = match p1,p2 with
  [], _ -> true
| (LApp::l), (LApp::l') -> sublist l l'
| (RApp::l), (RApp::l') -> sublist l l'
| ((PAbs _)::l), ((PAbs _)::l') -> sublist l l'
| _ -> false

let ssublist p1 p2 =
match p1 with
  None -> true
| Some p1 ->
    let rec fn p1 p2 =
      match List.rev p1, List.rev p2 with
      | _, [] -> false
      | [], _ -> true
      | (LApp::l), (LApp::l') -> fn l l'
      | (RApp::l), (RApp::l') -> fn l l'
      | ((PAbs _)::l), ((PAbs _)::l') -> fn l l'
      | _ -> false
    in fn p1 p2

let test_hash path e1 e2 rl lvl =
  let lvl' =
      (try
(*
	  print_string "searching: ";
	  print_expr_tr  (norm_lexpr rl e1); print_string " ";
	  print_expr_tr  (norm_lexpr rl e1); print_string " ";
*)
          find_adone (rl,e1,e2)
      with Not_found -> -1)
  in
(*
    print_int lvl'; print_newline ();
*)
    if lvl' >= lvl then (
    raise (Fail_match path))


let add_eqn result e l =
  begin
    let (t1, t2, _, path, _, _, _, (_, lvl, _, _)) = e in
    test_hash path t1.allt t2.allt result lvl
  end;

  let arg_mes args =
    let fn acc (arg, _) =
      match head arg with
	Uveq, _ ->
	  if head_length arg = 0 then acc else acc+1
      |  _ -> acc
    in List.fold_left fn 0 args
  in

  let term_mes e1 e2 = match e1, e2 with
    {head=UVar _; nbargs=n1; _}, {head=UVar _; nbargs=n2; _} ->
       if n1 = 0 || n2 = 0 then -1 else 10000000
  | {head=UVar _; nbargs = nb; _}, _ when nb = 0 ->
      -1
  | _, {head=UVar _; nbargs = nb; _} when nb = 0 ->
      -1
  | {head=UVar _; nbargs = nb; args = args; _}, {head=EVar _; _} ->
      let ma = arg_mes args in
      nb-ma-1 + 100*ma
  | {head=UVar _; nbargs = nb; args = args; _}, _ ->
      let ma = arg_mes args in
      nb-ma + 1000*ma
  | {head=EVar _; _}, {head=UVar _; nbargs = nb; args = args; _} ->
      let ma = arg_mes args in
      nb-ma-1 + 100*ma
  | _, {head=UVar _; nbargs = nb;args=args; _} ->
      let ma = arg_mes args in
      nb-ma + 1000*ma
  | _ -> 0
  in

  let eqn_cmp (e1,e2,_,_pe,_,_,_,_) (f1,f2,_,_pf,_,_,_,_) =
    match (term_mes e1 e2 - term_mes f1 f2) with
      0 -> min (term_size_rec e1.allt) (term_size_rec e2.allt) >  min (term_size_rec f1.allt) (term_size_rec f2.allt) (*path_compare pe pf *)
    | n -> n < 0
  in

  let rec fn = function
    [] -> [e]
  | e'::l as l0 -> if eqn_cmp e e' then e::l0 else e'::(fn l)
  in (fn l : eqn list)

let rec add_texprs path l rl env insert plvl rec_open
  ((opp,lvl,inl,inr) as noeq) lll1 lll2 lll3 =
  match lll1, lll2, lll3 with
    [], [], _ -> l
  | ((e1,_)::l1), ((e2,_)::l2), (_::op) ->
(*       if not (equal_kind k1 k2) then
         raise (Failure "bug in add_texprs path"); *)
       cross_var := false;
       let t1 = term_to_eqn e1 rl env in
       let vl = !cross_var in
       cross_var := false;
       let t2 = term_to_eqn e2 rl env in
       let vr = !cross_var in
       let nnoeq = if (inr && vr) || (inl && vl) then
         (opp,lvl, inl && not vl, inr && not vr) else noeq in
       add_texprs path (add_eqn rl
         (t1, t2 , env, (RApp::op),insert, plvl, rec_open, nnoeq) l)
                  rl env insert plvl rec_open noeq l1 l2 op
  | _ -> raise (Fail_match path)


let set_plvl plvl eq =
  match eq.head with (UVar _) -> plvl - 1 | _ ->  plvl

let subst_in_eqn (eqns : eqn list) result =
  let rec fn eqns = function
    [] -> eqns
  | (({head=UVar (n1,_); allt = e1; _} as eq1),
     ({head=UVar (n2,_); allt = e2; _} as eq2),
        env, path, insert, plvl, rec_open, noeq) as c::ls ->
       (try
	  let _ = Map.find n1 result in
          let e = norm_lexpr result e1 in
        try
	  let _ = Map.find n2 result in
          let e' = norm_lexpr result e2 in
	  let eq1 = term_to_eqn e result env in
	  let eq2 = term_to_eqn e' result env in
	  let plvl = set_plvl (set_plvl plvl eq1) eq2 in
          fn (add_eqn result (eq1,eq2,env,path,insert,plvl,rec_open,noeq) eqns) ls
        with Not_found ->
	  let eq1 = term_to_eqn e result env in
	  let plvl = set_plvl plvl eq1 in
          fn (add_eqn result (eq1,eq2,env,path,insert,plvl,rec_open, noeq) eqns) ls
      with Not_found ->
      try let _ = Map.find n2 result in
          let e' = norm_lexpr result e2 in
	  let eq2 = term_to_eqn e' result env in
	  let plvl = set_plvl plvl eq2 in
          fn (add_eqn result (eq1, eq2,env,path,insert, plvl,rec_open, noeq) eqns) ls
      with Not_found -> fn (add_eqn result c eqns) ls)
  | (({head=UVar (n1,_); allt = e1; _}), eq2,
     env, path,insert,plvl,rec_open,noeq) as c::ls ->
      (try
	let _ = Map.find n1 result in
        let e = norm_lexpr result e1 in
	let eq1 = term_to_eqn e result env in
	let plvl = set_plvl plvl eq1 in
        fn (add_eqn result (eq1,eq2,env,path,insert,plvl,rec_open,noeq)
             eqns) ls
      with Not_found ->
        fn (add_eqn result c eqns) ls)
  | (eq2, ({head=UVar (n1,_); allt = e1;_}),
     env,path,insert,plvl,rec_open,noeq) as c::ls ->
      (try
        let _ = Map.find n1 result in
        let e = norm_lexpr result e1 in
	let eq1 = term_to_eqn e result env in
	let plvl = set_plvl plvl eq1 in
        fn (add_eqn result (eq2,eq1,env,path,insert,plvl,rec_open,noeq)
            eqns) ls
      with Not_found ->
        fn (add_eqn result c eqns) ls)
  | c::ls ->
      fn (add_eqn result c eqns) ls
  in fn [] eqns


let print_ctx' ctx =
  let fn n s =
    try let _ = getuvar n in ()
    with Not_found ->
    if not (Set.is_empty s) then begin
      open_hbox ();
      print_string "Unification variable ?";
      print_int n;
      print_string " should not use ";
      let first = ref true in
      open_hovbox 0;
      Set.iter (function n ->
        if not !first then (print_string ","; print_cut ());
        first := false;
        try print_string (cst_local n)
        with Not_found -> print_string "UCst"; print_int n) s;
      print_newline ()
    end
  in
  Map.iter fn ctx

let print_ctx () =
  let _,ctx,eqns,_ = get_ulocal () in
  let gn (eq1,eq2,_,_,_,_,_,_) =
    open_hbox ();
    print_string "This equation should hold : ";
    print_expr eq1.allt;
    print_string " = ";
    print_expr eq2.allt;
    print_newline ()
  in
  print_ctx' ctx;
  List.iter gn eqns


let subraise path p =
  if not (sublist (List.rev path) (List.rev p)) then raise (Fail_match p)

exception Fast_exit of path list

type goal_state = goal * state * state list

exception Fail_subst

let simpl_subst_uvar n t result (ctx, nonu) =
  if (n > !muvar && n < !mvvar && !no_match && n > 0) || Set.mem n !nomatch_set
  then raise Fail_subst else did_match := true;
  let ctx =
    try
      let s = Map.find n ctx in
      propagate result ctx s t
    with
      Not_found -> ctx
    | Fail_propagate -> raise Fail_subst
  in
  let nresult = Map.add n t result in
  let nonu =
    try
      update_nonunifs n nresult nonu
    with
      Non_unif -> raise Fail_subst
  in
  nresult,(ctx, nonu)

let has_neg result ctx t =
  let result = ref result and ctx = ref ctx in
  let chg = ref false in
  let rec g d acc = function
    EApp (t,t') -> g d (t'::acc) t
  | EAbs (_,t,_) as e ->
      if acc = [] then g (d+1) [] t
      else (g d [] (norm_lsexpr !result e acc); chg := true)
  | EVar p  -> if p >= d then raise Exit
               else List.iter (g d []) acc
  | UVar (q,k) -> (
      try g d acc (Map.find q !result)
      with Not_found ->
      let hn, nbv, l = List.fold_right
        (fun t (hn, n, l) ->
           let sr = !result and sc = !ctx in
           try g d [] t; (hn, n+1, (n::l))
           with Exit -> result := sr; ctx := sc; true, n+1, l)
        acc (false, 0, []) in
      if hn then begin
        let rec h kl n ln k = match n,ln, norm2 k with
          0, [], k ->
            let nk = lArrow kl k in
            UVar(new_uvar (),nk)
        | n, (q::ln), (KArrow(k,k')) when q = n - 1 ->
            let t = h (k::kl) (n-1) ln k' in
            EApp(t,EVar q)
        | n, ln, (KArrow(_,k)) ->
            h kl (n-1) ln k
        | _ -> failwith "bug3 in has_neg"
        in
        let t0 = h [] nbv l k in
        let rec kn n k = match n, norm2 k with
          0, _ -> t0
        | n, (KArrow (k,k')) -> EAbs("x",kn (n-1) k',k)
        | _ -> failwith "bug5 in has_neg"
        in
        let nr, nc = simpl_subst_uvar q (kn nbv k) !result !ctx in
        result := nr; ctx := nc; chg := true
      end)
  | EAtom (o,_) ->
      (match get_value o with
        Def e -> if is_capsule o then g d acc e else List.iter (g d []) acc
      | Prg e -> g d [] (norm_lsexpr !result e acc)
      | _ -> List.iter (g d []) acc)
  | _ -> List.iter (g d []) acc
  in try g 0 [] t; !result, !ctx, !chg
     with Exit -> raise Fail_subst

let subst_uvar n t result ctx =
  let result, (ctx,nonu), chg = has_neg result ctx t in
  let t = if chg then norm_lexpr result t else t in
  if (n > !muvar && n < !mvvar && !no_match && n > 0) || Set.mem n !nomatch_set
  then raise Fail_subst else did_match := true;
  let ctx =
    try
      let s = Map.find n ctx in
      propagate result ctx s t
    with
      Not_found -> ctx
    | Fail_propagate -> raise Fail_subst
  in
  let nresult = Map.add n t result in
  let nonu =
    try
      update_nonunifs n nresult nonu
    with
      Non_unif -> raise Fail_subst
  in
  nresult,(ctx, nonu)

type tnode =
  Unode of int
| Onode of int
| Enode of int
| Anode
| Vnode of int
| Inode of Num.num
| Snode of string
| Root of (tnode * int) list

module Tnodetbl =
  Myhashtbl.Poly_Hashtbl (struct type key = tnode * int * int end)

type ttree =
  { node : tnode; son : ttree list; mutable father : mtree; mutable pos : int}

and mtree = (ttree list ref) Tnodetbl.t

exception Rec_call of ttree

let add_to_tree result tr e r pos =

  let rec add_to_tree_aux args = function
    EApp(t1,t2) -> add_to_tree_aux (t2::args) t1
  | h ->
    try let h, args = match h with
      UCst(n,_) -> Unode n, args
    | EData(Data.EInt n) -> Inode n, args
    | EData(Data.EString n) -> Snode n, args
    | UVar(n,_) -> (try raise (Rec_call
                      (add_to_tree_aux args (Map.find n result)))
                   with Not_found -> Vnode n, args)
    | EAtom(o,_) -> Onode (Data_base.Object.get_key o), args
    | EAbs(_,t,_) as e -> if args <> [] then
                       raise (Rec_call
                        (add_to_tree_aux [] (norm_lsexpr result e args)));
                     Anode, [t]
    | EVar n -> Enode n, args
    | _ -> failwith "bug0 in add_to_tree"
    in
    let th = try
        let l = !(Tnodetbl.find tr (h,0,0)) in
        match l with
          [t] -> if t.pos * pos < 0 then t.pos <- 0; t
        | _ -> failwith "bug3 in add_to_tree"
      with Not_found ->
        let t =
          { node = h; son = []; father = Tnodetbl.create 7; pos = pos} in
        Tnodetbl.add tr (h,0,0) (ref [t]);
        t
    in
    let rec fn tot p = function
      [] -> failwith "bug1 in add_to_tree"
    | t::l ->
        let acc = try !(Tnodetbl.find t.father (h,tot,p))
                  with Not_found -> [] in
        if l = [] || acc = [] then acc else interq acc (fn tot (p+1) l)
    in
    let rec gn tot t0 p = function
      [] -> ()
    | t::l ->
        gn tot t0 (p + 1) l;
        try let l = Tnodetbl.find t.father (h,tot,p) in l:=(t0::!l)
        with Not_found -> Tnodetbl.add t.father (h,tot,p) (ref [t0])
    in
    if args <> [] then
      let tot = List.length args in
      let lp = th::(List.map (add_to_tree_aux []) args) in
      match fn tot 1 lp with
        [] ->
          let t =
            { node = h; son = lp; father = Tnodetbl.create 7;pos = pos} in
          gn tot t 1 lp; t
      | [t] -> if t.pos * pos < 0 then t.pos <- 0; t
      | _ -> failwith "bug2 in add_to_tree"
    else th
   with Rec_call x -> x
in
  let t = add_to_tree_aux [] e in
  let t0 =
    { node = Root r; son = [t]; father = Tnodetbl.create 1; pos = pos} in
  Tnodetbl.add t.father (Root r,0,0) (ref [t0]); t0

let mesure rd t0 pos =
  let r0 = match t0.node with
    Root r -> r
  | _ -> failwith "bug 1 in mesure" in
  let t0 = match t0.son with
    [t] -> t
  | _ -> failwith "bug 2 in mesure" in
  let best = ref max_float in
  let rec best_root r0 l tbl =
    Tnodetbl.do_table (fun (h,_,p) nt ->
        match h with
          Root r -> (
            match !nt with
              [t] -> if t.pos * pos <= 0 then
                       let d = rd (List.rev r @ l) r0 in
                       if d < !best then best:=d
            | _ -> failwith "bug 3 in mesure")
       | _ -> List.iter (fun t -> if t.pos * pos <= 0 then
                         best_root r0 ((h,p)::l) t.father) !nt) tbl
  in
  let rec fn path t =
    best := max_float;
    if t.pos * pos <= 0 then best_root (List.rev path) [] t.father;
    let b = !best in
    let d = if t.son = [] then
        match t.node with
          Vnode _ -> 0.0 | _ -> 4.0
      else snd (List.fold_left
        (fun (p,n) x -> (p+1, n +. fn ((t.node,p)::path) x))
        (1,3.0) t.son) in
    d +. 5.0 *. min d b
  in fn r0 t0

let rec pre_unif result ctx env e1 e2 =

  let do_def oe e' k args dir =
    try
      if not (List.memq oe !match_local.local_close_tbl) then
        (let _ = symhash_find tbl_close_def oe in ());
      raise Exit
    with Not_found ->
      let e = try kind_inst oe k
      with Not_found -> raise Exit in
      let l = List.map (fun (e,_) -> e) args in
      let e = norm_lsexpr result e l in
      if dir then
	pre_unif result ctx env e e'
      else
	pre_unif result ctx env e' e
  in

  let do_csteq n e' args dir =
    let (e, _) =
      try
        List.assoc n !match_local.cst_eq
      with Not_found -> raise Exit
    in
    let l = List.map (fun (e,_) -> e) args in
    let e = norm_lsexpr result e l in
    if dir then
      pre_unif result ctx env e e'
    else
      pre_unif result ctx env e' e
  in

  let t1 = term_to_eqn e1 result env
  and t2 = term_to_eqn e2 result env in
  match t1.head, t2.head with
    EAbs(_,e1,k1), EAbs(_,e2,k2) when equal_kind k1 k2 ->
      let env = k1::env in
      pre_unif result ctx env e1 e2
  | UCst(n,_), UCst(p,_) when n = p && t1.nbargs = t2.nbargs ->
      lpre_unif result ctx env t1.args t2.args
  | EData(Data.EInt n), EData(Data.EInt p) when n = p && t1.nbargs = t2.nbargs ->
      lpre_unif result ctx env t1.args t2.args
  | EData(Data.EString n), EData(Data.EString p) when n = p && t1.nbargs = t2.nbargs ->
      lpre_unif result ctx env t1.args t2.args
  | EVar(n), EVar(p) when n = p && t1.nbargs = t2.nbargs ->
      lpre_unif result ctx env t1.args t2.args
  | EAtom(o,k), EAtom(o',k') when o == o' &&
      List.for_all2 equal_kind k k' && t1.nbargs = t2.nbargs ->
      lpre_unif	result ctx env t1.args t2.args
  | UVar(n,_), UVar(p,_) when n = p && t1.nbargs = t2.nbargs ->
      lpre_unif result ctx env t1.args t2.args
  | UVar(n,_), UVar(_,_) when t1.args = [] && t2.args = [] -> (
      try simpl_subst_uvar n e2 result ctx
      with Fail_subst -> result, ctx)
  | (UVar _, _) | (_, UVar _) ->
      (try let (result, ctx, _, rem), _  =
	fneq (0,0.0) deftri []
             ((t1, t2, env,[],None,0,([],[]),(None,0,false,false))::!remeq)
             result ctx [] [] in
      remeq:= rem;
      result, ctx
      with Fail_match _ ->  result, ctx)
  | EAtom(o1,k1), EAtom(o2,k2) ->
      if obj_cmp o1 o2 then begin
	try do_def o1 e2 k1 t1.args true with Exit ->
	try do_def o2 e1 k2 t2.args false with Exit ->
	result, ctx
      end else begin
	try do_def o2 e1 k2 t2.args false with Exit ->
	try do_def o1 e2 k1 t1.args true with Exit ->
	result, ctx
      end
  | UCst(n,_), UCst(n',_) ->
      if n > n' then begin
	try do_csteq n e2 t1.args true with Exit ->
	try do_csteq n' e1 t2.args false with Exit ->
	result, ctx
      end else begin
	try do_csteq n' e1 t2.args false with Exit ->
	try do_csteq n e2 t1.args true with Exit ->
	result, ctx
      end
  | UCst(n,_), _ -> (
      try do_csteq n e2 t1.args true with Exit ->
      result, ctx)
  | _, UCst(n,_) -> (
      try do_csteq n e1 t2.args false with Exit ->
      result, ctx)
  | EAtom(o,k), _ -> (
      try do_def o e2 k t1.args true with Exit ->
	result, ctx)
  | _, EAtom(o,k) -> (
      try do_def o e1 k t2.args false with Exit ->
	result, ctx)
  | _, _ -> result, ctx

and lpre_unif result ctx env l1 l2 =
  List.fold_left2
    (fun (result,ctx) (t1,_) (t2,_) -> pre_unif result ctx env t1 t2)
    (result,ctx) l1 l2

and newdistance result ctx env e1 e2 =
  let pos = get_undo_pos () in
  remeq := [];
  let result,_ = pre_unif result ctx env e1 e2 in
  let d = Hilbert.distance !match_local result e1 e2 in
  do_undo pos;
  d

and newdistance2 d1 result ctx env e1 e2 e3 e4 =
  if !trace_dist then begin
    open_hvbox 0;
    print_expr_tr (norm_lexpr result e1);
    print_string ","; print_break 1 2;
    print_expr_tr (norm_lexpr result e2);
    print_string " |"; print_break 1 2;
    print_expr_tr (norm_lexpr result e3);
    print_string ","; print_break 1 2;
    print_expr_tr (norm_lexpr result e4);
    print_string " -->"; print_break 1 2
  end;
  let pos = get_undo_pos () in
  remeq := [];
  let result,ctx = pre_unif result ctx env e1 e2 in
  let result,_   = pre_unif result ctx env e3 e4 in
  let d' = Hilbert.distance !match_local result e1 e2 in
  let d'' = Hilbert.distance !match_local result e3 e4 in
  do_undo pos;
  let d = d' +.  d'' in
  if !trace_dist then (
    print_float d1; print_newline ();
    print_float d; print_string ", ";
    print_float (d -. d1);
    print_newline ());
  (d' = 0.0) || (d'' <> 0.0), d, d'

and rl = ref [] and remeq = ref [] and openp = ref 0

and ldistance dpath h result ctx env l1 l2 =
  let (r,c,_) = List.fold_left2
    (fun (result,ctx,pos) (t1,_) (t2,_) ->
       let result,ctx = tdistance ((h,pos)::dpath) result ctx env t1 t2
       in result,ctx,pos+1)
    (result,ctx,1) l1 l2
  in r,c

and tdistance dpath result ctx env e1 e2 =

  let do_def oe e' k args dir =
    try
      if not (List.memq oe !match_local.local_close_tbl)
	  && not (is_recursive oe) then
        (let _ = symhash_find tbl_close_def oe in ());
      raise Exit
    with Not_found ->
      let e = try kind_inst oe k
      with Not_found -> raise Exit in
      let l = List.map (fun (e,_) -> e) args in
      let e = norm_lsexpr result e l in
      incr openp;
      if dir then
	tdistance dpath result ctx env e e'
      else
	tdistance dpath result ctx env e' e
  in

  let do_csteq n e' args dir =
    let (e, _) =
      try
        List.assoc n !match_local.cst_eq
      with Not_found -> raise Exit
    in
    let l = List.map (fun (e,_) -> e) args in
    let e = norm_lsexpr result e l in
    incr openp;
    if dir then
      tdistance dpath result ctx env e e'
    else
      tdistance dpath result ctx env e' e
  in

  let t1 = term_to_eqn e1 result env
  and t2 = term_to_eqn e2 result env in
  match t1.head, t2.head with
    EAbs(_,e1,k1), EAbs(_,e2,k2) when equal_kind k1 k2 ->
      let env = k1::env in
      tdistance dpath result ctx env e1 e2
  | UCst(n,_), UCst(p,_) when n = p && t1.nbargs = t2.nbargs ->
      ldistance dpath (Unode n) result ctx env t1.args t2.args
  | EData(Data.EInt n), EData(Data.EInt p) when n = p && t1.nbargs = t2.nbargs ->
      ldistance dpath (Inode n) result ctx env t1.args t2.args
  | EData(Data.EString n), EData(Data.EString p) when n = p && t1.nbargs = t2.nbargs ->
      ldistance dpath (Snode n) result ctx env t1.args t2.args
  | EVar(n), EVar(p) when n = p && t1.nbargs = t2.nbargs ->
      ldistance dpath (Enode n) result ctx env t1.args t2.args
  | EAtom(o,k), EAtom(o',k') when o == o' &&
      List.for_all2 equal_kind k k' && t1.nbargs = t2.nbargs ->
      ldistance dpath (Onode (Data_base.Object.get_key o))
	result ctx env t1.args t2.args
  | UVar(n,_), UVar(p,_) when n = p && t1.nbargs = t2.nbargs ->
      ldistance dpath (Unode n) result ctx env t1.args t2.args
  | UVar(n,_), UVar(_,_) when t1.args = [] && t2.args = [] -> (
      try simpl_subst_uvar n e2 result ctx
      with Fail_subst -> rl := (dpath,e1,e2)::!rl; result, ctx)
  | (UVar _, _) | (_, UVar _) ->
      (try let (result, ctx, _, rem), _  =
	fneq (0,0.0) deftri []
             ((t1, t2, env,[],None,0,([],[]),(None,0,false,false))::!remeq)
             result ctx [] [] in
      remeq:= rem;
      result, ctx
      with Fail_match _ ->  rl := (dpath,e1,e2)::!rl; result, ctx)
  | EAtom(o1,k1), EAtom(o2,k2) ->
      if obj_cmp o1 o2 then begin
	try do_def o1 e2 k1 t1.args true with Exit ->
	try do_def o2 e1 k2 t2.args false with Exit ->
	rl := (dpath,e1,e2)::!rl; result, ctx
      end else begin
	try do_def o2 e1 k2 t2.args false with Exit ->
	try do_def o1 e2 k1 t1.args true with Exit ->
	rl := (dpath,e1,e2)::!rl; result, ctx
      end
  | UCst(n,_), UCst(n',_) ->
      if n > n' then begin
	try do_csteq n e2 t1.args true with Exit ->
	try do_csteq n' e1 t2.args false with Exit ->
	rl := (dpath,e1,e2)::!rl; result, ctx
      end else begin
	try do_csteq n' e1 t2.args false with Exit ->
	try do_csteq n e2 t1.args true with Exit ->
	rl := (dpath,e1,e2)::!rl; result, ctx
      end
  | UCst(n,_), _ -> (
      try do_csteq n e2 t1.args true with Exit ->
      rl := (dpath,e1,e2)::!rl; result, ctx)
  | _, UCst(n,_) -> (
      try do_csteq n e1 t2.args false with Exit ->
      rl := (dpath,e1,e2)::!rl; result, ctx)
  | EAtom(o,k), _ -> (
      try do_def o e2 k t1.args true with Exit ->
	rl := (dpath,e1,e2)::!rl; result, ctx)
  | _, EAtom(o,k) -> (
      try do_def o e1 k t2.args false with Exit ->
	rl := (dpath,e1,e2)::!rl; result, ctx)
  | _, _ -> rl := (dpath,e1,e2)::!rl; result, ctx

and list_diff result l =
  let lp =
    let tr = Tnodetbl.create 43 in
    List.map (fun (dpath,e1,e2) ->
(*
      print_string "   ";
      List.iter (fun (h,n) -> print_int n; print_string"::") dpath;
      print_expr_tr (norm_lexpr result e1);
      print_string ","; print_expr_tr (norm_lexpr result e2);
      print_newline ();
*)
      add_to_tree result tr e1 dpath 1,
      add_to_tree result tr e2 dpath (-1)) l in
  let rec rd l1 l2 = match l1, l2 with
    (x::l), (x'::l') when x = x' -> rd l l'
  | l, l' -> float ((List.length l) + (List.length l'))
  in
  List.fold_left (fun n (t1,t2) ->
    let n1 = mesure rd t1 1 and n2 = mesure rd t2 (-1) in
(*        print_int n1; print_string " "; print_int n2; print_string " "; *)
    n +. n1 +. n2) 0.0 lp

and olddistance result ctx env e1 e2 =

  rl := []; remeq := []; openp := 0;
  let pos = get_undo_pos () in
  let result,_ = tdistance [] result ctx env e1 e2 in
  do_undo pos;
  (list_diff result !rl) +. float !openp

and olddistance2 d1 result ctx env e1 e2 e3 e4 =
  if !trace_dist then begin
    open_hvbox 0;
    print_expr_tr (norm_lexpr result e1);
    print_string ","; print_break 1 2;
    print_expr_tr (norm_lexpr result e2);
    print_string " |"; print_break 1 2;
    print_expr_tr (norm_lexpr result e3);
    print_string ","; print_break 1 2;
    print_expr_tr (norm_lexpr result e4);
    print_string " -->"; print_break 1 2
  end;
  rl := []; remeq := []; openp := 0;
  let pos = get_undo_pos () in
  let result,ctx = tdistance [] result ctx env e1 e2 in
  let l1 = !rl in
  rl := [];
  let result,_ = tdistance [] result ctx env e3 e4 in
  do_undo pos;
  let n = list_diff result l1 in
  let n' = list_diff result !rl in
  let d = max n n' +. float !openp in
  if !trace_dist then (
    print_float d; print_string ", ";
    print_float (d -. d1);
    print_newline ());
  (n = 0.0) || (n' <> 0.0), d, n

and distance result ctx env e1 e2 =
  (if !new_distance then newdistance else olddistance) result ctx env e1 e2

and distance2 d1 result ctx env e1 e2 e3 e4 =
  (if !new_distance then newdistance2 else olddistance2)
    d1 result ctx env e1 e2 e3 e4

and fneq (flvl, aug) call_trivial
         the_path (eqns : eqn list) result ctx lrl rrl =

  let eqt = ref [] in

  let rec fn only_cst (eqns : eqn list) result ctx lrl rrl =

    match eqns with
      [] -> result,ctx,(rev_path rrl@lrl),[]
    | ((eq1,eq2,env,path,insert,plvl,rec_open,((op,lvl,inl,inr) as noeq)))::suit ->

      if !trace_pmatch then begin
        open_hvbox 0;
        print_string "doing :"; print_break 1 2;
        let _ = print_path [] path in
        print_string " ";
        print_expr_tr (norm_lexpr result eq1.allt); print_string " =";
        print_break 1 2;
        print_expr_tr (norm_lexpr result eq2.allt);  print_break 1 2;
        print_string "plvl =";
        print_int plvl; print_break 1 2;
        print_string "lvl =";
        print_int lvl; if inl then print_string "l";
        if inr then print_string "r"; print_newline ();
	print_ctx' (fst ctx);
      end;

    let do_proj order rf k args = (
      let rec gn n = function
        [] -> raise (Fail_match path)
      | (arg,k')::ls ->
	  let pos = get_undo_pos () in
          try
	    (match arg with
	      EVar _ -> ()
            |  _ ->
		if plvl <= 0 then raise Not_found);
	    let kl = sub_kind k k' in
            let t = pi n args kl in
            let nr,ctx = subst_uvar rf t result ctx in
            let eqns = if order <= 1 then eqns else
	      (eq1,eq2,env,path,insert,plvl,rec_open,(op,0,inl,inr))::suit in
            fn false (subst_in_eqn eqns nr) nr ctx lrl rrl
          with
	    Not_found | Fail_match _ | Fail_subst ->
	      do_undo pos;
	      gn (n+1) ls
      in gn 1 args)

(*    and fix_head e =
      try
	let f,head, k,stack = decom'' e in
        match f with
	  None -> true
	| Some e -> fix_head (norm_sexpr e stack)
      with not_found -> false*)

    and do_cst order rf cst args kl =
(*      if not (fix_head cst) then raise (Fail_match path);*)
      let t = pid cst args kl in
      let nr,ctx = try subst_uvar rf t result ctx
                   with Fail_subst -> raise (Fail_match path) in
      let eqns = if order <= 1 then eqns else
        (eq1,eq2,env,path,insert,plvl,rec_open,(op,0,inl,inr))::suit in
      fn true (subst_in_eqn eqns nr) nr ctx lrl rrl

    and mobj_cmp o1 o2 =
      try
        match get_value o2 with
	  Def _ ->
            if not (List.memq o2 !match_local.local_close_tbl) then
              (let _ = symhash_find tbl_close_def o2 in true)
            else true
	| _ -> true
      with Not_found -> try
        match get_value o1 with
	  Def _ ->
            if not (List.memq o1 !match_local.local_close_tbl) then
              (let _ = symhash_find tbl_close_def o1 in false)
            else false
	| _ -> false
      with Not_found ->
	obj_cmp o1 o2

    and do_def oe k args t dir =
      try
        if not (List.memq oe !match_local.local_close_tbl) then
          (let _ = symhash_find tbl_close_def oe in ());
        raise (Fail_match path)
      with Not_found ->
      if List.memq oe ((if dir then fst else snd) rec_open)
      then raise (Fail_match path);
      let e = try kind_inst oe k
      with Not_found -> raise (Fail_match path) in
      let l = List.map (fun (e,_) -> e) args in
      let e = norm_lsexpr result e l in
      let lrl,rrl =
        if (Data_base.Object.get_value oe).origin = Local_hyp then
          lrl,rrl
        else if dir then
          (Rdef (path,insert,oe,k,l,true)::lrl), rrl
        else
          lrl, (Rdef (path,insert,oe,k,l,true)::rrl) in
      let t' = term_to_eqn e result env in
      let rec_open =
	if is_recursive oe then
	  match rec_open with l, r ->
	    if dir then (oe::l), r else l, (oe::r)
	else rec_open
      in
      let eq = if dir then (t', t, env,path,insert,plvl,rec_open,noeq)
                      else (t, t', env,path,insert,plvl,rec_open,noeq) in
      fn false (add_eqn result eq suit) result ctx lrl rrl

    and do_csteq n args e0 t dir =
      let e1, leq =
	try
	  let e, leq = List.assoc n !match_local.cst_eq in
	  let l = List.map (fun (e,_) -> e) args in
	  norm_lsexpr result e l, leq
	with Not_found -> raise (Fail_match path)
      in
      let make_req (e0, ll) (ng, _, e, hypt, ld) =
        let st0 = {
	  sref = new_ref ();
	  rule = if hypt then Axiom ng else Subgoal ng;
	  next = Fin (new_fin ())
        } in
	let path = make_path path args in
        let eqr = Req(path, poly_idt (),insert, e0, e, st0, [Fol st0], ld) in
        e, (eqr::ll)
      in
      let lrl,rrl =
        if dir then
          let _,lrl = List.fold_left make_req (e0,lrl) leq in
	  lrl, rrl
	else
          let _,rrl = List.fold_left make_req (e0,rrl) leq in
	  lrl, rrl
      in
      let t' = term_to_eqn e1 result env in
      let eq = if dir then (t', t, env,path,insert,plvl,rec_open,noeq)
                      else (t, t', env,path,insert,plvl,rec_open,noeq) in
      fn false (add_eqn result eq suit) result ctx lrl rrl

    and tmap t1 t2 r1 r2 =
      if lvl = 0 then raise (Fail_match path);
      (if not (ssublist op path)
         then raise (Fail_match path));

      let l1 = if r1 = Alleq || inl
        then [] else !getrwt r1
      and l2 = if r2 = Alleq || inr
        then [] else !getrwt r2 in

      if l1 = [] && l2 = [] then raise (Fail_match path);

      let l1 = generalize_for_equations l1 in
      let l2 = generalize_for_equations l2 in

      let d1 = distance result ctx env t1.allt t2.allt in

      let mes_eqn dir (o2,e1,e2,nl,k,_sy,eqtl as eq) =
(*
	List.iter2 (fun k k' ->
	  if not (equal_kind k k') then raise Fail_saturate)
	  (match (head_kind (if dir then t1 else t2).head) with _,_,k -> k)
	  (match (head_kind e1) with _,_,k -> k);
*)
        let (_pathd,_,t',t'') = saturate e1 e2 nl k t1.kind env in
        let t0' = norm_expr t' and t0'' = norm_expr t'' in
        let lf, m, ml = match dir with
            true -> distance2 d1 result ctx env t1.allt t0' t0'' t2.allt
          | false -> distance2 d1 result ctx env t2.allt t0' t0'' t1.allt
        in
        let lf = lf || (o2 = Alleq) in
        let is_simpler t1 t2 =
           match t1, t2 with
             (UCst _ | EAtom _), (UCst _ | EAtom _) -> false
           | (UCst _ | EAtom _), _ when not dir -> true
           | _, (UCst _ | EAtom _) when dir -> true
           | _ -> false
        in
        if (m = 0.0 && match eqtl with
              [] -> failwith "bug 56 in mes_eqn"
            | (_,_,_,_,nc,_)::_ -> nc = 0) then
        begin
          eqt:=[dir, (lf, -1e-100, t1.kind), eq, lrl, rrl,
                t1 , t2, suit, result, ctx, env, path, insert, plvl, rec_open,
		noeq];
          raise (Fast_exit path)
        end;
        let m = if ml = 0.0 && is_simpler t0' t0'' then 0.0 else m in
        lf, (m -. d1), t1.kind
      in

      let l2 = select
        (fun (_,_,_,_,_,sy,_ as eq) ->
           (not sy) || (not (List.exists (fun eq' -> eq == eq') l1))) l2 in
      let rec try_map f = function
	  [] -> []
	| x::l ->
	    let s = try_map f l in
	    try f x::s with Fail_saturate -> s
      in
      let l1 = try_map (fun eq -> (true, mes_eqn true eq, eq, lrl, rrl,
                  t1 , t2, suit, result, ctx, env, path, insert,
				   plvl, rec_open, noeq)) l1 in
      let l2 = try_map (fun eq -> (false, mes_eqn false eq, eq, lrl, rrl,
                  t1 , t2, suit, result, ctx, env, path, insert,
				   plvl, rec_open, noeq)) l2 in

      eqt := l1 @ l2 @ !eqt;
      raise (Fail_match path)

    and test_occur strict n0 l =
      let rec g acc = function
        EApp (t,t') -> g (t'::acc) t
      | EAbs (_,t,_) as e -> if acc = [] then g [] t
                        else g [] (norm_lsexpr result e acc)
      | Path (_,_) -> failwith "bug in test_occur"
      | UVar (p,_)  -> (try g acc (Map.find p result) with Not_found -> p = n0 ||
                                                                (strict && List.exists (g []) acc))
      | EAtom(o,_) ->
          (match get_value o with
            Def e -> if is_capsule o then g acc e else List.exists (g []) acc
          | Prg e -> g [] (norm_lsexpr result e acc)
          | _ -> List.exists (g []) acc)
      | _ -> List.exists (g []) acc in
      List.iter (fun (e,_) -> if g [] e then raise (Fail_match path)) l

    and test_args l =
      let fn = function
	  EVar _ -> true
	| _ -> false
      in
      let gn (t, _) =
	fn (norm_lexpr result t)
      in
      l <> [] && List.for_all gn l
    in


    let pos = get_undo_pos () in

    match eq1,eq2 with
      {head=EAbs(s1,e1,k1); _}, {head=EAbs(_,e2,k2); _} when equal_kind k1 k2 ->
	if !trace_pmatch then print_endline "abs-abs";
        let env = k1::env in
        fn false (add_eqn result (term_to_eqn e1 result env,
                     term_to_eqn e2 result env,
                     env,((PAbs (s1,k1))::path), insert, plvl, rec_open,noeq) suit)
                     result ctx lrl rrl

    | ({head=UCst(n1,k1); _} as t1), ({head=UCst(n2,k2); _} as t2) ->
	if !trace_pmatch then print_endline "cst-cst";
        begin
	  try try
	    if n1 != n2 || not (equal_kind k1 k2) then
	      raise (Fail_match path);
	    let np = make_path path t1.args in
            fn false (add_texprs path suit result env insert plvl rec_open
			noeq t1.args t2.args np)
              result ctx lrl rrl
	  with Fail_match p when not only_cst ->
	    do_undo pos;
	    subraise path p;
	    if n1 > n2 then do_csteq n1 t1.args t1.allt t2 true
	  else do_csteq n2 t2.args t2.allt t1 false
          with Fail_match p ->
	    do_undo pos;
	    subraise path p;
            tmap t1 t2 (Uneq n1) (Uneq n2)
	end

    | ({head=EVar n1; _} as t1), ({head=EVar n2; _} as t2) ->
	if !trace_pmatch then print_endline "evar-evar";
        if n1 <> n2 then raise (Fail_match path);
        let np = make_path path t1.args in
        fn false (add_texprs path suit result env insert plvl rec_open
	      noeq t1.args t2.args np)
           result ctx lrl rrl

    | ({head=EData n1; _} as t1), ({head=EData n2; _} as t2) ->
	if !trace_pmatch then print_endline "eint-eint";
        if not (Data.eq_data n1 n2) then raise (Fail_match path);
        let np = make_path path t1.args in
        fn false (add_texprs path suit result env insert plvl rec_open
	      noeq t1.args t2.args np)
           result ctx lrl rrl

    | ({head=EAtom(o1,k1); _} as t1), t2 when
          (Data_base.Object.get_value o1).origin = Local_hyp ->
	if !trace_pmatch then print_endline "eatomlocal-x";
	do_def o1 k1 t1.args t2 true

    | t2, ({head=EAtom(o1,k1); _} as t1) when
          (Data_base.Object.get_value o1).origin = Local_hyp ->
	if !trace_pmatch then print_endline "x-eatomlocal";
        do_def o1 k1 t1.args t2 false

    | ({head=EAtom(o1,k1); _} as t1), ({head=EAtom(o2,k2); _} as t2)  ->
	if !trace_pmatch then print_endline "eatom-eatom";
	begin
	  try try
	    if o1 != o2 || not (List.for_all2 equal_kind k1 k2) then
	      raise (Fail_match path);
            let np = make_path path t1.args in
            fn false (add_texprs path suit result env insert plvl rec_open
			noeq t1.args t2.args np)
              result ctx lrl rrl
          with Fail_match p when not only_cst ->
	    do_undo pos;
	    subraise path p;
            if mobj_cmp o1 o2 && (not (List.memq o1 (fst rec_open)) ||
	    (List.memq o2 (snd rec_open))) then
	      do_def o1 k1 t1.args t2 true
            else
	      do_def o2 k2 t2.args t1 false
          with Fail_match p ->
	    do_undo pos;
	    subraise path p;
            tmap t1 t2 (Oneq o1) (Oneq o2)
        end

   | ({head=UVar(n1,k1); _} as t1), ({head=EVar _; _} as t2) -> (
       if !trace_pmatch then print_endline "uvar-evar";
       test_occur false n1 t2.args;
       do_proj t1.order n1 (result_kind k1 t1.nbargs) t1.args)

   | ({head=UVar(n1,k1); _} as t1), ({head=EData _; _} as t2) -> (
       if !trace_pmatch then print_endline "uvar-edata";
       if t1.nbargs = 0 then (
         let result,ctx = try subst_uvar n1 t2.allt result ctx
         with Fail_subst -> raise (Fail_match path) in
         fn false (subst_in_eqn suit result) result ctx lrl rrl )
       else try
         do_proj t1.order n1 (result_kind k1 t1.nbargs) t1.args
       with Fail_match p ->
	 do_undo pos;
	 subraise path p;
         do_cst t1.order n1 t2.head t1.args t2.args)

   | ({head=UVar(n1,k1); _} as t1), ({head=UCst(n2,_); _} as t2) -> (
	if !trace_pmatch then print_endline "uvar-cst";
        test_occur false n1 t2.args;
        try if t1.nbargs = 0 then (
          test_occur true n1 t2.args;
           let result,ctx = try subst_uvar n1 t2.allt result ctx
                            with Fail_subst -> raise (Fail_match path) in
           fn false (subst_in_eqn suit result) result ctx lrl rrl )
        else try
           do_proj t1.order n1 (result_kind k1 t1.nbargs) t1.args
        with Fail_match p ->
	  do_undo pos;
	  subraise path p;
          do_cst t1.order n1 t2.head t1.args t2.args
        with Fail_match p ->
	  do_undo pos;
	  subraise path p;
	  do_csteq n2 t2.args t2.allt t1 false)

   | ({head=UVar(n1,k1); _} as t1), ({head=EAtom(o2,k2); _} as t2) -> (
	if !trace_pmatch then print_endline "uvar-eatom";
        test_occur false n1 t2.args;
        if t1.nbargs = 0 then (
          test_occur true n1 t2.args;
          let result,ctx =
	    try subst_uvar n1 t2.allt result ctx
            with Fail_subst -> raise (Fail_match path) in
          fn false (subst_in_eqn suit result) result ctx lrl rrl)
        else try
          do_proj t1.order n1 (result_kind k1 t1.nbargs) t1.args
        with Fail_match p -> try
	  do_undo pos;
	  subraise path p;
          do_cst t1.order n1 t2.head t1.args t2.args
        with Fail_match p when t1.args <> [] ->
	  do_undo pos;
	  subraise path p;
          do_def o2 k2 t2.args t1 false)

   | ({head=EVar _; _} as t2), ({head=UVar(n1,k1); _} as t1) -> (
       if !trace_pmatch then print_endline "evar-uvar";
       test_occur false n1 t2.args;
       do_proj t1.order n1 (result_kind k1 t1.nbargs) t1.args)

   | ({head=EData _; _} as t2), ({head=UVar(n1,k1); _} as t1) -> (
       if !trace_pmatch then print_endline "edata-uvar";
       if t1.nbargs = 0 then (
         let result,ctx = try subst_uvar n1 t2.allt result ctx
         with Fail_subst -> raise (Fail_match path) in
         fn false (subst_in_eqn suit result) result ctx lrl rrl)
       else try
         do_proj t1.order n1 (result_kind k1 t1.nbargs) t1.args
       with Fail_match p ->
	 do_undo pos;
	 subraise path p;
         do_cst t1.order n1 t2.head t1.args t2.args)

   | ({head=UCst(n2,_); _} as t2), ({head=UVar(n1,k1); _} as t1) ->
       if !trace_pmatch then print_endline "cst-uvar";
       test_occur false n1 t2.args; (
       try if t1.nbargs = 0 then (
	 test_occur true n1 t2.args;
         let result,ctx = try subst_uvar n1 t2.allt result ctx
         with Fail_subst -> raise (Fail_match path) in
         fn false (subst_in_eqn suit result) result ctx lrl rrl)
       else try
         do_proj t1.order n1 (result_kind k1 t1.nbargs) t1.args
       with Fail_match p ->
	 do_undo pos;
	 subraise path p;
         do_cst t1.order n1 t2.head t1.args t2.args
       with Fail_match p ->
	 do_undo pos;
	 subraise path p;
	 do_csteq n2 t2.args t2.allt t1 true)

    | ({head=EAtom(o2,k2); _} as t2), ({head=UVar(n1,k1); _} as t1) -> (
	if !trace_pmatch then print_endline "eatom-uvar";
        test_occur false n1 t2.args;
        if t1.nbargs = 0 then (
          test_occur true n1 t2.args;
           let result,ctx = try subst_uvar n1 t2.allt result ctx
                            with Fail_subst -> raise (Fail_match path) in
           fn false (subst_in_eqn suit result) result ctx lrl rrl)
        else try
          do_proj t1.order n1 (result_kind k1 t1.nbargs) t1.args
        with Fail_match p -> try
	  do_undo pos;
	  subraise path p;
          do_cst t1.order n1 t2.head t1.args t2.args
        with Fail_match p when t1.args <> [] ->
	  do_undo pos;
	  subraise path p;
          do_def o2 k2 t2.args t1 true)

    | ({head=EAtom(o1,k1); _} as t1), ({head=UCst(n2,_); _} as t2) ->
	if !trace_pmatch then print_endline "eatom-cst";
        (try do_csteq n2 t2.args t2.allt t1 false
        with Fail_match p -> try
	  do_undo pos;
          subraise path p;
	  do_def o1 k1 t1.args t2 true
          with Fail_match p ->
	    do_undo pos;
	    subraise path p;
            tmap t1 t2 (Oneq o1) (Uneq n2))

    | ({head=UCst(n1,_); _} as t1), ({head=EAtom(o2,k2); _} as t2) ->
	if !trace_pmatch then print_endline "cst-eatom";
        (try do_csteq n1 t1.args t1.allt t2 true
        with Fail_match p -> try
	  do_undo pos;
	  subraise path p;
	  do_def o2 k2 t2.args t1 false
        with Fail_match p ->
	  do_undo pos;
	  subraise path p;
          tmap t1 t2 (Uneq n1) (Oneq o2))

    | {head=EAbs _ as u; _} as t1, ({head=UVar(n,_); _} as t2) ->
	if !trace_pmatch then print_endline "eabs-uvar";
        if t2.nbargs = 0 then (
           let result,ctx = try test_occur true n [t1.allt,t1.kind]; subst_uvar n t1.allt result ctx
                            with Fail_subst -> raise (Fail_match path) in
           fn false (subst_in_eqn suit result) result ctx lrl rrl)
        else
        let e2 = eta_expand result u t2.kind t2.nbargs t2.args in
        let result,ctx = try subst_uvar n e2 result ctx
                         with Fail_subst -> raise (Fail_match path) in
        fn false (subst_in_eqn eqns result) result ctx lrl rrl

    | {head=UVar(n,_); _} as t1, ({head=EAbs _ as u; _} as t2)  ->
	if !trace_pmatch then print_endline "uvar-eabs";
        if t1.nbargs = 0 then (
           let result,ctx = try test_occur true n [t2.allt,t2.kind]; subst_uvar n t2.allt result ctx
                            with Fail_subst -> raise (Fail_match path) in
           fn false (subst_in_eqn suit result) result ctx lrl rrl)
        else
        let e1 = eta_expand result u t1.kind t1.nbargs t1.args in
        let result,ctx = try subst_uvar n e1 result ctx
                         with Fail_subst -> raise (Fail_match path) in
        fn false (subst_in_eqn eqns result) result ctx lrl rrl

    | {head=EAbs(s1,e1,k1); _}, t2 ->
	if !trace_pmatch then print_endline "eabs-x";
        let e2 = EApp(lift t2.allt,EVar 0) in
        let env = k1::env in
        fn false (add_eqn result
                    (term_to_eqn e1 result env, term_to_eqn e2 result env,
           env, (PAbs (s1,k1)::path), insert, plvl, rec_open,
		     noeq) suit) result ctx lrl rrl

    | t1, {head=EAbs(s2,e2,k2); _} ->
	if !trace_pmatch then print_endline "x-eabs";
        let e1 = EApp(lift t1.allt,EVar 0) in
        let env = k2::env in
        fn false (add_eqn result
                    (term_to_eqn e1 result env, term_to_eqn e2 result env,
           env, (PAbs (s2,k2)::path), insert, plvl, rec_open,
		     noeq) suit) result ctx lrl rrl


    | ({head=EAtom(o1,k1); _} as t1), t2 ->
	if !trace_pmatch then print_endline "eatom-x";
        (try
           do_def o1 k1 t1.args t2 true
        with Fail_match p ->
	  do_undo pos;
	  subraise path p;
          tmap t1 t2 (Oneq o1) Alleq)

    | t1, ({head=EAtom(o2,k2); _} as t2) ->
	if !trace_pmatch then print_endline "x-eatom";
        (try
           do_def o2 k2 t2.args t1 false
        with Fail_match p ->
	  do_undo pos;
	  subraise path p;
          tmap t1 t2 Alleq (Oneq o2))

    | ({head=UCst(n1,_); _} as t1), t2 -> (
	if !trace_pmatch then print_endline "cst-x";
        try do_csteq n1 t1.args t1.allt t2 true
        with Fail_match p ->
	  do_undo pos;
          subraise path p;
	  tmap t1 t2 (Uneq n1) Alleq)

    | t1, ({head=UCst(n2,_); _} as t2) -> (
	if !trace_pmatch then print_endline "x-cst";
	try do_csteq n2 t2.args t2.allt t1 false
        with Fail_match p ->
	  do_undo pos;
          subraise path p;
	  tmap t1 t2 Alleq (Uneq n2))

    | ({head=UVar(n1,_); _} as t1), ({head=UVar(n2,_); _} as t2) ->
	if !trace_pmatch then print_endline "uvar-uvar";
        if t1.nbargs = 0 && n1 = n2 then
          fn false suit result ctx lrl rrl else
	if t1.nbargs = 0 && test_args t2.args then (
	  let result,ctx = try subst_uvar n2 (cste t1.allt t2.args) result ctx
	                   with Fail_subst -> raise (Fail_match path) in
          fn false (subst_in_eqn suit result) result ctx lrl rrl) else
	if t2.nbargs = 0 && test_args t1.args then (
	  let result,ctx = try subst_uvar n1 (cste t2.allt t1.args) result ctx
	                   with Fail_subst -> raise (Fail_match path) in
          fn false (subst_in_eqn suit result) result ctx lrl rrl) else (
        test_occur false n1 t2.args;
        test_occur false n2 t1.args;
        if t1.nbargs = 0 && (t2.nbargs <> 0 || n2 > 0)
        then (
          test_occur true n1 t2.args;
          let result,ctx = try subst_uvar n1 t2.allt result ctx
                           with Fail_subst -> raise (Fail_match path) in
          fn false (subst_in_eqn suit result) result ctx lrl rrl)
        else if t2.nbargs = 0
        then (
          test_occur true n2 t1.args;
          let result,ctx = try subst_uvar n2 t1.allt result ctx
                           with Fail_subst -> raise (Fail_match path) in
          fn false (subst_in_eqn suit result) result ctx lrl rrl)
        else
          let nst = {sref = -1; rule = No_rule; next = Fin (new_fin ())} in
          let found = ref false in
          let jn = function
            t1,t2,kl,pl,None,plvl,rec_open,noeq -> found:=true; t1,t2,kl,pl,Some nst,plvl,rec_open,noeq
          | x -> x
          in
          let eqns = List.map jn eqns in
          let rwt = if !found then rev_path rrl@(Insert nst::lrl)
                              else rev_path rrl@lrl in
          result,ctx,rwt,eqns)

    | _ ->
	if !trace_pmatch then print_endline "x-x";
	do_undo pos; raise (Fail_match path)


  in

  try fn false eqns result ctx lrl rrl, call_trivial
  with Fail_match _ | Fast_exit _ ->

    let f (_,(_,d ,_),_,_,_,_,_,_,_,_,_,path ,_,_,_,_)
          (_,(_,d',_),_,_,_,_,_,_,_,_,_,path',_,_,_,_) =
      if d < d' then -1 else
        if d = d' && sublist (List.rev path) (List.rev path') then -1
      else 1
    in
    let l = List.sort f !eqt in

    let rec gn n l = match n,l with
        _, [] -> raise (Fail_match the_path)
      | 0, _ -> raise (Fail_match the_path)
      | n, ((dir,(lf,d2,keq),(_,e1,e2,nl,k,_,eqtl),lrl,rrl,
            t1,t2,suit,result,ctx,env,path,insert,plvl,rec_open,
            (op,lvl,inl,inr))::l) ->

      let frtr =
	let { eqflvl = eqflvl; _ }, _ , _ = call_trivial in
        if d2+.aug<0.0 then (eqflvl,0.0) else
          if flvl = 0 then raise (Fail_match path) else (flvl-1,d2+.aug)
      in
      let call_trivial, restore_gst = match insert with
        None | Some {rule = No_rule; _} -> call_trivial, (fun x -> x)
      | Some ({rule = In_rule (glc,stc); _} as str) ->
          let tri, f, (gl0,st0,nl) = call_trivial in
              (tri, f, (glc,stc.next,nl)),
                (function tri,f,(gl1,st1,nl) ->
                     str.rule <- In_rule (gl1,stc);
                     stc.next <- st1;
                     tri,f,(gl0,st0,nl))
      | _ -> failwith "bug3 in restore_gst"
      in
      let (pathd,largs,t',t'') =
	try
	  List.iter2 (fun k k' ->
	    if not (equal_kind k k') then raise Fail_saturate)
	    (match (head_kind (if dir then t1 else t2).head) with _,_,k -> k)
	    (match (head_kind e1) with _,_,k -> k);
	  saturate e1 e2 nl k keq env
	with
	  Fail_saturate ->  raise (Fail_match the_path)
      in
      let nbargs = List.length largs - 1 in
      let nlvl = if d2>=0.0 then lvl/7 else lvl/2 in


      let apply_eqn call_trivial contxt eqnth perm andpath ld =
        let tri, triv, ctriv, goal_state =
          let tri, triv, goal_state = call_trivial in
            let tri' = { nlim = tri.nlim - 1;
                         eqlvl = nlvl/10;
                         from_trivial = true;
                         first_order = true;
		         auto_elim = tri.auto_elim && not tri.from_trivial;
		         eqflvl = tri.eqflvl
		       } in
            tri, triv, triv tri', goal_state
        in
        let e, st0 = match eqnth with
          Eq_theo o -> (
            match get_value o with
              Def (EApp(EApp(EAtom(ot,_),e),_)) when ot == theorem_obj ->
                let sref = new_ref () in
                e, {sref = sref; rule = Theo (aobj o); next = Fin (new_fin ())}
            | _ -> failwith "bug 0 in apply_eqn")
        | Eq_axiom (e,n) ->
            let sref = new_ref () in
            e, {sref = sref; rule = Axiom n; next = Fin (new_fin ())}
        | Eq_subgoal (e,n) ->
            let sref = new_ref () in
            e, {sref = sref; rule = Subgoal n; next = Fin (new_fin ())}
        in
        let rec fn delayed gst contxt acc st0 perm andpath = function
          EApp(EAtom(o,_),(EAbs(_,_,k) as e)) when
              o == forall_obj ->
            let sref = new_ref () in
            let pos, nperm = match perm with
              [] -> failwith "bug 2 in apply_eqn"
            | pos::nperm -> pos, nperm
            in
            let es =
	      fst (List.nth largs (nbargs - pos))
	    in
            let st1 = {sref = sref; rule = Forall_elim (es,k);
                           next = Fin (new_fin ())} in
            st0.next <- Fol st1;
            fn delayed gst contxt acc st1
               nperm andpath (norm_lsexpr result e [es])
        | EApp(EApp(EAtom(o,_),e1),e2) when o == arrow_obj ->
            let ref1 = new_ref () and ref2 = new_ref () in
            let st2 = {sref = ref2; rule = Arrow_elim(st0.sref, ref1);
                       next = Fin (new_fin ())} in
            st0.next <- Fol st2;
            let delayed, (contxt, goal_state) =
              let (subst,ctx,rem,nonu) = contxt in
              if has_uvar subst e1 then begin
                (ref1, (Fol st2), e1)::delayed, (contxt, gst)
              end else begin
                let subst,(ctx,nonu),chg =
                  try has_neg subst (ctx, nonu) e1
                  with Fail_subst -> raise (Fail_match path) in
                let e1 = if chg then norm_lexpr subst e1 else e1 in
                push_adone ();
		push_dm ();
                try
		  no_match := true;
                  let r =
                    delayed,
                    ctriv (subst,ctx,rem,nonu) gst [ref1, (Fol st2), e1] in
                  pop_adone (); pop_dm (); r
                  with e -> pop_adone (); pop_dm (); raise e
              end
            in
            fn delayed goal_state contxt acc st2 perm andpath e2
       | EApp(EApp(EAtom(o,_),e1),e2) when o == !and_obj ->
           let ref3 = new_ref () in
           let b, nandpath = match andpath with
             [] -> failwith "bug 5 in apply_eqn"
           | b::l -> b,l in
           let st4 = {sref = new_ref ();
                      rule = Arrow_elim (ref3,st0.sref);
                      next = Fin (new_fin ())} in
           let st3 = {sref = ref3;
                      rule = Forall_elim (e2,kForm);
                      next = Fol st4} in
           let st2 = {sref = new_ref ();
                      rule = Forall_elim (e1,kForm);
                      next = Fol st3} in
           let st1 = {sref = new_ref ();
                      rule = Theo (match b with
			Left_and -> aobj !and_elim_l_obj
                      | Right_and -> aobj !and_elim_r_obj
		      | _ ->	failwith "bug path in apply_eqn");
                      next = Fol st2} in
           st0.next <- Fol st4;
           fn delayed gst contxt (Fol st1::acc) st4 perm
             nandpath (match b with
	       Left_and -> e1 | Right_and -> e2 | _ ->
		 failwith "bug path in apply_eqn")
       | EApp(EApp(EAtom(o,_),e1),e2) when o == equal_obj ->
	   (if ld then e1,e2 else e2,e1),st0, acc,
	   contxt, gst, delayed, pathd (* path_diff (List.hd keq) t1.kind *)
       | e ->
	   let nandpath = match andpath with
             Open_def::l -> l
	   |  _ -> failwith "bug path 2 in apply_eqn" in
	   let (f, o, k, u) = decom false e in
	   match f with
	     None -> failwith "bug path 3 in apply_eqn"
	   | Some f ->
	       let e = EAtom(o,k) in
               let akind, fe = build_subterm o k u in
               let ne = norm_expr (EApp(fe,f)) in
	       let st1 =
		 if (Data_base.Object.get_value o).origin = Local_hyp then
		   st0
		 else
		   let path = List.map (fun _ -> LApp) u in
		   let rl = Devl_def (Path(path, e), akind) in
		   let st =
		     {sref = new_ref (); rule = rl; next = Fin (new_fin ())} in
		   st0.next <- Fol st;
		   st
               in
	       fn delayed gst contxt acc st1 perm nandpath ne
        in
        let (e1,e2), st, acc, contxt, gst, delayed, pathd =
          fn [] goal_state contxt [] st0 perm andpath e in
	let context =
	  EAbs("x",List.fold_left (fun t (u,_) -> EApp(t,u))
		 (EVar 0) (List.map (fun (e,t) -> (lift e,t))
                   (last_in_list pathd
		    (List.rev largs))),
	       mk_Var ()) in
        (if lf then
	  Req(path, context, insert, e1, e2, st, ((Fol st0)::acc),ld)
        else
	  Req(path, context, insert, e2, e1, st, ((Fol st0)::acc), not ld)),
        contxt, (tri, triv, gst), delayed
      in

      let do_delayed call_trivial contxt delayed =
        if delayed = [] then contxt, call_trivial else
        let tri, triv, ctriv, goal_state =
          let tri, triv, goal_state = call_trivial in
            let tri' = { nlim = tri.nlim - 1;
                         eqlvl = nlvl/10;
                         from_trivial = true;
                         first_order = true;
		         auto_elim = tri.auto_elim && not tri.from_trivial;
			 eqflvl = tri.eqflvl
		       } in
            tri, triv, triv tri', goal_state
        in
        let fn (subst,ctx,rem,nonu) gst las =
          let treat (ref1, st2, e1) (las,subst,ctx,nonu) =
            let subst,(ctx,nonu),chg =
              try has_neg subst (ctx,nonu) e1
              with Fail_subst -> raise (Fail_match path) in
            let e1 = if chg then norm_lexpr subst e1 else e1 in
            let s = depth_uvar subst e1 in
            ((s, (ref1, st2, e1))::las),subst,ctx,nonu
          in
          let las,subst,ctx,nonu =
            List.fold_right treat las ([],subst,ctx,nonu) in
          let las = List.sort (fun (s,_) (s',_) -> if s > s' then -1 else 1) las in
          let las = List.map snd las in
          push_adone ();
	  push_dm ();
          try
	    no_match := true;
            let r = ctriv (subst,ctx,rem,nonu) gst las in
            pop_adone (); pop_dm (); r
          with e -> pop_adone (); pop_dm (); raise e

        in
          let contxt, gst =
            fn contxt goal_state delayed in
          contxt, (tri, triv, gst)
      in
      let ptr = ref false in

      let bucket = badd_adone (result,t1.allt,t2.allt) lvl in
(*
      print_string "adding to adone";
      print_expr_tr (norm_lexpr result t1.allt); print_string " ";
      print_expr_tr (norm_lexpr result t2.allt); print_string " ";
      print_int lvl; print_newline ();
*)
      try
        let t0' = norm_expr t' and t0'' = norm_expr t'' in
        let t1,t2,t0',t0'',ninr = match dir,lf with
          true, true -> t1,t2,t0',t0'',inr
        | true, false -> t2,t1,t0'',t0',inl
        | false, true -> t2,t1,t0',t0'',inl
        | false, false -> t1,t2,t0'',t0',inr
        in

        test_hash path t1.allt t0' result lvl;

if !trace_pmatch then begin
        print_string "try equations ";
        print_int lvl; print_string " ";
        print_float d2; print_string " ";
        List.iter (function eq,_,_,_,_,_ -> print_eq eq) eqtl; print_string " : ";
        print_expr_tr t0'; print_string " = ";
        print_expr_tr t0''; print_newline ()
end;

        let noeq = (Some path,nlvl,false,true) in
        let t' = term_to_eqn t0' result env in
        let eq' = t1, t', env, path, insert, plvl, rec_open, noeq in
        let (subst,ctx,rules,rem), call_trivial =
          fneq frtr call_trivial path [eq'] result ctx [] [] in

        let nlvl = if d2>=0.0 then lvl/7 else lvl-(count_eq rules)-1 in
        test_hash path t0'' t2.allt subst nlvl;
        let t'' = term_to_eqn t0'' result env in

if !trace_pmatch then begin
        print_int lvl; print_string " ";
        print_endline "equation applies ..."
end;

        let rec try_eqtl = function
          [] -> raise Exit
        | (eqth,perm,andpath,ld,_,_)::eqtl ->
          try apply_eqn call_trivial (subst, fst ctx, [], snd ctx)
                        eqth perm andpath ld
          with Ill_rule _ -> try_eqtl eqtl
        in
        let eqr, (subst,ctx,rem',nonu),
            call_trivial, delayed = try_eqtl eqtl in
        let ctx = ctx,nonu in

        let eq = if dir = lf then
           t'', t2, env, path,insert,plvl,rec_open,
           (op,nlvl,not lf && has_uvar subst t''.allt,ninr)
        else
           t2, t'', env, path,insert,plvl,rec_open,
           (op,nlvl,ninr, not lf && has_uvar subst t''.allt) in
        let eqns = subst_in_eqn (add_eqn result eq rem) subst in
        let eqns = List.fold_left (fun rem eq -> add_eqn subst eq rem)
                                 eqns rem' in
        let nlrl, nrrl = if dir = lf then (eqr::rules), []
                                     else [], (eqr::rules) in
        ptr:=true;
        let (nsubst,nctx,nrules,rem), call_trivial =
          fneq frtr call_trivial path eqns subst ctx nlrl nrrl
        in

        let (nsubst,nctx,rem,nonu), call_trivial =
          try do_delayed call_trivial (nsubst,fst nctx,rem, snd nctx) delayed
          with Ill_rule _ -> raise Exit
        in
        let call_trivial = restore_gst call_trivial in
        let nctx = nctx,nonu in

        fast_remove_adone bucket;
(*
        print_string "succeed : ";
        print_expr_tr (norm_lexpr nsubst t1'); print_string " = ";
        print_expr_tr (norm_lexpr nsubst t2'); print_string " at level ";
        print_int lvl; print_newline ();
*)
        fneq frtr call_trivial the_path
          (subst_in_eqn (suit@rem) nsubst) nsubst nctx (nrules@lrl) rrl
      with
        Fail_match p ->
          subraise path p;
          let n = if !ptr then n-1 else n in
          gn n l
      | Exit -> gn n l

    in gn !eqbreadth l

let pmatch leqn loc inl inr call_trivial e1 e2 =
  let pos = get_undo_pos () in
  let v = type_check e1 in
  type_strong e2 v;
  if !trace_pmatch then begin
    open_hvbox 0;
    print_expr_tr e1;
    print_string " ="; print_break 1 2;
    print_expr_tr e2;
    print_newline ()
  end;
  push_dm ();
  did_match := false; muvar:=get_uvar (); mvvar:=get_vvar();
  let (r,u,m,l) = get_ulocal () in
  let sgetrwt = !getrwt in
  getrwt := build_getrwt leqn;
  let smatch_local = !match_local in
  match_local := loc;
  let {eqlvl = lvl; eqflvl = eqflvl; _}, _, _ = call_trivial in
  let (subst,(ctx,nonu),rwt,rem),calt  = try
    fneq (eqflvl, 0.0) call_trivial []
         ((term_to_eqn e1 r [], term_to_eqn e2 r [],[],[],None,!eqplvl,
         ([],[]),(None,lvl,inl,inr))::m) r (u,l) [] []
    with
      Fail_match _ ->
        pop_dm ();
	do_undo pos;
        clear_adone !adone;
	getrwt := sgetrwt;
    	match_local := smatch_local;
        if !trace_pmatch then print_endline "failed";
        raise Fail_matching
      | e ->
	  pop_dm (); do_undo pos;
	  clear_adone !adone; getrwt := sgetrwt; raise e
  in
    let dm = !did_match in
    pop_dm ();
    set_ulocal (subst,ctx,rem,nonu);
    clear_adone !adone;
    getrwt := sgetrwt;
    match_local := smatch_local;
    if !trace_pmatch then print_endline "succeed";
    let _,_,gst = calt in
    (dm, rwt,gst)

let smatch loc e1 e2 =
  let pos = get_undo_pos () in
  let v = type_check e1 in
  type_strong e2 v;
  if !trace_pmatch then begin
    open_hvbox 0;
    print_expr_tr e1;
    print_string " ="; print_break 1 2;
    print_expr_tr e2;
    print_newline ()
  end;
  push_dm ();
  did_match := false; muvar:=get_uvar (); mvvar:=get_vvar();
  let (r,u,m,l) = get_ulocal () in
  let sgetrwt = !getrwt in
  getrwt := (fun _ -> []);
  let smatch_local = !match_local in
  match_local := loc;
  let (subst,(ctx,nonu),rwt,rem),_  = try
    fneq (0,0.0) deftri [] ((term_to_eqn e1 r [], term_to_eqn e2 r [],[],[],
			   None,!eqplvl,([],[]),(None,0,false,false))::m) r (u,l) [] []
    with
      Fail_match _ ->
         pop_dm ();
	 do_undo pos;
         getrwt := sgetrwt;
    	 match_local := smatch_local;
         clear_adone !adone;
         if !trace_pmatch then print_endline "failed";
         raise Fail_matching
    | e -> pop_dm (); do_undo pos;clear_adone !adone; getrwt := sgetrwt; raise e
  in
  let dm = !did_match in
  pop_dm ();
  set_ulocal (subst,ctx,rem,nonu);
  getrwt := sgetrwt;
  match_local := smatch_local;
  clear_adone !adone;
  if !trace_pmatch then print_endline "succeed";
  (dm, rwt)

let smatch_env loc e1 e2 env =
  if !trace_pmatch then begin
    open_hvbox 0;
    print_expr_tr e1;
    print_string " ="; print_break 1 2;
    print_expr_tr e2;
    print_newline ()
  end;
  let (r,u,m,l) = get_ulocal () in
  let pos = get_undo_pos () in
  let sgetrwt = !getrwt in
  push_dm ();
  did_match := false; muvar:=get_uvar (); mvvar:=get_vvar();
  getrwt := (fun _ -> []);
  let smatch_local = !match_local in
  match_local := loc;
  let (subst,(ctx,nonu),rwt,rem),_  = try
    fneq (0,0.0) deftri []
         ((term_to_eqn e1 r env, term_to_eqn e2 r env,env,[],None,!eqplvl,
    ([],[]),(None,0,false,false))::m) r (u,l) [] []
    with
      Fail_match _ ->
         pop_dm ();
	 getrwt := sgetrwt;
	 do_undo pos;
    	 match_local := smatch_local;
         clear_adone !adone;
         if !trace_pmatch then print_endline "failed";
         raise Fail_matching
    | e -> pop_dm (); do_undo pos;clear_adone !adone; getrwt := sgetrwt; raise e
  in
  let dm = !did_match in
  pop_dm ();
  set_ulocal (subst,ctx,rem,nonu);
  getrwt := sgetrwt;
  match_local := smatch_local;
  clear_adone !adone;
  if !trace_pmatch then print_endline "succeed";
  (dm, rwt)

let umatch leqn loc e1 e2 =
  let pos = get_undo_pos () in
  let v = type_check e1 in
  type_strong e2 v;
  if !trace_pmatch then begin
    open_hvbox 0;
    print_expr_tr e1;
    print_string " ="; print_break 1 2;
    print_expr_tr e2;
    print_newline ()
  end;
  push_dm ();
  did_match := false; muvar:=get_uvar (); mvvar:=get_vvar();
  let (r,u,m,l) = get_ulocal () in
  let sgetrwt = !getrwt in
  getrwt := build_getrwt leqn;
  let smatch_local = !match_local in
  match_local := loc;
  let conditions = ref [] in
  let call_trivial =
    {nlim = 0; eqlvl = !Flags.eqdepth; from_trivial = true; first_order = false;
     auto_elim = false; eqflvl = !Flags.eqflvl},
    (fun _ ctxt ll ng ->
      conditions := (List.map (fun (_,_,e) -> e) ng) @ !conditions;
      ctxt, ll),
    (defgoal,Fin 0,[])
  in
  let (subst,(ctx,nonu),_,rem),_  = try
    fneq (!Flags.eqflvl, 0.0) call_trivial []
      ((term_to_eqn e1 r [], term_to_eqn e2 r [],[],[],None,!eqplvl,
        ([],[]),(None,!Flags.eqflvl,false,false))::m) r (u,l) [] []
    with
      Fail_match _ ->
         pop_dm ();
	 do_undo pos;
         getrwt := sgetrwt;
    	 match_local := smatch_local;
         clear_adone !adone;
         if !trace_pmatch then print_endline "failed";
         raise Fail_matching
    | e -> pop_dm (); do_undo pos;clear_adone !adone; getrwt := sgetrwt; raise e
  in
  pop_dm ();
  set_ulocal (subst,ctx,rem,nonu);
  getrwt := sgetrwt;
  match_local := smatch_local;
  clear_adone !adone;
  if !trace_pmatch then print_endline "succeed";
  !conditions

let dist loc t1 t2 =
  let smatch_local = !match_local in
  let save_no_match = !no_match in
  try
    match_local := loc;
    no_match := true;
    let result, ctx, _, nonu = get_ulocal () in
    let r = distance result (ctx,nonu) [] t1 t2 in
    match_local := smatch_local;
    no_match := save_no_match;
    r
  with e ->
    match_local := smatch_local;
    no_match := save_no_match;
    raise e


let dist2 loc t1 t2 t3 t4 =
  let smatch_local = !match_local in
  let save_no_match = !no_match in
  try
    match_local := loc;
    no_match := true;
    let result, ctx, _, nonu = get_ulocal () in
    let _, r, _ = distance2 0.0 result (ctx,nonu) [] t1 t2 t3 t4 in
    match_local := smatch_local;
    no_match := save_no_match;
    r
  with e ->
    match_local := smatch_local;
    no_match := save_no_match;
    raise e
