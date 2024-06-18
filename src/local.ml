(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.13 $ *)
(*######################################################*)
(*			local.ml			*)
(*######################################################*)

open Format
open Type
open Type.Base
open Data_base
open Undo

exception Fail_propagate

let fcmp_expr =
  (ref (fun _ -> failwith "fcmp_expr not ready") : (expr -> expr -> int) ref)

module Expr_order = struct
  type t = expr
  let compare e1 e2 = !fcmp_expr e1 e2
end

module Exprmap = Map.Make (Expr_order)
module Exprset = Set.Make (Expr_order)

open Basic

type adone = expr list * expr list * int Exprmap.t

type state_c =
  { mutable sref : int; mutable rule : rule; mutable next : state}

and rule =
  Axiom of int
| Subgoal of int
| No_rule
| In_rule of (goal * state_c)
| Arrow_intro of string * int * expr
| Arrow_elim of int * int
| Forall_intro of string * int * kind
| Forall_elim of expr * kind
| Cut_rule of string * int * int * int
| Fact_def of expr * expr * kind
| Devl_def of expr * kind
| Lr_eqn of path list * expr * int * int
| Rl_eqn of path list * expr * int * int
| Decl_local_def of string * obj
| Theo of expr
| Comment of string
| Claim of expr

and state =
  Fin of int
| Fol of state_c

and hyp_state =
  Not_eq
| An_eq
| Dont_know of eqpath list list

and hyp_kind =
  Hypo
| Theor of expr
| Subg

and leqns = (pos_eq * eqns) list

and rules = af2_obj list

and hyp_type =
  (string * (expr * int * hyp_kind * hyp_state * (bool * rules))) list

and goal =
  { mutable gref : int;
    mutable hyp : hyp_type;
    concl : expr;
    oldhyp : hyp_type;
    eqns : leqns;
    local : local_defs;
    mutable ax_test : bool;
    mutable left_test : bool;
    mutable done_list : adone }

type rig = {head : expr;
            args : (expr * kind) list;
            nbargs : int;
            order : int;
	    kind : kind;
            allt : expr}

type eqn = rig * rig * kind list * path list * state_c option * int *
      (af2_obj list * af2_obj list) *
	   (path list option * int * bool * bool)

type nonunifs =
         (expr * expr) list Map.t

type contxt =
         expr Map.t          (* unified variables *)
       * Set.t Map.t    (* skolem constraints *)
       * eqn list    (* high order unification constraints *)
       * nonunifs list

(* local definitions *)

let add_local ld s c =
  { ld with cst_def = (s,c)::ld.cst_def }

let find_local s =
  List.assoc s !cur_local.cst_def

let is_local s =
  List.mem_assoc s !cur_local.cst_def ||
  List.mem_assoc s !cur_local.caps_def

let cst_local p =
  let rec look_for = function
    [] -> raise Not_found
  | (s,UCst(q,_))::l -> if q = p then s else look_for l
  | _::l -> look_for l in
  look_for !cur_local.cst_def

let real_local_add ld name o =
  let gen = List.length ld.caps_def in
  let r = capsule_object name o gen in
  { ld with caps_def = (name, r)::ld.caps_def }, r

let add_local_tex ld o name sy =
  { ld with local_tex_tbl = (o,(name,sy))::ld.local_tex_tbl }

let add_local_ctex ld n name sy =
  { ld with local_ctex_tbl = (n,(name,sy))::ld.local_ctex_tbl }

let add_local_close ld o =
  { ld with local_close_tbl = o::ld.local_close_tbl }

let remove_local_cst ld names hyps =
  { ld with cst_def = select (fun (n,_) -> not (List.mem n names)) ld.cst_def;
    caps_def = select (fun (n,_) -> not (List.mem n names)) ld.caps_def;
    cst_eq = select (fun (_,(_,l)) -> not (List.exists (fun (n,_,_,_,_) -> List.mem n hyps) l)) ld.cst_eq }

let rename_local_cst ld oname nname =
  let find = ref 0 in
  let res = { ld with
    cst_def =
      List.map (fun (n,t as c) ->
        if n = oname then (incr find; nname,t) else c) ld.cst_def}
  in
  if !find = 0 then raise Not_found else res

let rename_caps_def ld oname nname =
  let find = ref 0 in
  let res = { ld with
    caps_def =
      List.map (fun (n,o as c) ->
        if n = oname then begin
	  incr find;
	  let undo = sym_rename_undoable o nname in
	  add_to_undo undo;
	  nname, o
	end else c) ld.caps_def}
  in
  if !find = 0 then raise Not_found else res

let add_cst_eq ld num_cst e leq =
  { ld with cst_eq = (num_cst,(e,leq))::ld.cst_eq  }

(* unification context *)

let ulocal_defs = ref
      (Map.empty, Map.empty, [], [])

let cst_count = ref 1
let uvar_count = ref (-1)
let vvar_count = ref 1
let vvar_kind = ref []
let uvar_names = ref []

let new_const () = let r = !cst_count in cst_count:=r+1;r
let new_uvar () = let r = !uvar_count in uvar_count:=r-1;r
let new_vvar () = let r = !vvar_count in vvar_count:=r+1;r
let new_ivar n =
  if n < 0 then
    UVar(n, mk_Var ())
  else if n < !vvar_count then
    UVar(n, List.assoc n !vvar_kind)
  else begin
    let n = new_vvar () in
    let k = mk_Var () in
    vvar_kind := (n,k)::!vvar_kind;
    UVar(n,k)
  end

let get_uvar () = !uvar_count
let get_vvar () = !vvar_count
let name_uvar n name = uvar_names := (n,name)::!uvar_names

let get_uvar_name n = List.assoc n !uvar_names
let get_uvar_by_name name = cossa name !uvar_names

let set_ulocal l = ulocal_defs := l
let get_ulocal () = !ulocal_defs

let update n s map =
  Map.add n s map

let singl a =
  Set.add a Set.empty

let add_skolem n s (r,sk,m,l) =
  try
    (r,update n (Set.union s (Map.find n sk)) sk ,m, l)
  with
    Not_found -> (r,Map.add n s sk,m,l)

let reset_local () =
  ulocal_defs := Map.empty, Map.empty, [], [];
  cst_count := 1;
  uvar_count := -1;
  vvar_count := 1;
  vvar_kind := [];
  uvar_names := []

let getuvar n =
  let (u,_,_,_) = !ulocal_defs in Map.find n u

let add_skolem' n s sk =
  try
    update n (Set.union s (Map.find n sk)) sk
  with
    Not_found -> Map.add n s sk

let propagate res sk s t =
  let rec g sk d = function
    EAtom(o,_) -> (
      match (Object.get_value o).fvalue with
        Def e -> if is_capsule o then g sk d e else sk
      | Prg e -> g sk d e
      | _ -> sk)
  | Path (path,e)  -> g sk (d + path_count path) e
  | UCst(p,_) -> if Set.mem p s then raise Fail_propagate else sk
  | EApp (t,t') -> g (g sk d t') d t
  | EAbs (_,t,_) -> g sk (d+1) t
  | UVar (n',_)  -> (try g sk d (Map.find n' res)
                    with Not_found -> add_skolem' n' s sk)
  | _ -> sk
  in g sk 0 t

let fadd_to_tbl = ref (fun _ -> raise Exit)

exception Non_unif

let print_nonunifs ctxt l =
  print_endline "non unif =";
  List.iter (fun tbl ->
    print_endline "[";
    Map.iter (fun n l ->
      print_string "constraint on ";
      print_int n;
      print_newline ();
      List.iter (fun (e1,e2) ->
                   !fprint_expr ctxt e1;
                   print_string " <> ";
		   !fprint_expr ctxt e2;
		   print_newline ()) l) tbl;
    print_endline "]") l

let update_nonunifs n ctxt l =
  List.fold_left (fun l tbl ->
    try
      let lc = Map.find n tbl in
      let tbl = Map.remove n tbl in
      let tbl = List.fold_left
        (fun tbl (e1,e2) ->
           !fadd_to_tbl ctxt None tbl e1 e2) tbl lc in
      let empty = ref true in
      (try Map.iter (fun _ _ -> empty := false; raise Exit) tbl
       with Exit -> ());
      if !empty then raise Non_unif;
      tbl::l
    with
      Not_found -> tbl::l
    | Exit -> l
  ) [] l

let add_non_unif maxvar als =
  let (r,u,m,l) = !ulocal_defs in
  try
    let nl =
      List.fold_left (fun nl (e1,e2) ->
                         !fadd_to_tbl r maxvar nl e1 e2)
                     Map.empty als in
    let empty = ref true in
    (try Map.iter (fun _ _ -> empty := false; raise Exit) nl
     with Exit -> ());
    if !empty then raise Non_unif;
    ulocal_defs := (r,u,m,(nl::l));
  with Exit -> ()

let def_uvar n t =
  let (r,u,m,l) = !ulocal_defs in
  let u =
    try
      let s = Map.find n u in
      propagate r u s t
    with
      Fail_propagate -> raise (Failure "bug in def_uvar")
    | Not_found -> u
  in
  let r = Map.add n t r in
  let l = update_nonunifs n r l in
  ulocal_defs := (r,u,m,l)
