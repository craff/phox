(* $State: Exp $ $Date: 2004/11/22 13:38:04 $ $Revision: 1.11 $ *)
(*######################################################*)
(*			local.mli			*)
(*######################################################*)

open Type
open Type.Base

exception Fail_propagate

module Exprmap : Map.S with type key = expr
module Exprset : Set.S with type elt = expr

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

(* unification context *)

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
      expr Map.t          (* value of unified variables *)
    * Set.t Map.t    (* skolem constraints associate to the variable number $n$ the set of numbers the variable can not use *)
    * eqn list    (* high order unification constraints (flex-flex equations) *)
    * nonunifs list (* list of pairs of terms that must not unify *)

exception Non_unif


val add_local : local_defs -> string -> expr -> local_defs
val find_local : string -> expr
val is_local : string -> bool
val cst_local : int -> string
val real_local_add : local_defs -> string -> symbol -> local_defs * obj
val add_local_tex : local_defs -> obj -> string -> syntax -> local_defs
val add_local_ctex : local_defs -> int -> string -> syntax -> local_defs
val add_local_close : local_defs -> obj -> local_defs
val remove_local_cst : local_defs -> string list -> int list -> local_defs
val rename_local_cst : local_defs -> string -> string -> local_defs
val rename_caps_def : local_defs -> string -> string -> local_defs
val add_cst_eq : local_defs -> int -> expr ->
	(int * expr * expr * bool * bool) list -> local_defs

val set_ulocal : contxt -> unit
val get_ulocal : unit -> contxt
val singl : int -> Set.t
val add_skolem : int -> Set.t -> contxt -> contxt
val getuvar : int -> expr
val propagate : expr Map.t -> Set.t Map.t -> Set.t -> expr ->  Set.t Map.t
val update_nonunifs : int -> expr Map.t -> nonunifs list -> nonunifs list
val add_non_unif : (int * int) option -> (expr * expr) list -> unit
val print_nonunifs : expr Map.t -> nonunifs list -> unit

val new_const : unit -> int
val new_uvar : unit -> int
val new_vvar : unit -> int
val new_ivar : int -> expr
val def_uvar : int -> expr -> unit
val get_uvar : unit -> int
val get_vvar : unit -> int

val vvar_count : int ref
val vvar_kind : (int * kind) list ref
val reset_local : unit -> unit
val fadd_to_tbl :  (expr Map.t -> (int * int) option -> nonunifs ->
                    expr -> expr -> nonunifs) ref

val fcmp_expr : (expr -> expr -> int) ref
val ulocal_defs : (Type.expr Basic.Map.t * Basic.Set.t Basic.Map.t * eqn list *
     (Type.expr * Type.expr) list Basic.Map.t list) ref

val name_uvar : int -> string -> unit
val get_uvar_name : int -> string
val get_uvar_by_name : string -> int
