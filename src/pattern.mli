(* $State: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.8 $ *)

(*######################################################*)
(*			pattern.mli			*)
(*######################################################*)

open Data_base
open Types
open Local
open Basic

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
| Rdef of path list * state_c option * af2_obj * kind list * expr list * bool
| Insert of Local.state_c

val reset_ref : unit -> unit
val new_ref : unit -> int
val reset_fin : unit -> unit
val new_fin : unit -> int

type goal_state = goal * state * state list

val print_ctx : unit -> unit

val count_eq : rrule list -> int

val rev_path : rrule list -> rrule list

val pmatch : (pos_eq * eqns) list -> 
	     local_defs ->
             bool -> bool ->
             (trinfo * 
                (trinfo -> contxt -> goal_state -> 
                   (int * state * expr) list -> contxt * goal_state) * 
                goal_state) ->
             expr -> expr -> bool * rrule list * goal_state

val smatch : local_defs -> expr -> expr -> bool * rrule list

val umatch : (pos_eq * eqns) list -> local_defs -> expr -> expr -> expr list

val smatch_env : local_defs -> expr -> expr -> kind list -> bool * rrule list

val dist : local_defs -> expr -> expr -> float

val dist2 : local_defs -> expr -> expr -> expr -> expr -> float

val reset_dm : unit -> unit

val push_dm : unit -> unit

val pop_dm : unit -> unit

val no_match : bool ref

val nomatch_set : Set.t ref

val reset_nomatch_set : unit -> unit
