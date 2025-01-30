(*######################################################*)
(*			rewrite.mli			*)
(*######################################################*)

open Type
open Pattern
open Interact

type rewrite_opt =
  Ad_lib
| Once_path of path list
| Once_ipath of int list
| Once_nth of int
| Lim of int
| Until of expr
| Ortho of path list list

val rule_rewrite : trinfo -> (bool * bool * af2_obj) list ->
  rewrite_opt -> bool -> bool -> arule

val rule_rewrite_hyp : trinfo -> (bool * bool * af2_obj) list ->
  string -> rewrite_opt -> bool -> bool -> arule

val make_th_list : string -> af2_obj list -> bool -> unit
