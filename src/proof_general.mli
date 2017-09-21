(* $State: Exp $ $Date: 2006/02/24 17:01:54 $ $Revision: 1.5 $ *)
(*######################################################*)
(*			proof_general.mli		*)
(*######################################################*)

val is_definition : int -> string -> unit
val is_equation : int -> string -> unit
val is_hypothesis : int -> string -> unit
val is_locked : int -> unit

val menu_intro : int -> string list -> int
val menu_evaluate : int -> int
val menu_evaluate_hyp : int -> string -> int
val menu_left : string -> int -> int
val menu_elim : string -> int -> int
val menu_apply : string -> string list -> int -> int
val menu_rewrite : string list -> int -> int
val menu_rewrite_hyp : string -> string list -> int -> int
