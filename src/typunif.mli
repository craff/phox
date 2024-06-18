(* $State: Exp $ $Date: 2002/06/20 12:04:39 $ $Revision: 1.2 $ *)
(*######################################################*)
(*			typunif.mli			*)
(*######################################################*)


open Type

exception Clash
exception Type_Clash of expr * kind * kind * string list

val norm : kind -> kind
val norm2 : kind -> kind

val kind_subst : kind list -> kind -> kind
val kind_subst_expr : kind list -> expr -> expr

(* unification of two kinds *)
val unif : kind -> kind -> unit           (* raise clash when it fails *)
val equal_kind : kind -> kind -> bool  (* returns false when unif fails *)
val filter_arrow : kind -> kind * kind

(* for private use in typing.ml *)
val unify : expr -> string list -> kind -> kind -> unit
