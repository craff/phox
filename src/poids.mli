(* $State: Exp $ $Date: 2004/05/24 08:23:24 $ $Revision: 1.5 $ *)
(*######################################################*)
(*			poids.mli                       *)
(*######################################################*)

open Types

val initweight : weight

val more_than_max_weight : weight -> bool

val inferior_to_greatest_weight : weight -> bool

val updt_greatest_weight : weight -> unit

val order_weight : weight -> weight -> int

val weight_merge : weight -> weight -> expr -> weight
