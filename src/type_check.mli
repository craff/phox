(* $State: Exp $ $Date: 2001/01/04 17:40:49 $ $Revision: 1.2 $ *)
(*######################################################*)
(*			type_check.ml			*)
(*######################################################*)

open Type

exception Bad_proof of int

val it_path : 'a -> 'a list -> path list -> 'a list
val proof_check : expr -> expr
