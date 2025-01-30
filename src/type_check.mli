(*######################################################*)
(*			type_check.ml			*)
(*######################################################*)

open Type

exception Bad_proof of int

val it_path : 'a -> 'a list -> path list -> 'a list
val proof_check : expr -> expr
