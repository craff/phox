(*######################################################*)
(*			compile.mli			*)
(*######################################################*)

open Type
open Lambda_exp

val compile : af2_obj -> term

val translate : af2_obj -> af2_obj -> af2_obj -> term
