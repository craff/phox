(* $State: Exp $ $Date: 2002/12/06 12:36:45 $ $Revision: 1.3 $ *)
(*######################################################*)
(*			compile.mli			*)
(*######################################################*)

open Types
open Lambda

val compile : af2_obj -> term

val translate : af2_obj -> af2_obj -> af2_obj -> term
