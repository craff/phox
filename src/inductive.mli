(* $State: Exp $ $Date: 2004/01/08 17:23:27 $ $Revision: 1.2 $ *)
(*######################################################*)
(*			inductive.mli			*)
(*######################################################*)


val in_inductive : bool ref

val parse_inductive : bool -> Lex.token Stream.t -> unit

val parse_data : bool -> Lex.token Stream.t -> unit
(*
val parse_type : bool -> Lex.token Stream.t -> unit
*)
