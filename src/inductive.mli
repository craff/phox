(*######################################################*)
(*			inductive.mli			*)
(*######################################################*)


val in_inductive : bool ref

val parse_inductive : bool -> Lex.token Stream.t -> unit

val parse_data : bool -> Lex.token Stream.t -> unit
(*
val parse_type : bool -> Lex.token Stream.t -> unit
*)
