(*######################################################*)
(*			parse_cmd.mli			*)
(*######################################################*)


open Lex
open Flags

exception End_of_module

val parse_value : token Stream.t -> flag_value

val parse_cmd : char Stream.t -> token Stream.t -> unit
