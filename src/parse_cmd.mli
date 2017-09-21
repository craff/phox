(* $State: Exp $ $Date: 2000/10/12 09:58:27 $ $Revision: 1.1.1.1 $ *)
(*######################################################*)
(*			parse_cmd.mli			*)
(*######################################################*)


open Lexer
open Flags

exception End_of_module

val parse_value : token Stream.t -> flag_value

val parse_cmd : char Stream.t -> token Stream.t -> unit
