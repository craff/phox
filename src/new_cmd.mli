open Lexer
open Types
open Interact

type new_cmd

val parse_newcmd : bool -> token Stream.t -> new_cmd

val interpret_newcmd : new_cmd -> arule
