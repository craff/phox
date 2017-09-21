open Lambda
open Lexer

val get_def : string -> term

val add_def : string -> term -> unit

val del_defs : string list  -> unit

val parse_lambda : token Stream.t -> term

val outputs : ?kvm:bool -> string list -> unit
