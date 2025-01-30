(*######################################################*)
(*			tex.mli				*)
(*######################################################*)

open Type
open Lex

val tex_docs : (string * out_channel) list ref
val parse_tex_header : token Stream.t -> unit
val do_tex : string list -> char Stream.t -> unit
val close_tex : unit -> unit
val exit_tex : unit -> unit
val parse_tex_sym : token Stream.t -> string * syntax
