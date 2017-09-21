(* $State: Exp $ $Date: 2000/10/12 09:58:27 $ $Revision: 1.1.1.1 $ *)
(*######################################################*)
(*			tex.mli				*)
(*######################################################*)

open Types
open Lexer

val tex_docs : (string * out_channel) list ref
val parse_tex_header : token Stream.t -> unit
val do_tex : string list -> char Stream.t -> unit
val close_tex : unit -> unit
val exit_tex : unit -> unit
val parse_tex_sym : token Stream.t -> string * syntax
