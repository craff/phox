(* $State: Exp $ $Date: 2004/01/08 17:23:27 $ $Revision: 1.2 $ *)
(*######################################################*)
(*			inductive.mli			*)
(*######################################################*)

open Basic
open Types.Base
open Data_base.Object
open Types

val in_inductive : bool ref 

val parse_inductive : bool -> Lexer.token Stream.t -> unit

val parse_data : bool -> Lexer.token Stream.t -> unit
(*
val parse_type : bool -> Lexer.token Stream.t -> unit
*)
