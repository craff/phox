(* $State: Exp $ $Date: 2004/05/18 15:55:28 $ $Revision: 1.3 $ *)
(*######################################################*)
(*			lexer.mli			*)
(*######################################################*)

type token =
    Lpar | Rpar | Dot | Dol
  | Ident of string
  | Kwd of string
  | Num of Num.num
  | Float of float
  | Str of string
  | Char of char
  | Uid of int
  | Unid of string
  | Kid of string
  | Eof
  | Joker of string
  | Tex of string list * char Stream.t

exception Illegal_char of char

(* the lexical analisys *)
val next_token : char Stream.t -> token
(* to call after an error to eat everything before the next carriage return *)
val reset_lexer : char Stream.t -> unit
(* a useless function *)
val print_token : token -> unit
val string_of_token : token -> string
val extra_dot : bool ref
val comment : char Stream.t -> unit
val special : char Stream.t -> char
val stream_map : ('a -> 'b) -> 'a -> 'b Stream.t
