(* $State: Exp $ $Date: 2004/11/22 13:38:04 $ $Revision: 1.5 $ *)
(*######################################################*)
(*			parser.mli			*)
(*######################################################*)

open Lexer
open Types

exception Syntax_error
exception Unbound of string
exception Illegal_bind of string
exception Not_def of string
exception Invalid_kwd of string
exception Cant_bind of string list
exception Dup_arg of string

val inlet : bool ref

val bind_free : bool -> int -> (string * int) list -> expr -> expr

(* parse an expression *)
val parse_expr : token Stream.t -> expr
val parse_free_expr : token Stream.t -> expr
val parse_tex_expr : string -> token Stream.t -> expr

(* parse an atomic expression *)
val parse_atomexpr : token Stream.t -> expr

(* parse a kind *)
val parse_kind : token Stream.t -> kind

(* parse an expression with some free variables *)
val parse_bound_expr : (string * kind) list -> token Stream.t -> expr

(* parse an atomic expression with some free variables *)
val parse_bound_atomexpr : string list -> token Stream.t -> expr

(* parse the definition of a syntax *)
val parse_syntax_def : 
  bool -> token Stream.t -> (string * syntax * (string * kind) list)

(* parse a legal identifier *)
val parse_ident : token Stream.t -> string
val parse_ident_list : token Stream.t -> string list
val parse_ass_ident : token Stream.t -> string * kind
type isass = 
  Noass
| Ass of kind
| IAss of expr
val parse_bind : int * coma * semi -> token Stream.t -> string list * (int * coma * semi) * isass

(* parse a list of legal identifier *)
val parse_args : token Stream.t -> (string * kind) list

(* Get a syntax from a string, usefull to construct object of type syntax !*)
val syntax_of_string : bool -> string -> string * syntax
val expr_of_string : string -> expr

val parse_renaming : token Stream.t -> renaming

val terror : token -> token Stream.t -> string
val serror : string -> token Stream.t -> string

val not_proof_mode : unit -> unit
val set_proof_mode : (int -> expr) -> unit

val cur_env : int ref

val parse_sort : token Stream.t -> string * int * sym_value

val parse_kind_vargs :  token Stream.t -> kind list
val reset_kvar : unit -> unit
val get_kname : kind -> string
