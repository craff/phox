(*######################################################*)
(*			print.mli			*)
(*######################################################*)


open Type

exception Stack

(* printing function *)
val in_mmath : bool ref
val in_verb : bool ref
val tex_local : (string * expr) list ref
val farrow_obj : af2_obj ref
val print_expr : expr -> unit
val print_expr_sy : bool -> expr -> unit
val print_expr_sorted : expr -> unit
val print_tex_expr : expr -> unit
val print_expr_tr : expr -> unit
val print_kind : kind -> unit
val print_path : string list -> path list -> string list
val print_object : af2_obj -> unit
(* with a list of names for the free DeBruijn indices *)
val print_expr_env : string list -> expr -> unit
(* function making a free name from a root *)
val free_name : string -> string list -> string
val ftbl_tex_syntax : (string * syntax * bool) symhash ref
val fkTheorem : kind ref

(* reset the name of kind variables used to print polymorphic kind *)
val reset_kind_var : unit -> unit

(* a list of object in the base which should be printed by a special function.
   this function will get the list of arguments of the constant *)
val print_sp : (af2_obj * (expr list -> expr)) list ref
val do_texify : bool -> bool -> string -> string

val print_local : local_defs -> unit

val print_pipe_and_stdout : (bool -> unit) -> unit
val print_eq : eq_type -> unit
val is_case : af2_obj -> bool

val print_to_string : ('a -> unit) -> 'a -> string
