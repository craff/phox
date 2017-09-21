(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.8 $ *)
(*######################################################*)
(*			flags.mli			*)
(*######################################################*)

type flag_value = 
    Vint of int
|   Vbool of bool
|   Vstring of string
|   Vprint

val set_flag : string -> flag_value -> unit

val trace_trivial : bool ref
val trace_pmatch : bool ref
val trace_level : int ref
val trace_eqres : bool ref
val trace_dist : bool ref
val trdepth : int ref
val pgtrdepth : int ref
val eqdepth : int ref
val eqbreadth : int ref
val eqflvl : int ref
val eqplvl : int ref
val auto_lvl : int ref
val auto_type : bool ref
val tex_type_sugar : bool ref
val tex_infix_sugar : bool ref
val tex_lisp_app : bool ref
val debug_proof_check : bool ref
val min_tex_space : int ref
val max_tex_space : int ref
val comma_tex_space : int ref
val binder_tex_space : int ref
val tex_indent : int ref
val tex_margin : int ref
val tex_max_indent : int ref
val print_sort : bool ref
val print_match_case : bool ref
val auto_left_lvl : int ref
val new_distance : bool ref
val resol_verbose : int ref
val cndats_max_length : int ref
val cndats_max_weight : int ref
val newcmd_resolve : bool ref

val reset_flags : unit -> unit

type trace_save

val decr_trace_level : unit -> trace_save
val incr_trace_level : trace_save -> unit
