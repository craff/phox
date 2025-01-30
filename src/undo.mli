(*######################################################*)
(*			undo.mli  			*)
(*######################################################*)

type undo_pos

val update : 'a ref -> 'a -> unit
val add_to_undo : (unit -> unit) -> unit
val reset_undo_unif : unit -> unit
val init_undo_unif : unit -> unit
val get_undo_pos : unit -> undo_pos
val do_undo : undo_pos -> unit
val print_undo_size : unit -> unit
