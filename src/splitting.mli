exception Unsat
type litname = int
val print_litname : int -> unit
type slit = { name : litname; pol : bool; }
type truetree = Nil of bool | Nodtt of litname * truetree * truetree
val mklit : litname -> bool -> slit
val new_litname : unit -> int
val current_litname : unit -> int
val reinit_litnames : unit -> unit
val lit_state : truetree ref
val init_lit_state : unit -> unit
val mem_remove : litname -> slit list -> slit list * slit
val add : slit list -> truetree -> truetree
val simpltree : truetree -> truetree
val split_add : slit list -> unit
val test_insat : slit list list -> truetree
