(*######################################################*)
(*			module.mli			*)
(*######################################################*)

open Type

val local_modules : string list ref
val concat_module_names : string -> string -> string
val import_intf : string -> unit
val use_intf : bool -> string -> renaming -> unit
val write_all : string -> unit
val load_pervasives : unit -> unit
val reset_base : unit -> unit
