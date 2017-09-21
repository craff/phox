(* $State: Exp $ $Date: 2000/10/12 09:58:27 $ $Revision: 1.1.1.1 $ *)
(*######################################################*)
(*			module.mli			*)
(*######################################################*)

open Types

val local_modules : string list ref
val concat_module_names : string -> string -> string
val import_intf : string -> unit
val use_intf : bool -> string -> renaming -> unit
val write_all : string -> unit
val load_pervasives : unit -> unit
val reset_base : unit -> unit
