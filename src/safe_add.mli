(* $State: Exp $ $Date: 2004/01/08 17:23:28 $ $Revision: 1.3 $ *)
(*######################################################*)
(*			safe_add.mli			*)
(*######################################################*)


open Data_base
open Types

(* add_key reuse lock : add a keyword, the first argument tells if the
   keyword can still be used to define a prefix of infix operator. If
   the boolean [lock] is true then the object can't be removed *)
val add_key : bool -> bool -> argkind list -> unit


(* add_sym name kind valeur syntax lock : add an object to the global
   context. If the boolean [lock] is true then the object can't be
   removed *)
val add_sym : string -> kind -> sym_value -> syntax -> bool -> 
               bool -> renaming -> int option -> af2_obj

val add_rlocal : Types.local_defs -> string -> kind -> sym_value -> syntax 
                   -> Types.local_defs * af2_obj


(* change the definition of an object *)
val redef_obj : af2_obj -> sym_value -> bool -> unit

val ftheorem_obj : af2_obj ref
val ftheorem_list_cons_obj : af2_obj ref
val fclaim_obj : af2_obj ref

