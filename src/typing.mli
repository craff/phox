(* $State: Exp $ $Date: 2001/12/14 10:11:29 $ $Revision: 1.2 $ *)
(*######################################################*)
(*			typing.mli			*)
(*######################################################*)


open Type


type generalize_env = (int * (kind ref * kind) list) ref

val generalize_kind : generalize_env -> kind -> kind
val generalize_path : generalize_env -> path list -> path list
val generalize_expr : generalize_env -> expr -> expr

(* inferes the type of an expression *)
val type_check : expr -> kind

(* inferes the type of an expression which is known to be well typed *)
val fast_type_infer : kind list -> expr -> kind

(* check the type of an expression *)
val type_strong : expr -> kind -> unit

(* get an expression from an object in the base and instanciate its kind
   to match the given kind. USE ONLY THAT ON POLYMORPHIC OBJECTS *)
val kind_inst : af2_obj -> kind list -> expr

(* if a term is EAtom(o,k), expend the definition using kind_inst above *)
val get_inst : expr -> expr

val subst_obj_kind : kind list -> af2_obj -> kind

val build_subterm : af2_obj -> kind list -> expr list -> kind * expr
