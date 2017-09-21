(* $State: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.11 $ *)
(*######################################################*)
(*			lambda_util.mli			*)
(*######################################################*)

open Basic
open Data_base
open Types

exception Free_match
exception Wrong_path

type env_cell =
  A of expr * env * int
| B of int
and env = env_cell list


(* functions use for parsing only *)
val last_lvl : argkind list -> level
val bind : string -> expr -> kind -> expr

(* bind or substitute a constant in a term *)
val bind_cst : string -> int -> expr -> kind -> expr
val subst_cst : int -> expr -> expr -> expr

(* bind an atom in a term *)
val bind_atom : string -> af2_obj -> expr -> kind -> expr

(* you guessed *)
val term_size : expr -> int
val term_size_rec : expr -> int
val fis_close : (af2_obj -> bool) ref

(* get the kind and the val of an object in the context. 
   ALWAYS use the last form if you need both. *)
val get_kind : af2_obj -> kind
val get_safe_kind : af2_obj -> kind
val get_value : af2_obj -> sym_value
val get_kind_value : af2_obj -> sym_value * kind

(* copy function with or without hash-consing.
   You should not need to call them ! (uses in
   parser, print and safe_add) *)
val ckind_copy :  kind -> kind
val ckind_expr_copy : sym_value * kind -> sym_value * kind
val cexpr_copy : sym_value -> sym_value
val ctexpr_copy : expr -> expr
val kind_copy :  kind -> kind
val kind_expr_copy : sym_value * kind -> sym_value * kind
val expr_copy : sym_value -> sym_value
val texpr_copy : expr -> expr
val clear_cache : unit -> unit
val mod_copy : (af2_obj -> af2_obj) -> expr -> expr
val mod_kind_copy : (af2_obj -> af2_obj) -> kind -> kind

(* lifting of DeBruijn indicies *)
val lift : expr -> expr         (* +1 *)
val mlift : int -> expr -> expr (* +n *)
val unlift : expr -> expr       (* -1 *)

(* equality functions *)

val equal_path : path list -> path list -> bool
val equal_pos_eq : pos_eq -> pos_eq -> bool
val equal_expr : expr -> expr -> bool
val equal_kind_no_unif : kind -> kind -> bool
val cmp_expr : expr -> expr -> int
val order : kind -> int

(* hash functions compatible with these equality *)
val hash_expr : int -> expr -> int
(* with a special behavior for unification variables *)
val hashi_expr : int -> expr -> int

(* Test equality of two pairs of [expr] up to renaming of unbound unification
   variables *)
val uni_expr : expr Map.t * expr * expr -> 
                 expr Map.t * expr * expr -> bool

val eqi_expr : expr Map.t * expr * expr -> 
                 expr Map.t * expr * expr -> bool

(* uniformise a pair of [expr] so that equal_expr and uni_expr coincide *)
val uniform : expr Map.t -> expr -> expr -> expr * expr

(* normalisation functions *)
(* standard *)
val norm_expr : expr -> expr
(* with a context for unification variables *)
val norm_lexpr : expr Map.t -> expr -> expr
(* with a list of arguments (with or without kind) *)
val norm_ldexpr : expr Map.t -> (af2_obj -> bool) -> (int -> expr option) -> expr -> expr
val norm_st_expr : expr -> (expr * kind) list -> expr
(* normalisation with an arguments stack *)
val norm_sexpr : expr -> expr list -> expr
(* normalisation with an environment *)
val norm_env_expr : expr -> expr list -> expr
val norm_lsexpr : expr Map.t -> expr -> expr list -> expr
val subst_expr : (int * expr) list ->  expr -> expr

(* eta reduction (used for printing only) *)
val eta_red : expr -> expr

(* substitution at a position specified by a path *)
val path_subst : path list -> expr -> expr -> expr
(* test equality after substitution *)
val path_test : path list -> expr -> expr -> expr -> bool
(* path_diff k k': checks if k' is final in k and compute the path length difference *) 
val path_diff : kind -> kind -> int

(* test if an expression starting with some "lambdas" use at least one 
   of its argument *)
val linear_uvar : expr -> bool

(* list of unification variables *)
val list_uvar : expr -> Set.t
val list_ucst : expr -> Set.t
val has_uvar : expr Map.t -> expr -> bool
val depth_uvar : expr Map.t -> expr -> int

val expr_local : expr -> string

(* get the head of a term *)
val head : expr -> (pos_eq * af2_obj)
val assoc_eq : pos_eq -> (pos_eq * 'a) list -> 'a
val count_lambdas : expr -> int
val advance_in_arrow : int -> kind -> kind
val head_length : expr -> int
val head_kind : expr -> (pos_eq * af2_obj * kind list) 

val lArrow : kind list -> kind -> kind
 
(* saturation of two abstractions with unification variables *)
exception Fail_saturate
val saturate : expr -> expr -> int -> kind -> kind -> kind list -> 
  int * (expr*kind) list * expr * expr

val eqcmp : expr -> expr -> expr -> expr -> int list

val add_Equations :
  ext -> pos_eq -> pos_eq -> bool ->
  expr -> expr -> int ->  eq_type -> kind -> eqpath list -> bool -> int -> bool -> unit
val add_Rules :
  ext -> af2_obj -> string -> expr -> af2_obj -> 
    expr -> int -> rule_option -> float -> bool -> unit
val add_Trivial_Hacks :
  ext -> af2_obj -> int -> bool -> unit
val add_Tex_syntax :
  ext -> af2_obj -> string -> syntax -> bool -> unit

val apply_perm : 
  int list -> 'a list -> 'a list

val simpl_match : int -> expr -> expr -> (int * expr) list
val occur : int -> expr -> bool
val occur' : int -> expr -> bool
val occur_evar : expr -> bool
val occur_set : expr Map.t -> Set.t -> expr -> bool

type stack = (expr * env * int) list
exception Efun_error of string

val efun_table : ((stack -> env -> int -> expr -> expr) -> 
                  (stack -> expr -> expr) -> 
                    stack -> int -> expr) array
val add_fun : ((stack -> env -> int -> expr -> expr) -> 
               (stack -> expr -> expr) -> 
                  stack -> int -> expr) -> sym_value
val evaluable : kind -> bool
val space_of_int : int -> string
val space_of_num : Num.num -> string

val make_pattern : expr -> expr
val saturate_pattern : expr -> expr

val generalize_for_rules : af2_obj -> expr -> expr -> expr * expr * expr

val generalize_for_equations : eqns -> eqns

