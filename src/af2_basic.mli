(* $State: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.16 $ *)
(*######################################################*)
(*		      af2_basic.mlip			*)
(*######################################################*)

open Type

val type_form : expr -> unit
val init_data_af2 : Base.base -> unit
val tsym_get : string -> af2_obj

val kForm : kind
val kProof : kind
val kTheorem : kind
val kTheorem_list : kind
val kNum : kind
val kString : kind
val kSyntax : kind
val kUnit : kind
val iOption : af2_obj
val iList : af2_obj
val iPair : af2_obj
val iSum : af2_obj

val arrow_obj : af2_obj
val forall_obj : af2_obj
val equal_obj : af2_obj
val theorem_obj : af2_obj
val comment_obj : af2_obj
val arrow_intro_obj : af2_obj
val arrow_elim_obj : af2_obj
val cut_rule_obj : af2_obj
val forall_intro_obj : af2_obj
val forall_elim_obj : af2_obj
val devl_def_obj : af2_obj
val fact_def_obj : af2_obj
val local_def_obj : af2_obj
val lr_eqn_obj : af2_obj
val rl_eqn_obj : af2_obj
val use_theorem_obj : af2_obj
val claim_obj : af2_obj
val lclaim_obj : af2_obj
val imported_obj : af2_obj
val proof_obj : af2_obj
val equal_reflexive_obj : af2_obj
val theorem_list_cons_obj : af2_obj
val theorem_list_nil_obj : af2_obj
val default_object : af2_obj
val match_object : af2_obj
val rewrite_rules : ext
val let_obj : af2_obj ref
val and_obj : af2_obj ref
val or_obj : af2_obj ref
val false_obj : af2_obj ref
val true_obj : af2_obj ref
val diff_obj : af2_obj ref
val not_obj : af2_obj ref
val and_elim_l_obj : af2_obj ref
val and_elim_r_obj : af2_obj ref
val exists_obj : af2_obj ref
val exists_one_obj : af2_obj ref
val peirce_law_obj : af2_obj ref
val absurd_obj : af2_obj ref
val contradiction_obj : af2_obj ref
val false_elim_obj : af2_obj ref
(*
val fun_none_obj : af2_obj
val fun_some_obj : af2_obj
val fun_nil_obj : af2_obj
val fun_cons_obj : af2_obj
val fun_fix_obj : af2_obj
val fun_unit_obj : af2_obj
val fun_add_obj : af2_obj
val fun_sub_obj : af2_obj
val fun_mul_obj : af2_obj
val fun_div_obj : af2_obj
val fun_eq_obj : af2_obj
val fun_less_obj : af2_obj
val fun_lesseq_obj : af2_obj
val fun_gt_obj : af2_obj
val fun_gteq_obj : af2_obj
val fun_if_obj : af2_obj
val fun_raise_obj : af2_obj
val fun_catch_obj : af2_obj
val fun_call_obj : af2_obj
val fun_new_elim_obj : af2_obj
val fun_new_intro_obj : af2_obj
val fun_close_def_obj : af2_obj
val fun_def_obj : af2_obj
val fun_elim_after_intro_obj : af2_obj
val fun_fun_obj : af2_obj
val fun_new_rewrite_obj : af2_obj
val fun_save_obj : af2_obj
val fun_quit_obj : af2_obj
val fun_cst_obj : af2_obj
val fun_local_obj : af2_obj
val fun_goal_obj : af2_obj
val fun_intro_num_obj : af2_obj
val fun_intro_names_obj : af2_obj
val fun_intro_objs_obj : af2_obj
val fun_match_obj : af2_obj
val fun_trivial_obj : af2_obj
val fun_auto_obj : af2_obj
val fun_use_obj : af2_obj
val fun_rmh_obj : af2_obj
val fun_slh_obj : af2_obj
val fun_axiom_obj : af2_obj
val fun_pair_obj : af2_obj
val fun_fst_obj : af2_obj
val fun_snd_obj : af2_obj
val fun_inl_obj : af2_obj
val fun_inr_obj : af2_obj
*)
val after_pervasives : unit -> unit
val tbl_rewrite : eqns eqhash
val intro_ext : ext
val tbl_intro :
  (string * (expr * af2_obj * expr * int * rule_option * float * bool)) list symhash
val elim_ext : ext
val tbl_elim :
  (string * (expr * af2_obj * expr * int * rule_option * float * bool)) list symhash
val elim_after_intro : ext
val tbl_elim_after_intro : (int * bool) symhash
val close_def : ext
val tbl_close_def : (int * bool) symhash
val tex_syntax : ext
val tbl_tex_syntax : (string * syntax * bool) symhash
val add_intro : bool -> bool -> bool -> bool -> string -> af2_obj -> float -> bool -> unit
val add_elim : af2_obj -> string -> int -> af2_obj -> int -> float -> bool -> unit
val fNONE : int
val fALLE : int
val fTOT : int
val fLEFT : int
val fINV : int
val fNEC : int
val fDND : int
val fTRM : int
val fCTD : int
val fREM : int
val isALLE : int -> bool
val isTOT : int -> bool
val isLEFT : int -> bool
val isINV : int -> bool
val isNEC : int -> bool
val isDND : int -> bool
val isTRM : int -> bool
val isCTD : int -> bool
val isREM : int -> bool
val add_elim_after_intro : af2_obj -> int -> bool -> unit
val fdo_add_close : (int list -> af2_obj -> unit) ref
val add_close_def : int list -> af2_obj -> bool -> unit
val fdo_add_syntax : (int list -> af2_obj -> string -> syntax -> unit) ref
val add_tex_syntax : int list -> af2_obj -> string -> syntax -> bool -> unit
exception Dont_Know_Eq
val decompose_eq : eqpath list list ->
  expr -> (expr * expr * int * eqpath list * int * kind) list * bool
val add_rewrite : int -> af2_obj -> bool -> unit
val delete_special : string -> af2_obj -> unit
val default_of : kind -> expr
val add_basic_tex : unit -> unit
val decom : bool -> expr -> expr option * af2_obj * kind list * expr list
val decom' : expr -> expr option * pos_eq * kind list * expr list
val decom'' : expr -> expr option * pos_eq * kind list * expr list

val print_proof : string -> unit
