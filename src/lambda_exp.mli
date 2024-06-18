open Bindlib

type term
type stack
type term_val = {
  name : string;
  mutable value : term;
}

val bApp : term pre_term -> term pre_term -> term pre_term

val bLam : (term pre_term -> term pre_term) -> term pre_term

val bCro : stack pre_term -> term pre_term -> term pre_term

val bMu : (stack pre_term -> term pre_term) -> term pre_term

val bDef : term_val -> term pre_term

val bSVar : string -> term 

val bSide : string -> term 

val eval : term -> term

val cc : term

val print_term : term -> unit

val print_kvm_term : term -> unit

