(*######################################################*)
(*			interact.mli			*)
(*######################################################*)

(* les commandes de l'editeur de preuves interactif *)

(* A NETOYER : commentaires des tactiques*)

open Type
open Local
open Pattern

(* Le principe :
    ou tient les preuves par le haut (et nom par la racine )*)

(* un objet de type state est soit une entree "incomplete" (ce sequent
n'est pas prouve) il est alors associe a un objet de type goal. ou
bien a une entre "complete" (typiquement un axiome ou l'application
d'un theorem *)

(* type d'une preuve :
    Goal = la formule a prouver
    Remain = les entrees incompletes de la preuve (la premiere entree
             constitue le "goal" courant)
    Leaf = les entrees completes de la preuve *)

type proof_state =
  {goal : expr;
   gpoly: int;
   remain : (goal*state) list;
   leaf : state list;
   pname : string option;
   ptex_name : string option;
   pexported : bool}

(* type des options pour rule_elim *)

and new_elim_option =
    NOptFl of expr * kind
  | NOptDf of string * new_elim_option list list

and elim_option =
    OptFl of expr
  | OptDf of string * (int * elim_option) list
  | OptInt of string list
  | OptAfter of string
  | OptNoax
  | OptWith of new_elim_option list list

(* type de la preuve courante (on utilise No_proof si il n'y a pas de
preuve en cours *)
and proof =
    No_proof
  | A_proof of proof_state
  | To_save of sym_value * expr * int * string option * string option * bool


(* Type des regles (ou tatique) generales :
    une tactique prend le "state" et "goal" d'une entree incomplete E
    et renvoie une liste d'entree incomplete ainsi qu'une liste d'entre
    complete qui peuvent etre substitues a E *)
type arule = goal -> state -> (goal * state) list * state list

type rule_opt =
  RNum of int              (* nombre de règles *)
| Names of (string *  new_elim_option list list option) list
  (* nom des règles, sauf pour-tout et -> nom de la variables ou de l'hyp
                              choisit par phox si "" *)
| Auth of af2_obj list     (* intros: listes des af2_obj au quels on applique une règle *)
| Inv_only
| Default

(* ponteur sur la preuve courante *)
val cur_proof : proof ref

(* do_goal F
    commence une preuve de F (on doit avoir cur_proof = No_proof avant) *)
val do_goal : expr -> string option -> string option -> bool -> unit

(* do_rule b T
    applique une tactique generale T au goal courant *)
val do_rule : int -> string -> int list -> arule -> int

(* do_save name
    sauve le theorem prouve sous le nom "name". La preuve courante doit
    d'abord etre termine (proof.Remain = []) *)
val do_save : string option -> bool -> unit

(* do_claim name expr
    ajoute "expr" comme un axiome de nom "name" *)
val do_claim : string -> string option -> expr -> bool -> unit

(* do_depend name
    affiche les axiomes (si le booléens est vrai) ou les théorème
    (sinon) dont le theorem de nom "name" depend *)
type depend_arg =
    Axioms
  | All
  | Immediate

val do_depend : depend_arg -> string -> unit

(* do_next ()
    change de goal courant (permutation des goals )*)
val do_next : int -> unit

(* do_instance e1 e2
    just unify e1 and e2 (usefull tu instanciate unif. var *)
val do_instance : int -> expr -> expr -> unit

(* do_undo_cmds nb
    defait les n dernieres tactiques ayant produit le goal courant *)
val do_undo_cmds : int -> unit

(* do_goals ()
    affiche tous les goals (le goal courant en dernier)*)
val do_goals : unit -> unit
val print_goal : bool -> bool -> int -> int -> goal -> unit

(* do_abort ()
    interromp la preuve courante *)
val do_abort : unit -> unit

(* les tactiques ....pas de commentaires, ca va changer ...*)
val rule_intro : bool ref -> trinfo -> rule_opt -> arule

val rule_axiom : bool -> trinfo -> string -> arule

val rule_theo : expr -> arule

val rule_elim : bool -> trinfo -> bool -> bool -> bool ->
                 (int * elim_option) list -> int -> expr -> arule

val rule_left : trinfo -> string ->
                rule_opt -> int list ref option -> arule
val rule_trivial : bool -> string list -> string list ->
                    trinfo -> arule
val mult_trivial : trinfo -> (goal * state) list ->
                     (goal * state) list * state list
val rule_auto : bool -> string list -> string list -> trinfo -> arule

val rule_use : bool -> trinfo -> string -> expr -> arule
(*  add a goal "e" with the current hypothesys, then "e" is added
    to the hypothesys of the previous goal. the boolean control
    if the new goal is first or second *)

val rule_rm : bool -> string list -> arule

val rule_rename : string -> string -> arule

val rule_claim : arule
val rule_absurd : arule
val rule_contradiction : arule

val rule_apply : trinfo -> string -> (int * elim_option) list -> int ->
   expr -> arule

val do_add_rlocal : string -> kind -> sym_value -> syntax -> arule

val do_add_csyntax : int -> string -> syntax -> arule

val set_local : int -> unit

val apply_rewrite : bool -> state list -> goal -> state -> rrule list ->
                      goal * state * state list
val add_assq :  pos_eq -> 'b -> (pos_eq * 'b) list -> (pos_eq * 'b) list
val hyp_to_erule : expr -> int -> hyp_kind -> eq_type
val hyp_to_rule : int -> hyp_kind -> rule
type store_stack
val store_mark : string -> store_stack
val store : string -> unit
val restore_to :  store_stack -> unit
val restore : bool -> unit
val pop_store : unit -> unit
val mem_expr : bool -> expr -> adone -> bool
val emapadd : expr -> adone -> adone
val emapadd' : expr -> adone -> adone
val adone : adone -> int Exprmap.t
val add_adone : adone -> expr -> int -> adone

(* Tactical *)

val compose_rule : arule -> arule -> arule
val map_rule : arule -> arule list -> arule
val orelse_rule : arule -> arule -> arule
val dispatch_rule : arule -> arule list -> arule
val try_rule : arule -> arule
val sort_rule : arule -> arule
val no_rule : arule

val add_to_nomatch : int -> unit

val remove_from_nomatch  : bool -> int -> unit

val prove_claim : string -> bool -> unit
val make_claim : string -> unit

val new_cmd_opt : (string * new_elim_option list list) list ref
val lock_intro : expr list ref
val lock_elim : string list ref
val lock_depth : (string * int) list ref


(* first bool: invertible rules only *)
(* ouvre-t-on des définitions, même si on a trouvé un règle *)
val get_intros : bool -> (pos_eq * eqns) list -> local_defs -> bool -> expr
  -> bool * (string *  (expr * af2_obj * expr * int * rule_option * float * bool)) list
val get_lefts : 'a option -> bool -> rule_opt -> string -> goal ->
  expr * int * hyp_kind * hyp_state *
  ((string * af2_obj list) *
   (expr * af2_obj * expr * int * rule_option *
    float * bool))
  list

val var_sat : goal -> unit
val try_axiom : bool -> int -> (goal * state) list -> state list ->
  (goal * state) list * state list

val from_resol : expr list ref option ref

val call_trivial : trinfo -> contxt -> (goal * state * state list) ->
                     (int * state * Exprmap.key) list -> contxt * (goal * state * state list)
