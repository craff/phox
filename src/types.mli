(* $State: Exp $ $Date: 2005/09/19 07:16:40 $ $Revision: 1.9 $ *)
(*######################################################*)
(*			type.mli			*)
(*######################################################*)


open Format
open Basic
open Data_base
open Object
open Data

(* the basic object manipuled *)

(* the kind of an object *)

(* les sortes (kind) elles memes *)
type kind =
  KArrow of kind * kind     (* arrow *)
| KAtom of symbol o_object * kind list  (* constante de type *)
| KVar of kind ref          (* variable polymorphe *)
| KBVar of int              (* variable liee par un Let, indice de B. *)
| Unknown

(* syntax of symbol *)

and syntax =
  Trivial | Hiden of bool
| Prefix of argkind list * permutation
| Infix of level * level * argkind list * permutation * string * string
| Mute | Free

and permutation =
  Idtperm
| Perm of int list * int list

and level = float

and coma =
  Nocoma
| Coma of expr

and semi =
  Nosemi
| Semi of expr

and argkind =
	Bind of int * coma * semi
|	Arg of level
|	Key of string
|       IKey of string
|       Space of string * string

and assoc = Non_assoc | Left_assoc | Right_assoc

(* Terme du lambda-calcul simplement type *)

and expr =
  EVar of int
                   (* variable liee, indice de Bruijn *)
| FVar of string
                   (* variable libre, disparait apres le parsing *)
| EAtom of symbol o_object * kind list
		   (* reference a la base de donnee *)
| EApp of expr * expr
	           (* application *)
| EAbs of string * expr * kind
		   (* abstraction, string used for printing only *)
| UCst of int * kind
		   (* constante pour l'unification *)
| UVar of int * kind
		   (* variable pour l'unification *)
| Path of path list * expr
		   (* chemin dans les termes + expression *)
                   (* ceci est un lieur !, on lui donne pourtant
                      le type de l'expression *)
| Syntax of syntax
| EData of data

and path =
  LApp
| RApp
| PAbs of string * kind

(* Termes + informations stockes dans la base de donnees *)

and sym_value =
  Cst                   (* une constante *)
| Def of expr           (* objet definit *)
| Prg of expr		(* programme *)
| Fun of int		(* un programme primitif *)
| KCst                  (* une constante de sorte *)
| KDef of kind          (* une sorte définies *)
(* cas particulier *)
| VKey                  (* un mot clef *)
| Imp                   (* imported (only in interface file) *)
| AImp of symbol o_object

and symbol = {
  fkind : kind;         (* type simple + expr reguliere *)
  mutable fvalue : sym_value;   (* valeur ... *)
                        (* mutability only used for importing *)
  syntax : syntax;      (* la syntaxe: comment parser et afficher *)
  poly : int;          (* le type est-il polymorphe *)
  exported : bool;      (* l'objet doit-il etre exporte *)
  mutable origin : renaming       (* origine ... *)
}

and renaming =
  Imported of string * renaming
| Used of renstruct * renaming
| Idtren
| Kernel
| Local_hyp
| Local_def
| Being_added

and renstruct = {
  default : string;
  rlocal : (string * (string * syntax)) list;
  general : (string * string) list;
  from : (string * renaming) list
}

(* About equations *)

type eq_type =
  Eq_theo of symbol o_object
| Eq_axiom of expr * int
| Eq_subgoal of expr * int

type eq_perm = int list

type pos_eq =
  Alleq
| Uveq
| Oneq of symbol o_object
| Uneq of int

type eqpath = Left_and | Right_and | Open_def

type eqns = (pos_eq * expr * expr * int * kind * bool *
               (eq_type * eq_perm * eqpath list * bool * int * bool) list) list

(* The type pos_eq gives the different possibilities for the head of
   an expr : An object in the context, a constant (UCst) or a variable
   (UVar). The hashtbl of a rewrite rules uses the pos_eq of the
   left term in the equation as an hash-key.
     - 1st arg in eqns : the pos_eq of the right term
     - 2nd arg : left term (form \lambda x1 ... \lambda xn t)
     - 3rd arg : right term (form \lambda x1 ... \lambda xn t)
     - 4th arg : kind of the term (gives the number of lambdas)
     - 5th arg : is the equation symetric
     - 6th arg : List of theorem and hypothesis
           1: what theorem or hypothesis
           2: the permutation
           3: conjunction list
           4: direction
           5: conditionnal
           6: exported *)

type 'a eqhash
type 'a symhash

type rule_option =
  Intro_opt of int * symbol o_object option
| Elim_opt of int list

(* Type clause généralisée *)
(* should stay here *)
type weight = float

type clause =
    {
      (* first bool : true = negative literal *)
      (* second bool : true = rigid literal *)
      literals : (expr * bool * bool) list;
      weight : weight;
    }

type hint =
    Literal_hint of int
  | Or_hint of hint * hint
  | And_hint of hint * hint

type tbl_types =
    (* Equations pour rewrite. DO NOT CHNAGE THIS ONE *)
| Equations of eqns eqhash

    (* Regle d'introduction et d'elimination *)
| Rules of (string *
	      (expr * symbol o_object * expr * int * rule_option * float * bool)) list symhash

    (* Auto_elim et elim_after_intro : optimisations de trivial *)
| Trivial_Hacks of (int * bool) symhash

| Tex_syntax of (string * syntax * bool) symhash

exception Error
exception Gen_error of string

(* the function getting the [symbol object] used in an object of type
   [expr] or [sym_value] *)

type af2_obj = symbol o_object
type ext = (symbol,tbl_types) o_extern

(* build an expression from an object *)
val make_args : int -> kind list
val aobj : af2_obj -> expr
val sub_sym : symbol -> af2_obj list
val sub_expr : expr -> af2_obj list
val sp_del : af2_obj list -> ext -> unit
val sp_sub : ext -> af2_obj list
val sp_new : unit -> ext array
val imported_modules : (string * renaming) list ref
val tmp_modules : (string * renaming) list ref

module Base: Base with type symbol = symbol and type tbl_types = tbl_types

open Base

(* manipulation of level *)

val level_leq : level -> level -> bool
val level_le : level -> level -> bool
val level_cmp : level -> level -> int
val inf_level : level -> level -> level
val delta : level -> level
val delta' : level -> level
val idelta' : level -> level
val approx : level -> level -> bool
val min_level : level
val max_level : level
val print_level : level -> unit
val level_to_string : level -> string

(* others *)

val dummy_sym : symbol
val dummy_obj : af2_obj

val path_count : path list -> int

val eqhash_new : int -> 'b eqhash
val eqhash_clear : 'b eqhash -> unit
val eqhash_add : 'b eqhash -> pos_eq -> 'b -> unit
val eqhash_find : 'b eqhash -> pos_eq -> 'b
val eqhash_remove : 'b eqhash -> pos_eq -> unit
val eqhash_do_table : (pos_eq -> 'b -> 'c) -> 'b eqhash -> unit
val eqhash_it_table : ('c -> pos_eq -> 'b -> 'c) -> 'c -> 'b eqhash -> 'c

val symhash_new : int -> 'b symhash
val symhash_clear : 'b symhash -> unit
val symhash_add : 'b symhash -> af2_obj -> 'b -> unit
val symhash_find : 'b symhash -> af2_obj -> 'b
val symhash_remove : 'b symhash -> af2_obj -> unit
val symhash_do_table : (af2_obj -> 'b -> 'c) -> 'b symhash -> unit
val symhash_it_table : ('c -> af2_obj -> 'b -> 'c) -> 'c -> 'b symhash -> 'c

val get_Equations : tbl_types -> eqns eqhash
val get_Rules :
  tbl_types -> (string *
		  (expr * af2_obj * expr * int * rule_option * float * bool)) list symhash
val get_Trivial_Hacks : tbl_types -> (int * bool) symhash
val get_Tex_syntax : tbl_types -> (string * syntax * bool) symhash

val the_base : base ref

type local_defs = {
    cst_def : (string * expr) list;
    caps_def : (string * af2_obj) list;
    local_ctex_tbl : (int * (string * syntax)) list;
    local_tex_tbl : (af2_obj * (string * syntax)) list;
    local_close_tbl : af2_obj list;
    cst_eq : (int * (expr * (int * expr * expr * bool * bool ) list)) list
}

val empty_local : local_defs
val cur_local : local_defs ref

val sym_get : string -> af2_obj
val sym_add : string -> symbol -> bool -> af2_obj
val sym_del : af2_obj -> unit
val sym_rename : af2_obj -> string -> unit
val sym_rename_undoable : af2_obj -> string -> unit -> unit
val set_value : af2_obj -> symbol -> unit
val get_syntax : af2_obj -> syntax
val get_name : af2_obj -> string
val get_sym : af2_obj -> symbol
val is_poly : af2_obj -> int
val get_table : string -> ext
val reset_tables : base -> unit

(* manipulation of [kind] *)
val mk_Var : unit -> kind

val fprint_expr : (expr Map.t -> expr -> unit) ref
val fprint_kind : (kind -> unit) ref

val recursive : bool ref
