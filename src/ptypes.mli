type adresse = bool list
type 'a origine =
    Resol of int * 'a origine * int * 'a origine * 'a
  | Decomp of int * 'a origine * 'a * string
  | Contrac of int * 'a origine * 'a
  | Split of int * 'a origine * int
  | Donne
type ('a, 'b) clause = {
  litx_pos : 'a list;
  litx_neg : 'a list;
  litx_ukn : 'a list;
  litx_ps : Splitting.litname list;
  litx_ns : Splitting.litname list;
  poids : Typespoids.poidsclause;
  vientde : 'a origine;
  numero : int;
  contr : 'b ref;
  indice : Typespoids.indiceclause;
  histclist : (int * (Typespoids.indiceclause * int)) list;
  histrlist : (string * (Typespoids.indiceclause * int)) list;
}
type ('a, 'b) tree =
    Feuille of 'a
  | Nr of 'a * 'b * ('a, 'b) tree * ('a, 'b) tree
  | Nrs of 'a * Splitting.litname * ('a, 'b) tree * ('a, 'b) tree
  | Nd of 'a * 'b * string * ('a, 'b) tree
  | Nc of 'a * 'b * ('a, 'b) tree
  | Ns of 'a * int * ('a, 'b) tree
  | Mktree of 'a
  | Central of 'a * Splitting.litname * ('a, 'b) tree
exception Proved
exception Prove_fails
exception EmptySplit
exception Noprinting
val verbose : int ref
val pause : bool ref
val maxcndts : int ref
val splitting : bool ref
val check_subcase : bool ref
val trace_proof : bool ref
val empty_clause : int ref
val taillecndats : int ref
val timemax : int ref
module type Types =
  sig
    type litteral
    type contrainte
    type proof_tree
    val ordre :
      (litteral, contrainte) clause -> (litteral, contrainte) clause -> int
    val longueur : litteral -> int
    module MapSplit : Map.S
    val memory_split : Splitting.litname MapSplit.t ref
    module Hashform : Hashtbl.S
    val cndats : (litteral, contrainte) clause list ref
    val djvues :
      ((litteral, contrainte) clause *
       (litteral * bool, (litteral, contrainte) clause * litteral) Hashtbl.t)
      list ref
    val initdjvues :
      ((litteral, contrainte) clause *
       (litteral * bool, (litteral, contrainte) clause * litteral) Hashtbl.t)
      list ref
    val empty_s_clauses : (litteral, contrainte) clause list ref
    val initallclauses : (int, (litteral, contrainte) clause) Hashtbl.t
    val allclauses : (int, (litteral, contrainte) clause) Hashtbl.t
  end
module Types :
  functor (Logic : Logic.Logic) ->
    sig
      exception Probleme
      exception Elim
      type litteral = Logic.formula
      type contrainte = Logic.constraints
      type proof_tree = ((litteral, contrainte) clause, litteral) tree
      val ordre : ('a, 'b) clause -> ('c, 'd) clause -> int
      val longueur : Logic.formula -> int
      module OrderedLit :
        sig
          type t = litteral
          val compare : Logic.formula -> Logic.formula -> int
        end
      module MapSplit :
        sig
          type key = OrderedLit.t
          type 'a t = 'a Map.Make(OrderedLit).t
          val empty : 'a t
          val is_empty : 'a t -> bool
          val add : key -> 'a -> 'a t -> 'a t
          val find : key -> 'a t -> 'a
          val remove : key -> 'a t -> 'a t
          val mem : key -> 'a t -> bool
          val iter : (key -> 'a -> unit) -> 'a t -> unit
          val map : ('a -> 'b) -> 'a t -> 'b t
          val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
          val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
          val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
          val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
        end
      val memory_split : Splitting.litname MapSplit.t ref
      module Hashform :
        sig
          type key = Logic.FormHashType.t
          type 'a t = 'a Hashtbl.Make(Logic.FormHashType).t
          val create : int -> 'a t
          val clear : 'a t -> unit
          val copy : 'a t -> 'a t
          val add : 'a t -> key -> 'a -> unit
          val remove : 'a t -> key -> unit
          val find : 'a t -> key -> 'a
          val find_all : 'a t -> key -> 'a list
          val replace : 'a t -> key -> 'a -> unit
          val mem : 'a t -> key -> bool
          val iter : (key -> 'a -> unit) -> 'a t -> unit
          val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
          val length : 'a t -> int
        end
      val cndats : (litteral, contrainte) clause list ref
      val djvues :
        ((litteral, contrainte) clause *
         ((litteral, contrainte) clause * litteral) Hashform.t)
        list ref
      val initdjvues :
        ((litteral, contrainte) clause *
         ((litteral, contrainte) clause * litteral) Hashform.t)
        list ref
      val empty_s_clauses : (litteral, contrainte) clause list ref
      val initallclauses : (int, (litteral, contrainte) clause) Hashtbl.t
      val allclauses : (int, (litteral, contrainte) clause) Hashtbl.t
    end
