module Oldeduction :
  functor (Logic : Logic.Logic) ->
    sig
      module Ty :
        sig
          exception Probleme
          exception Elim
          type litteral = Logic.formula
          type contrainte = Logic.constraints
          type proof_tree =
            ((litteral, contrainte) Ptypes.clause, litteral) Ptypes.tree
          val ordre : ('a, 'b) Ptypes.clause -> ('c, 'd) Ptypes.clause -> int
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
          val cndats : (litteral, contrainte) Ptypes.clause list ref
          val djvues :
            ((litteral, contrainte) Ptypes.clause *
             ((litteral, contrainte) Ptypes.clause * litteral) Hashform.t)
            list ref
          val initdjvues :
            ((litteral, contrainte) Ptypes.clause *
             ((litteral, contrainte) Ptypes.clause * litteral) Hashform.t)
            list ref
          val empty_s_clauses : (litteral, contrainte) Ptypes.clause list ref
          val initallclauses :
            (int, (litteral, contrainte) Ptypes.clause) Hashtbl.t
          val allclauses :
            (int, (litteral, contrainte) Ptypes.clause) Hashtbl.t
        end
      exception Prooftree of
                  ((Ty.litteral, Ty.contrainte) Ptypes.clause, Ty.litteral)
                  Ptypes.tree
      type 'a info = Quadr of 'a | Simpl of 'a
      type lit = { nom : Splitting.litname; pol : bool; }
      type oclause = { elts : lit info list; num : int; }
      val to_oclause : ('a, 'b) Ptypes.clause -> oclause
      val clausevide : ('a, Ty.contrainte) Ptypes.clause
      val to_clause : oclause -> ('a, Ty.contrainte) Ptypes.clause
      val alloclauses : lit list list ref
      val makelist : 'a info list -> 'a list
      val eliminate : oclause -> unit
      val is_redundant_or_change : oclause -> bool
      val proof_search :
        (Ty.litteral, Ty.contrainte) Ptypes.clause list ->
        (Ty.litteral, Ty.contrainte) Ptypes.clause ->
        ((Ty.litteral, Ty.contrainte) Ptypes.clause, Ty.litteral) Ptypes.tree
    end
