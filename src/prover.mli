module Prover :
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
      module Af :
        sig
          module Ty :
            sig
              exception Probleme
              exception Elim
              type litteral = Logic.formula
              type contrainte = Logic.constraints
              type proof_tree =
                ((litteral, contrainte) Ptypes.clause, litteral) Ptypes.tree
              val ordre :
                ('a, 'b) Ptypes.clause -> ('c, 'd) Ptypes.clause -> int
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
              val empty_s_clauses :
                (litteral, contrainte) Ptypes.clause list ref
              val initallclauses :
                (int, (litteral, contrainte) Ptypes.clause) Hashtbl.t
              val allclauses :
                (int, (litteral, contrainte) Ptypes.clause) Hashtbl.t
            end
          val print_clause : (Logic.formula, 'a) Ptypes.clause -> unit
          val print_clause_list :
            (Logic.formula, 'a) Ptypes.clause list -> unit
          val antsl : string
          val print_proof :
            ((Logic.formula, 'a) Ptypes.clause, Logic.formula) Ptypes.tree ->
            (int, (Logic.formula, 'a) Ptypes.clause) Hashtbl.t -> unit
        end
      module Maj :
        sig
          module Ty :
            sig
              exception Probleme
              exception Elim
              type litteral = Logic.formula
              type contrainte = Logic.constraints
              type proof_tree =
                ((litteral, contrainte) Ptypes.clause, litteral) Ptypes.tree
              val ordre :
                ('a, 'b) Ptypes.clause -> ('c, 'd) Ptypes.clause -> int
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
              val empty_s_clauses :
                (litteral, contrainte) Ptypes.clause list ref
              val initallclauses :
                (int, (litteral, contrainte) Ptypes.clause) Hashtbl.t
              val allclauses :
                (int, (litteral, contrainte) Ptypes.clause) Hashtbl.t
            end
          val tauto : (Logic.formula, 'a) Ptypes.clause -> bool
          val subsume :
            (Logic.formula, 'a) Ptypes.clause ->
            (Logic.formula, 'b) Ptypes.clause -> bool
          val majcndats :
            (Logic.formula, 'a) Ptypes.clause ->
            (Logic.formula, 'a) Ptypes.clause list ->
            ((Logic.formula, 'b) Ptypes.clause * 'c) list ->
            (Logic.formula, 'a) Ptypes.clause list
          val majdjvues :
            (Logic.formula, 'a) Ptypes.clause ->
            ((Logic.formula, 'b) Ptypes.clause * 'c) list ->
            ((Logic.formula, 'b) Ptypes.clause * 'c) list
          val add_empty_with_split :
            (Logic.formula, 'a) Ptypes.clause ->
            (Logic.formula, 'b) Ptypes.clause list ->
            ((Logic.formula, 'c) Ptypes.clause * 'd) list ->
            (Logic.formula, 'b) Ptypes.clause list *
            ((Logic.formula, 'c) Ptypes.clause * 'd) list
          val majesclauses :
            (Logic.formula, 'a) Ptypes.clause ->
            (Logic.formula, 'b) Ptypes.clause list ->
            (Logic.formula, 'b) Ptypes.clause list
        end
      module Oldd :
        sig
          module Ty :
            sig
              exception Probleme
              exception Elim
              type litteral = Logic.formula
              type contrainte = Logic.constraints
              type proof_tree =
                ((litteral, contrainte) Ptypes.clause, litteral) Ptypes.tree
              val ordre :
                ('a, 'b) Ptypes.clause -> ('c, 'd) Ptypes.clause -> int
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
              val empty_s_clauses :
                (litteral, contrainte) Ptypes.clause list ref
              val initallclauses :
                (int, (litteral, contrainte) Ptypes.clause) Hashtbl.t
              val allclauses :
                (int, (litteral, contrainte) Ptypes.clause) Hashtbl.t
            end
          exception Prooftree of
                      ((Ty.litteral, Ty.contrainte) Ptypes.clause,
                       Ty.litteral)
                      Ptypes.tree
          type 'a info =
            'a Oldeduction.Oldeduction(Logic).info =
              Quadr of 'a
            | Simpl of 'a
          type lit =
            Oldeduction.Oldeduction(Logic).lit = {
            nom : Splitting.litname;
            pol : bool;
          }
          type oclause =
            Oldeduction.Oldeduction(Logic).oclause = {
            elts : lit info list;
            num : int;
          }
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
            ((Ty.litteral, Ty.contrainte) Ptypes.clause, Ty.litteral)
            Ptypes.tree
        end
      exception Build_fails
      val initclause : ('a, Ty.contrainte) Ptypes.clause
      val new_num_clause : unit -> int
      val met : string ref
      val list_delete_nth : 'a list -> int -> 'a list * 'a
      val compare_formula : Logic.formula -> Logic.formula -> int
      val merge_perso : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
      val except : Logic.formula -> Logic.formula list -> Logic.formula list
      val add_hist_r :
        (string * (float option * int)) list ->
        string -> (string * (float option * int)) list
      val add_hist_c :
        (int * (Typespoids.indiceclause * int)) list ->
        ('a, 'b) Ptypes.clause ->
        (int * (Typespoids.indiceclause * int)) list
      val merge_hist :
        ('a * ('b * int)) list ->
        ('a * ('b * int)) list -> ('a * ('b * int)) list
      val pos_neg_list :
        Logic.formula list ->
        Logic.formula list * Logic.formula list * Logic.formula list
      val apply_subst_clause :
        Logic.substitution ->
        (Logic.formula, 'a) Ptypes.clause ->
        (Logic.formula, 'a) Ptypes.clause
      val get_renaming_clause :
        Logic.renaming ->
        (Logic.formula, Logic.constraints) Ptypes.clause -> Logic.renaming
      val rename_clause :
        Logic.renaming ->
        (Logic.formula, Logic.constraints) Ptypes.clause ->
        (Logic.formula, Logic.constraints) Ptypes.clause
      val add_hyplist_to_cndats :
        (Ty.litteral * int option * Ty.contrainte * int) list -> unit
      val add_goal_to_cndats : Ty.litteral -> unit
      val merge_except :
        Logic.formula ->
        Logic.formula list -> Logic.formula list -> Logic.formula list
      val merge_3 :
        Logic.formula list ->
        Logic.formula list -> Logic.formula list -> Logic.formula list
      val merge :
        int ->
        Logic.formula ->
        (Logic.formula, 'a) Ptypes.clause ->
        (Logic.formula, 'b) Ptypes.clause ->
        Logic.formula list ->
        Logic.formula list ->
        Logic.formula list -> (Logic.formula, 'b) Ptypes.clause
      val merge_contr :
        Logic.formula ->
        (Logic.formula, 'a) Ptypes.clause ->
        (Logic.formula, 'b) Ptypes.clause ->
        (Logic.formula, 'c) Ptypes.clause ->
        Logic.formula list ->
        Logic.formula list ->
        Logic.formula list -> (Logic.formula, 'a) Ptypes.clause
      val premajcndats :
        (Ty.litteral, Ty.contrainte) Ptypes.clause ->
        (Logic.formula, Ty.contrainte) Ptypes.clause list ->
        ((Logic.formula, Ty.contrainte) Ptypes.clause *
         ((Ty.litteral, Ty.contrainte) Ptypes.clause * Ty.litteral)
         Ty.Hashform.t)
        list -> (Logic.formula, Ty.contrainte) Ptypes.clause list
      val split_clause :
        (Ty.MapSplit.key, Ty.contrainte) Ptypes.clause ->
        (Ty.MapSplit.key, Ty.contrainte) Ptypes.clause list
      val decompose_clause :
        (Ty.litteral, Ty.contrainte) Ptypes.clause ->
        (Ty.litteral, Ty.contrainte) Ptypes.clause *
        ((Ty.litteral, Ty.contrainte) Ptypes.clause * Ty.litteral)
        Ty.Hashform.t
      val subcase : 'a list -> 'b list -> 'a list -> 'b list -> bool
      val build_resolvante :
        (Logic.formula, Logic.constraints) Ptypes.clause ->
        Logic.formula ->
        (Logic.formula, Logic.constraints) Ptypes.clause ->
        Logic.formula ->
        int * Logic.formula *
        (Logic.formula, Logic.constraints) Ptypes.clause *
        (Logic.formula, Logic.constraints) Ptypes.clause *
        Logic.formula list * Logic.formula list * Logic.formula list *
        Logic.constraints
      val contract :
        Logic.formula ->
        (Logic.formula, 'a) Ptypes.clause ->
        (Logic.formula, 'b) Ptypes.clause ->
        Logic.constraints ->
        (Logic.formula * (Logic.formula, 'a) Ptypes.clause *
         (Logic.formula, 'b) Ptypes.clause * Logic.constraints *
         Logic.constraints * Logic.formula list * Logic.formula list *
         Logic.formula list)
        list
      val add_resol :
        (Ty.litteral, Logic.constraints) Ptypes.clause ->
        Logic.formula ->
        (Ty.litteral, Logic.constraints) Ptypes.clause ->
        Logic.formula -> unit
      val all_resol :
        (Ty.litteral, Ty.contrainte) Ptypes.clause *
        ((Ty.litteral, Ty.contrainte) Ptypes.clause * Ty.litteral)
        Ty.Hashform.t -> unit
      val list_sub : 'a list -> int -> 'a list
      val axiom : Logic.formula * int option * Ty.contrainte * int -> unit
      val real_init : 'a -> unit
      val init : 'a -> unit
      val time_out : 'a -> 'b
      val prove :
        ?methode:string ->
        (Ty.litteral * int option * Ty.contrainte * int) list ->
        Ty.litteral -> unit
    end
