open Logic
open Typespoids
open Splitting

type adresse = bool list

(* Donne l'arbre des origines d'une clause *)

type 'a origine =
    Resol of int * 'a origine * int * 'a origine * 'a (* int est le numéro des clauses *)
  | Decomp of int * 'a origine * 'a * string (* le string est le nom de la règle *)
  | Contrac of int * 'a origine * 'a (* le dernier 'a est le littéral contracté *)
  | Split of int * 'a origine * int (* le dernier int est le numéro du paquet *)
  | Donne

type ('a,'b) clause =
    {
     litx_pos : 'a list      ; (* littéraux positifs *)
     litx_neg : 'a list      ; (* littéraux négatifs *)
     litx_ukn : 'a list      ; (* littéraux inconnus (variables d'unif) *)
     litx_ps  : litname list ; (* littéraux positifs provenant de splitting *)
     litx_ns  : litname list ; (* littéraux négatifs provenent de splitting *)
     poids : poidsclause     ; (* poids de la clause *)
     vientde : 'a origine    ; (* origine de la clause pour retracer les preuves *)
     numero : int            ; (* numéro de la clause *)
     contr : 'b ref          ; (* contraintes sur la clause *)
     indice : indiceclause   ; (* indice de la clause (réutilisation) *)
     histclist : (int * (indiceclause * int)) list; (* historique d'utilisation de clauses *)
     histrlist : (string * (indiceclause * int)) list; (* historique d'utilisation de règles *)
   }



(* un type identique à origine, mais pour l'affichage *)

type ('a, 'b) tree =
    Feuille of 'a
  | Nr of 'a * 'b * ('a, 'b) tree * ('a, 'b) tree (* résolution ; clause, littéral, et arbres *)
  | Nrs of 'a * litname * ('a, 'b) tree * ('a, 'b) tree (* résolution sur lit de split *)
  | Nd of 'a * 'b * string * ('a, 'b) tree  (* décomposition ; clause, littéral, nom de la règle, et arbre *)
  | Nc of 'a * 'b * ('a,'b) tree (* contraction ; clause, littéral et arbre *)
  | Ns of 'a * int * ('a, 'b) tree (* splitting ; clause, numéro du paquet et arbre *)
  | Mktree of 'a (* arbre de preuve à faire *)
  | Central of 'a * litname * ('a,'b) tree (* OL-déduction utilisation de clause centrale *)
                                           (* litname est le littéral résolu *)

(* Exceptions de sortie du prouveur *)

exception Proved

exception Prove_fails


(* exception pour le splitting (clause vide sauf variables de splitting) *)

exception EmptySplit


(* cas où l'OL-deduction ne trouve pas *)

exception Noprinting


(* Variable du mode verbeux MODIFIABLE *)

let verbose = ref 1

(* variable qui autorise ou non l'arrêt du prouver à chaque étape lors d'un mode verbeux MODIFIABLE *)

let pause = ref false

(* Variable qui restreint la liste des candidats MODIFIABLE *)

let maxcndts = ref 40

(* option du splitting MODIFIABLE *)

let splitting = ref true

(* option sur le fait de vérifier les sous-cas MODIFIABLE *)

let check_subcase = ref true

(* Variable pour savoir si l'on trace la preuve MODIFIABLE *)

let trace_proof = ref true

(* donne le numéro de la clause vide *)

let empty_clause = ref 0

(* calcul en temps réel du nombre de candidats *)

let taillecndats = ref 0

(* temps maximal donné au prouveur *)
(* si 0 temps illimité MODIFIABLE *)

let timemax = ref 30

module type Types =
  sig
    type litteral
    type contrainte
    type proof_tree
    val ordre : (litteral,contrainte) clause -> (litteral,contrainte) clause -> int
    val longueur : litteral -> int
    module MapSplit : Map.S
    val memory_split : (litname MapSplit.t) ref
    module Hashform : Hashtbl.S
    val cndats : (litteral,contrainte) clause list ref
    val djvues : ((litteral,contrainte) clause * ((litteral*bool),((litteral,contrainte) clause * litteral)) Hashtbl.t) list ref
    val initdjvues : ((litteral,contrainte) clause * ((litteral*bool),((litteral,contrainte) clause * litteral)) Hashtbl.t) list ref
    val empty_s_clauses : ((litteral,contrainte) clause) list ref
    val initallclauses : (int,(litteral,contrainte) clause) Hashtbl.t
    val allclauses : (int,(litteral,contrainte) clause) Hashtbl.t
  end

module Types(Logic:Logic) = struct

  open Logic


(* Exceptions *)


(* Cas de mauvaise lecture d'une formule ou cas impossible *)

  exception Probleme

(* Permet d'éliminer une clause : subsumée ou vraie (donc inutile) *)

  exception Elim

(* Sortie quand la preuve est faite, ie la clause vide est trouvée *)

  type litteral = formula (* formula est donnée dans Logic *)

  type contrainte = constraints

  type proof_tree = ((litteral,contrainte) clause,litteral) tree

(* fonction d'ordre sur les clauses par leur poids *)

  let ordre c1 c2 = 
    ordrepoids c1.poids c2.poids



  let longueur f = (* défini dans Logic *)
    size f

  module OrderedLit =
    struct
      type t = litteral
      let compare f1 f2 =
	if equal_formula f1 f2 then 0 else compare f1 f2
    end

  module MapSplit = Map.Make(OrderedLit)

  let memory_split : (litname MapSplit.t) ref = ref MapSplit.empty


  module Hashform = Hashtbl.Make(FormHashType)
      (* module de tables de hashage pour les formules *)


      (* cndats définie comme valeur globale *)

  let cndats
      : ((litteral,contrainte) clause list) ref
      = ref []

      (* djvues définie comme valeur globale *)

  let djvues
      : ((litteral,contrainte) clause * ((litteral,contrainte) clause * litteral) Hashform.t) list ref
      = ref []

  let initdjvues = ref (!djvues)

      (* les clauses vides avec des littéraux de splitting *)
      (* ensemble satisfaisable *)

  let empty_s_clauses
      : ((litteral,contrainte) clause) list ref
      = ref []

      (* allclauses définie comme valeur glogale *)

  let initallclauses
      : (int,(litteral,contrainte) clause) Hashtbl.t
      = Hashtbl.create 10007

  let allclauses
      : (int,(litteral,contrainte) clause) Hashtbl.t
      = Hashtbl.create 10007

end
