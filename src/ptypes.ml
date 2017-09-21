open Logic
open Typespoids
open Splitting

type adresse = bool list

(* Donne l'arbre des origines d'une clause *)

type 'a origine =
    Resol of int * 'a origine * int * 'a origine * 'a (* int est le num�ro des clauses *)
  | Decomp of int * 'a origine * 'a * string (* le string est le nom de la r�gle *)
  | Contrac of int * 'a origine * 'a (* le dernier 'a est le litt�ral contract� *)
  | Split of int * 'a origine * int (* le dernier int est le num�ro du paquet *)
  | Donne

type ('a,'b) clause =
    {
     litx_pos : 'a list      ; (* litt�raux positifs *)
     litx_neg : 'a list      ; (* litt�raux n�gatifs *)
     litx_ukn : 'a list      ; (* litt�raux inconnus (variables d'unif) *)
     litx_ps  : litname list ; (* litt�raux positifs provenant de splitting *)
     litx_ns  : litname list ; (* litt�raux n�gatifs provenent de splitting *)
     poids : poidsclause     ; (* poids de la clause *)
     vientde : 'a origine    ; (* origine de la clause pour retracer les preuves *)
     numero : int            ; (* num�ro de la clause *)
     contr : 'b ref          ; (* contraintes sur la clause *)
     indice : indiceclause   ; (* indice de la clause (r�utilisation) *)
     histclist : (int * (indiceclause * int)) list; (* historique d'utilisation de clauses *)
     histrlist : (string * (indiceclause * int)) list; (* historique d'utilisation de r�gles *)
   }



(* un type identique � origine, mais pour l'affichage *)

type ('a, 'b) tree =
    Feuille of 'a
  | Nr of 'a * 'b * ('a, 'b) tree * ('a, 'b) tree (* r�solution ; clause, litt�ral, et arbres *)
  | Nrs of 'a * litname * ('a, 'b) tree * ('a, 'b) tree (* r�solution sur lit de split *)
  | Nd of 'a * 'b * string * ('a, 'b) tree  (* d�composition ; clause, litt�ral, nom de la r�gle, et arbre *)
  | Nc of 'a * 'b * ('a,'b) tree (* contraction ; clause, litt�ral et arbre *)
  | Ns of 'a * int * ('a, 'b) tree (* splitting ; clause, num�ro du paquet et arbre *)
  | Mktree of 'a (* arbre de preuve � faire *)
  | Central of 'a * litname * ('a,'b) tree (* OL-d�duction utilisation de clause centrale *)
                                           (* litname est le litt�ral r�solu *)

(* Exceptions de sortie du prouveur *)

exception Proved

exception Prove_fails


(* exception pour le splitting (clause vide sauf variables de splitting) *)

exception EmptySplit


(* cas o� l'OL-deduction ne trouve pas *)

exception Noprinting


(* Variable du mode verbeux MODIFIABLE *)

let verbose = ref 1

(* variable qui autorise ou non l'arr�t du prouver � chaque �tape lors d'un mode verbeux MODIFIABLE *)

let pause = ref false

(* Variable qui restreint la liste des candidats MODIFIABLE *)

let maxcndts = ref 40

(* option du splitting MODIFIABLE *)

let splitting = ref true

(* option sur le fait de v�rifier les sous-cas MODIFIABLE *)

let check_subcase = ref true

(* Variable pour savoir si l'on trace la preuve MODIFIABLE *)

let trace_proof = ref true

(* donne le num�ro de la clause vide *)

let empty_clause = ref 0

(* calcul en temps r�el du nombre de candidats *)

let taillecndats = ref 0

(* temps maximal donn� au prouveur *)
(* si 0 temps illimit� MODIFIABLE *)

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

(* Permet d'�liminer une clause : subsum�e ou vraie (donc inutile) *)

  exception Elim

(* Sortie quand la preuve est faite, ie la clause vide est trouv�e *)

  type litteral = formula (* formula est donn�e dans Logic *)

  type contrainte = constraints

  type proof_tree = ((litteral,contrainte) clause,litteral) tree

(* fonction d'ordre sur les clauses par leur poids *)

  let ordre c1 c2 = 
    ordrepoids c1.poids c2.poids



  let longueur f = (* d�fini dans Logic *)
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


      (* cndats d�finie comme valeur globale *)

  let cndats
      : ((litteral,contrainte) clause list) ref
      = ref []

      (* djvues d�finie comme valeur globale *)

  let djvues
      : ((litteral,contrainte) clause * ((litteral,contrainte) clause * litteral) Hashform.t) list ref
      = ref []

  let initdjvues = ref (!djvues)

      (* les clauses vides avec des litt�raux de splitting *)
      (* ensemble satisfaisable *)

  let empty_s_clauses
      : ((litteral,contrainte) clause) list ref
      = ref []

      (* allclauses d�finie comme valeur glogale *)

  let initallclauses
      : (int,(litteral,contrainte) clause) Hashtbl.t
      = Hashtbl.create 10007

  let allclauses
      : (int,(litteral,contrainte) clause) Hashtbl.t
      = Hashtbl.create 10007

end
