(* $State: Exp $ $Date: 2001/01/18 10:18:46 $ $Revision: 1.3 $ *)
(*######################################################*)
(*			files.mli			*)
(*######################################################*)

(* Attention : 
     ouverture de "type.mli" pour l'exception Error, 
     a par ca ce fichier est portable *)

(* gestion d'une liste de canaux d'entree utilise pour
   la commande include *)

(* exception qui est leve quand on ferme le dernier fichier de la liste *)
exception Quit
exception Restart

(* pointeur sur le  canal d'entree courant *)
val cur_input : in_channel ref
val cur_line : int ref
val cur_col : int ref

(* termine la lecture du canal courant et reprend la lecture du suivant 
   dans la liste *)
val pop_input : unit -> unit

(* ferme tous les canaux sauf le dernier de la liste (utilise pour 
   remonter au "top_level") *)
val pop_all : unit -> unit

val open_path : string -> in_channel

(* ouvre un fichier en lecture, et l'ajoute dans la liste. 
   moodifie la valeur de cur_input pour pointer sur le nouveau canal *)
val read_file : string -> unit

(* add a path to the path list *)
val add_path : string -> unit

(* set the path from its default value *)
val set_path : unit -> unit

(* print all the path *)
val print_path : unit -> unit

val path_list : string list ref

val is_top : unit -> bool
