(* $State: Exp $ $Date: 2005/02/28 14:10:07 $ $Revision: 1.5 $ *)
(*######################################################*)
(*			data_base.mli			*)
(*######################################################*)

(* gestion d'une base d'un "ensemble de donnees" modulaire *)

(* note : la modularite n'est pas encore completement implementee !! *)

module Object : sig
  type 'a o_object
  type ('a,'b) o_extern

  (* get_name o
      renvoie le nom de l'objet encapsule o *)
  val get_name : 'a o_object -> string

  (* get_key o
      renvoie la "clef" de l'objet encapsule o *)
  val get_key : 'a o_object -> int

  (* get_value o
      renvoie la valeur de l'objet encapsule o *)
  val get_value : 'a o_object -> 'a

  (* To construct the encapsuled table. Use it ONLY to construct
     the initial tables in the init_base fonction *)
  val mk_ext : string -> 'b -> ('a,'b) o_extern

  val get_ext_tbl : ('a,'b) o_extern -> 'b
  val get_ext_name : ('a,'b) o_extern -> string
  val is_locked : 'a o_object -> bool
end

module type Data = sig
  type symbol
  type tbl_types
  type renaming
  type obj = symbol Object.o_object
  type extern = (symbol,tbl_types) Object.o_extern

  val sub_obj : symbol -> obj list
  val sp_new : unit -> extern array
  val sp_sub : extern -> obj list
  val sp_del : obj list -> extern -> unit

  val sp_write : out_channel -> unit
  val sp_read : in_channel -> (string * renaming) list
  val recursive : bool ref
end

module type Base = sig
  type symbol
  type tbl_types
  type renaming
  type obj = symbol Object.o_object
  type extern = (symbol,tbl_types) Object.o_extern

  (* type of a base *)
  type base

  (* exception levee en cas d'erreur *)
  exception Base_failure of string

  (* exception levee en cas de tentative de redefinition d'un symbol *)
  exception All_ready_def

  (* exception levee en cas de definition recursive d'un symbol *)
  exception Rec_def

  val dummy_object : symbol -> obj

  val capsule_object : string -> symbol -> int -> obj
  val is_capsule : obj -> bool
  val rename_capsule : obj -> string -> unit -> unit

  val dummy_base : unit -> base

  val load_base :  string list -> string -> base * (string * renaming) list
  val new_base :  unit -> base

  (* save_base b
      sauve la base b (en ecrasant eventuellement l'ancienne version) *)
  val save_base : base -> string -> unit

  (* base_get b name
      recherche l'objet de nom "name" dans la base b *)
  val base_get : base -> string -> obj

  (* base_rename o name
      change the name of the object o *)
  val base_rename : obj -> string -> unit

  (* base_add b name x l
      ajoute l'objet x dans la base b sous le nom "name" (side effect)
      et renvoie une version encapsule de l'objet x. le boolene l indique
      si l'objet est "locked" *)
  val base_add : base -> string -> symbol -> bool -> obj

  (* base_remove b o
      supprime l'objet o de la base b
      Attention, tous les objets referencant o doivent avoir ete supprimes
      de la base, sinon une exception est levee *)
  val base_remove : bool -> base -> obj -> unit

  (* to update the link after a modification of a table *)
  val update_ext_link : extern -> unit

  (* To read the table *)
  val get_table_byname : base -> string -> extern
  val do_ext_table : base -> (extern -> unit) -> unit

  (* rec_remove b o
      supprime l'objet o de la base b
      Attention, tous les sous-objets referencant o sont recursivement
      supprimes *)
  val rec_remove : bool -> base -> obj -> unit

  val ext_remove : extern -> obj list -> unit

  (* set_value o
      Change the val of the object o *)
  val set_value : base -> obj -> symbol -> unit

  (* get_rlink filter o
      Get all the object recursively using o and verifying filter *)
  val get_rlink : (obj -> bool) -> obj -> obj list
  val get_link : obj -> obj list

  val obj_cmp : obj -> obj -> bool

  val do_base : (obj -> unit) -> base -> unit
  val it_base : (obj -> 'a -> 'a) -> 'a -> base -> 'a

  val filter_base : (obj -> bool) -> base -> obj list

  val is_recursive : obj -> bool

end

module Base (Data : Data) : Base
  with type symbol = Data.symbol
  and  type tbl_types = Data.tbl_types
  and  type renaming = Data.renaming
