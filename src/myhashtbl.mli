(* $State: Exp $ $Date: 2000/10/12 09:58:27 $ $Revision: 1.1.1.1 $ *)
(* Hash tables and hash functions *)

(* Hash tables are hashed association tables, with in-place modification. *)

module type Key_type = sig
  type key
  val hash : key -> int
  val eq : key -> key -> bool
end

module type Hashtbl = sig
  type key
  (* The type of hash tables from type [key] to type ['a]. *)
  type 'a t
  (* The bucket type (usefull for fast_remove) *)
  type 'a bucket

  val create : int -> 'a t
        (* [create n] creates a new, empty hash table, with initial size [n].
           The table grows as needed, so [n] is just an initial guess.
           Better results are said to be achieved when [n] is a prime
           number. *)
  val clear : 'a t -> unit
        (* Empty a hash table. *)

  val add : 'a t -> key -> 'a -> unit
        (* [add tbl x y] adds a binding of [x] to [y] in table [tbl].
           Previous bindings for [x] are not removed, but simply
           hidden. That is, after performing [remove tbl x], the previous
           binding for [x], if any, is restored.
           (This is the semantics of association lists.) *)

  val badd : 'a t -> key -> 'a -> 'a bucket
        (* same has add but send the bucket back *)

  val find : 'a t -> key -> 'a
        (* [find tbl x] returns the current binding of [x] in [tbl],
           or raises [Not_found] if no such binding List.exists. *)

  val find_all : 'a t -> key -> 'a list
        (* [find_all tbl x] returns the list of all data associated with [x]
           in [tbl]. The current binding is returned first, then the previous
           bindings, in reverse order of introduction in the table. *)

  val remove : 'a t -> key -> unit
        (* [remove tbl x] removes the current binding of [x] in [tbl],
           restoring the previous binding if it List.exists.
           It does nothing if [x] is not bound in [tbl]. *)

  val fast_remove : 'a t -> 'a bucket -> unit
        (* [remove tbl x] removes the current binding of [x] in [tbl],
           restoring the previous binding if it List.exists.
           It does nothing if [x] is not bound in [tbl]. *)

  val do_table : (key -> 'a -> 'c) -> 'a t -> unit
        (* [Hashtbl.iter f tbl] applies [f] to all bindings in table [tbl],
	   discarding all the results.
           [f] receives the key as first argument, and the associated val
           as second argument. The order in which the bindings are passed to
           [f] is unpredictable. Each binding is presented one time to [f]. *)

  val it_table : ('c -> key -> 'a -> 'c) -> 'c -> 'a t -> 'c
        (* [Hashtbl.iter f a tbl] is similar to fold_left2 f a l1 l2 where 
           l1 is the list of all key in tbl and l2 the list of all data.
           The order in which bindings are passed to [f] is unpredictable. *)

  val add_find : 'a t -> key -> 'a -> ('a -> 'c) -> ('a bucket -> 'c) -> 'c
        (* [add_find tbl x y f g] if the key [x] is bound to [z] in [tbl] 
            then [f z] is called otherwise a new binding from [x] to [y] is 
            added to [tbl] hand [g] is called on the newly created bucket. *)

  val bucket_info : 'a bucket -> 'a
  val bucket_key : 'a bucket -> key

end

module Hashtbl (Key_type : Key_type) : Hashtbl 
  with type key = Key_type.key

module Poly_Hashtbl (Type : sig type key end) : Hashtbl 
  with type key = Type.key


