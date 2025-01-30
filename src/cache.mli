(*######################################################*)
(*			cache.mli			*)
(*######################################################*)

open Myhashtbl

module type Cache = sig
  type key
  type t

(* [create n hashfun eqfun] creates a new cache of size [n] using
   [hashfun] and [eqfun] as hash function and equality test. *)
  val create : int -> t

(* acces to the cache *)
  val cache : t -> key -> key

(* clear cache *)
  val clear : t -> unit
end

module Cache (Key_type : Key_type) : Cache with type key = Key_type.key
