(* $State: Exp $ $Date: 2000/10/12 09:58:26 $ $Revision: 1.1.1.1 $ *)
(*######################################################*)
(*			cache.ml			*)
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

module Cache (Key_type : Key_type) = struct
  open Key_type
  type key = Key_type.key

  module Myhashtbl = Myhashtbl.Hashtbl (Key_type)

  type cache_tbl = (key * int ref) Myhashtbl.t
  type cache_buck = (key * int ref) Myhashtbl.bucket

  type t = cache_tbl * cache_buck Queue.t * int ref * int

  let create n = 
    let tbl = Myhashtbl.create n in (tbl, Queue.create (), ref 0, n) 

  let clear (tbl, q, ptr, _) =
    Myhashtbl.clear tbl;
    Queue.clear q;
    ptr:=0

  let cache (ht, qt, nb, max) t =
    let t = Myhashtbl.add_find ht t (t, ref 0)
      (fun (t,nr) -> nr := !nr + 1; t)
      (fun buck -> Queue.add buck qt; nb := !nb + 1; t)
    in

    while !nb > max do
      let buck = Queue.take qt in 
      let (_,nr) = Myhashtbl.bucket_info buck in
      if !nr > 0 then (nr:= !nr - 1; Queue.add buck qt)
      else (Myhashtbl.fast_remove ht buck; nb := !nb - 1)
    done;

    t

end
