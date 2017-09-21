(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.8 $ *)
(*######################################################*)
(*			basic.ml			*)
(*######################################################*)

val print_endline : string -> unit

module Int_ord : sig type t = int val compare : 'a -> 'a -> int end
module Map : Map.S with type key = int
module Set : Set.S with type elt = int

val union : 'a list -> 'a list -> 'a list
val inter : 'a list -> 'a list -> 'a list
val subtract : 'a list -> 'a list -> 'a list
val unionq : 'a list -> 'a list -> 'a list
val interq : 'a list -> 'a list -> 'a list
val subtractq : 'a list -> 'a list -> 'a list
val uniona : ('a * 'b) list -> ('a * 'b) list -> ('a * 'b) list
val subtracta : ('a * 'b) list -> ('a * 'c) list -> ('a * 'b) list
val rma : ('a * 'b) list -> 'a -> ('a * 'b) list
val nth_try : int -> 'a list -> 'a
val cons_fst : 'a -> 'a list * 'b * 'c -> 'a list * 'b * 'c
val cons_nonempty : 'a list -> 'a list list -> 'a list list
val select : ('a -> bool) -> 'a list -> 'a list
val int_to_alpha : bool -> int -> string
val cossa : 'a -> ('b * 'a) list -> 'b
val cossaf : 'a -> ('b * ('a * 'c)) list -> 'b
val cossas : 'a -> ('b * ('a * 'c)) list -> 'c
val assoc3 : 'a -> ('a * 'b * 'c) list -> 'b * 'c
val last : 'a list -> 'a
val liat : 'a list -> 'a list
val snoc : 'a -> 'a list -> 'a list
val rev_append : 'a list -> 'a list -> 'a list
val insert : int -> 'a list -> 'a list
val extract : int -> 'a list -> 'a list
val last_in_list : int -> 'a list -> 'a list
val rotate : 'a list -> 'a list
val list_do : ('a -> unit) -> 'a list -> unit
val list_count : (int -> 'a -> unit) -> 'a list -> unit
val list_bcount : (int -> 'a -> unit) -> 'a list -> unit
val stream_map : ('a -> 'b) -> 'a -> 'b Stream.t
val best : ('a -> int) -> 'a list -> 'a * 'a list
val forall2 : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val cons_option : ('a option) -> ('a list) -> 'a list
val flat_select_map : (int -> 'a -> 'a list) -> int list -> 'a list -> (bool * 'a) list




