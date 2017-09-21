(* $State: Exp $ $Date: 2006/02/24 17:01:53 $ $Revision: 1.3 $ *)
(* Hash tables *)

(* We do dynamic hashing, and we double the size of the table when
   buckets become too long, but without re-hashing the elements. *)

let mo x y =
  let r = x mod y in
  if r < 0 then r + y else r

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

module Poly_Key_type (Type : sig type key end) = struct
  type key = Type.key

  let hash k = Hashtbl.hash_param 10 100 k
  let eq = (=)
end

module Hashtbl (Key_type : Key_type) = struct
  open Key_type

  type tmp = key
  type key = tmp
  type 'a t =
    { mutable max_len: int;                    (* max length of a bucket *)
      mutable data: 'a bucketlist array}

  and 'a bucketlist =
      Empty
    | Cons of 'a bucket

  and 'a bucket =
    {hash : int; key : key; mutable hval : 'a;
     mutable next : 'a bucketlist}

  let bucket_info buck = buck.hval
  let bucket_key buck = buck.key

  let create initial_size =
    { max_len = 1; data = Array.make initial_size Empty }

  let clear h =
    for i = 0 to Array.length h.data - 1 do
      h.data.(i) <- Empty
    done

  let resize h =
    let n = Array.length h.data in
    let nn = n+n in
    let newdata = Array.make nn Empty in
      let rec fn = function
        Empty -> ()
      | Cons ({hash = hn; next = rest} as bucket) ->
          fn rest;
          let r = newdata.(mo hn nn) in
          bucket.next <- r; newdata.(mo hn nn) <- Cons bucket
      in Array.iter fn h.data;
      h.data <- newdata;
      ()

  let rec bucket_too_long hl n bucket =
    if n < 0 then true else
      match bucket with
        Empty -> false
      | Cons{hash = hash; next = rest} ->
          if List.mem hash hl then
            bucket_too_long hl n rest
          else
            bucket_too_long (hash::hl) n rest

  let add h key info =
    let hn = hash key in
    let i = mo hn (Array.length h.data) in
    let bucket = Cons{hash = hn; key=key; hval=info; next=h.data.(i)} in
      h.data.(i) <- bucket;
      if bucket_too_long [] h.max_len bucket then resize h

  let badd h key info =
    let hn = hash key in
    let i = mo hn (Array.length h.data) in
    let bucket = {hash = hn; key=key; hval=info; next=h.data.(i)} in
      h.data.(i) <- Cons bucket;
      if bucket_too_long [] h.max_len h.data.(i) then resize h;
      bucket

  let remove h key =
    let i = mo (hash key) (Array.length h.data) in

    match h.data.(i) with
      Empty -> raise Not_found
    | Cons({key = k1; next = rest1} as buck1) ->
        if eq key k1 then h.data.(i) <- rest1 else
        match rest1 with
          Empty -> raise Not_found
        | Cons({key = k2; next = rest2} as buck2) ->
            if eq key k2 then buck1.next <- rest2 else
            match rest2 with
              Empty -> raise Not_found
            | Cons({key = k3; next = rest3} as last) ->
                if eq key k3 then buck2.next <- rest3 else begin
                  let rec rm ({next = pr} as buck) = function
                      Empty ->
                        raise Not_found
                    | Cons({key = k; next = rest} as last) ->
                        if eq key k then buck.next <- rest else rm last rest
                  in rm last rest3
                end

  let fast_remove h ({hash = hn} as bucket) =
    let i = mo hn (Array.length h.data) in

    match h.data.(i) with
      Empty -> raise Not_found
    | Cons({next = rest1} as buck1) ->
        if buck1 == bucket then h.data.(i) <- rest1 else
        match rest1 with
          Empty -> raise Not_found
        | Cons({next = rest2} as buck2)->
            if buck2 == bucket then buck1.next <- rest2 else
            match rest2 with
              Empty -> raise Not_found
            | Cons({next = rest3} as buck3) ->
                if buck3 == bucket then buck2.next <- rest3 else begin
                  let rec rm ({next = pr} as obuck) = function
                      Empty ->
                        raise Not_found
                    | Cons({next = rest} as buck) ->
                        if buck == bucket then obuck.next <- rest
                                          else rm buck rest
                  in rm buck3 rest3
                end


  let find h key =
    match h.data.(mo (hash key) (Array.length h.data)) with
      Empty -> raise Not_found
    | Cons{key = k1; hval = d1; next = rest1} ->
        if eq key k1 then d1 else
        match rest1 with
          Empty -> raise Not_found
        | Cons{key = k2; hval = d2; next = rest2} ->
            if eq key k2 then d2 else
            match rest2 with
              Empty -> raise Not_found
            | Cons{key = k3; hval = d3; next = rest3} ->
                if eq key k3 then d3 else begin
                  let rec find = function
                      Empty ->
                        raise Not_found
                    | Cons{key = k; hval = d; next = rest} ->
                        if eq key k then d else find rest
                  in find rest3
                end

  let add_find h key info ft fn =
    let hn = hash key in
    let i = mo hn (Array.length h.data) in
    let rec find = function
      Empty ->
        let bucket = {hash = hn; key=key; hval=info; next=h.data.(i)} in
        h.data.(i) <- Cons bucket;
        if bucket_too_long [] h.max_len h.data.(i) then resize h;
        fn bucket
    | Cons{key = k; hval = d; next = rest} ->
        if eq key k then ft d else find rest
    in find h.data.(i)

  let find_all h key =
    let rec find_in_bucket = function
      Empty ->
        []
    | Cons{key = k; hval = d; next = rest} ->
        if eq k key then d :: find_in_bucket rest
                         else find_in_bucket rest in
    find_in_bucket h.data.(mo (hash key) (Array.length h.data))

  let do_table f h =
    let len = Array.length h.data in
    for i = 0 to len - 1 do
      let rec do_bucket = function
          Empty ->
            ()
        | Cons{key = k; hval = d; next = rest} ->
            f k d; do_bucket rest in
      do_bucket h.data.(i)
    done

  let it_table f a h =
    let len = Array.length h.data in
    let res = ref a in
    for i = 0 to len - 1 do
      let rec do_bucket = function
          Empty ->
            ()
        | Cons{key = k; hval = d; next = rest} ->
            res := f !res k d; do_bucket rest in
      do_bucket h.data.(i)
    done;
    !res

end

module Poly_Hashtbl (Type : sig type key end) =
  Hashtbl (Poly_Key_type (Type))
