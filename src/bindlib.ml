(* We need set of integers : *)
module Int_ord = struct
  type t = int
  let compare = compare
end
module Set = Set.Make(Int_ord)

(* merge l l' merge two sorted lists in one sorted list without repetition *)
let rec merge l l' =
  match l, l' with
    [], l -> l
  | l, [] -> l
  | ((x,_ as c)::ls as l),((x',_ as c')::ls' as l') ->
    if x = x' then merge ls l'
    else if x <= x' then c::(merge ls l')
    else c'::(merge l ls')

(* diffs l computes the set of all (y - x) for x and y distinct in l *)
let rec diffs acc res = function
  [] -> res
| x::l ->
    let rec gn acc res = function
      [] -> diffs (x::acc) res l
    | y::l -> gn acc (Set.add (y - x) res) l
    in gn acc res acc

let rec diffs' acc res = function
  [] -> acc, res
| (x,_)::l ->
    let rec gn acc res = function
      [] -> diffs' (x::acc) res l
    | y::l -> gn acc (Set.add (y - x) res) l
    in gn acc res acc

(* ppcnd l computes the smallest number n such that for any x and y distinct*)
(* in l, x mod n <> y mod n *)
let ppcnd l l' =
  let n = ref (List.length l + List.length l') in
  if !n < 2 then !n else
  let acc, s = diffs' [] Set.empty l' in
  let s = diffs acc s l in
  try while true do
    try
      Set.iter (fun p -> if p mod !n = 0 then raise Not_found) s;
      raise Exit
    with Not_found -> incr n
  done; 0 with Exit -> !n

(* search n l, remove the first occurrence of n in the sorted list l *)
let rec search n = function
    [] -> raise Not_found
  | (n',_ as c) ::ls ->
      if n < n' then
	raise Not_found
      else if n > n' then
	c::(search n ls)
      else
      	ls

(* no comment *)
let get_next = function
  [] -> 0
| x::_ -> x


(* the exception raised when start_term is called on a non-closed term *)
exception Bindlib_error

(* the type of binder: ('a,'b) binder is an expression of type 'b with a bound*)
(* variable of type 'a *)
(*  exported abstract *)
type ('a,'b) binder = 'a -> 'b

(* the substitution, it is just an application ! *)
let subst f x = f x

(* the environment type: it is used to store the value of all bound
   variables. We need the "Obj" module because all the bound variable
   may have diffrent types and we want to store them in an array *)

type environment = Obj.t array

(* the type of expression of type 'a using binder and under construction *)
type 'a pre_term =

    (* the term as no free variable *)
    Closed of 'a

    (* the general case : *)
    (* Open(vt,bt,t):
         what "t" means :
           if v is an array olding the value of all the free variable of the
           constructed term, the (t v) will be the this term where the free
           variable have been subsituted with their value
         vt is the list of all free variable in the term
         bt is a list of bound variable of the term that have a place reserved
           for their value in the Aenvironment "v" you may give to "t". This is
           provided To avoid building a new array (or closure) each time you
           descend under a binder
    *)
  | Open of (int * (Obj.t -> Obj.t) option) list *
	int list * (environment -> 'a)

(* Construct a 'a pre_term to represent the variable numbered var
   You can notice that we use the environment to store values as a hashtable
   with no failure (we always find the value the first time we look for it)
   The last case in the environment is used to store the position of the next
   variable we can assign in the environment.
*)
let mk_var var =
    Open([var, None], [],
	 fun v -> Obj.magic v.(var mod (Array.length v - 1)))

(* A version to use when we want to be able to call start_term when this
   variable is "free" *)
let mk_var_val var fn =
    Open([var, Some (Obj.magic fn)], [],
	 fun v -> Obj.magic v.(var mod (Array.length v - 1)))

(* take a ter of type 'a and turn it into a 'a pre_term taht can be used to*)
(* construct a larger term with binder *)
let unit t = Closed(t)

(* take a function t and an environment v and create an environment nv with*)
(* places for future values of bound variable that t needs. table is an array*)
(* containing the free variable, nsize if the required size of the new array*)
(* and next is the first bound variable that may be assigned is the new array *)
let mk_select next nsize table t v =
  let nb_global = Array.length table in
  let osize = (Array.length v) - 1 in
  let nv = Array.make (nsize + 1) (Obj.repr next) in
  for i = 0 to nb_global - 1 do
    nv.(table.(i) mod nsize) <- v.(table.(i) mod osize)
  done;
  t nv

(* select, takes a term t waiting for an environment with the value of the*)
(* free variable listed in "frees" and the value and the bound variable that*)
(* have a reserved place listed in bounds and transform it into a a term that*)
(* wait for an environment with no reserved place for bound variable *)
let select frees bounds t =
  match bounds with
    [] -> t
  | next::_ ->
      let table = Array.of_list (List.map fst frees) in
      let nsize = ppcnd bounds frees in
      mk_select next nsize table t

let mk_apply f a v = f v (a v)
let mk_lapply f a v = f (a v)
let mk_rapply f a v = f v a

let mk_lapply_test f a v = f false (a v)

(* the "bind" function of the monad: take an object of type ('a -> 'b)*)
(* pre_term, that is a function with some free variables, an argument of type*)
(* 'a  pre_term, and build the application, of type 'b pre_term which is a*)
(* term that may also have free variables *)
(* The function select is used here to build the "minimal" closure when both*)
(* the function and the argument have free variables *)
let apply tf ta =
  match tf, ta with
    Closed(f), Closed (a) -> Closed (f a)
  | Closed(f), Open(va,ba,a) ->
      Open(va,ba,mk_lapply f a)
  | Open(vf,bf,f), Closed(a) ->
      Open(vf, bf, mk_rapply f a)
  | Open(vf,bf,f), Open(va,ba,a) ->
      let vars = merge vf va in
      Open(vars, [],
	   mk_apply (select vf bf f) (select va ba a))

(* Used in some cases ! *)
let bind_apply = apply

(* used for a binder when you bind a variable in closed term (therefore that*)
(* variable does not occur in the term ! *)
let mk_closed_bind pt _ =
  pt

(* used for binder which binds a variable with no occurrence (but the term has*)
(* other free variables *)
let mk_mute_bind pt v _ =
  pt v

(* used for the first binder in a closed term (the binder that binds the last*)
(* free variable in a term and make it a close term *)
let mk_first_bind var_mod_size next sizep pt arg =
  let v = Array.make sizep (Obj.repr next) in
  v.(var_mod_size) <- Obj.repr arg;
  pt v

(* used for the general case of a binder *)
let mk_bind var next pt v arg =
  let size = Array.length v - 1 in
  if (Obj.magic v.(size) : int) = var then begin
    v.(size) <- Obj.repr next;
    v.(var mod size) <- Obj.repr arg;
    pt v
  end else begin
    let nv = Array.copy v in
    nv.(size) <- Obj.repr next;
    nv.(var mod size) <- Obj.repr arg;
    pt nv
  end

(* the function that creates the number of a new variable *)
let new_var =
  let count = ref 0 in
  fun () -> incr count; !count

let bind_aux v = function
     Closed(t) ->
       Closed (mk_closed_bind t)
   | Open(vt,bt,t) ->
       try
         match vt with
          [var, _] ->
            if v <> var then raise Not_found;
            let next = get_next bt in
            let size = ppcnd (var::bt) [] in
            Closed (mk_first_bind (var mod size) next (size+1) t)
        | og ->
            let ng = search v og in
            let lg = v::bt in
            let next = get_next bt in
            Open(ng, lg, mk_bind v next t)
      with Not_found ->
	Open(vt, bt, mk_mute_bind t)

(* take a function of type ('a -> 'b) pre_term and transform it into a binder*)
(* of type ('a -> 'b) binder pre_term *)
let bind fpt =
  let v = new_var () in
  bind_aux v (fpt (mk_var v))

let bind_val bv fpt =
  let v = new_var () in
  bind_aux v (fpt (mk_var_val v bv))

(* When a term has no free variable, you can get it ! *)
let start_term = function
   Closed(t) -> t
 | Open(vt,bt,t) ->
     let size = ppcnd bt vt in
     let next = get_next bt in
     let env = Array.make (size+1) (Obj.repr next) in
     List.iter (function
       _, None ->
         raise Bindlib_error
     | var, Some fn ->
         env.(var mod size) <- fn (Obj.repr (mk_var_val var fn))) vt;
     t env

let is_closed = function
   Closed(_) -> true
 | _ -> false

(* Here are some usefull function *)
(* Some of them are optimised (the comment is the simple definition) *)

(*
let unit_apply f ta = apply (unit f) ta
*)
let unit_apply f ta =
  match ta with
    Closed(a) -> Closed (f a)
  | Open(va,ba,a) ->
      Open(va, ba, mk_lapply f a)

let unit_apply_test f ta =
  match ta with
    Closed(a) -> Closed (f true a)
  | Open(va,ba,a) ->
      Open(va, ba, mk_lapply_test f a)

(*
let unit_apply2 f t t' = apply (unit_apply f t) t'
*)

let mk_apply2 f a b v = f (a v) (b v)
let mk_lapply2 f a b v = f a (b v)
let mk_rapply2 f a b v = f (a v) b
let mk_apply2_test f a b v = f false (a v) (b v)
let mk_lapply2_test f a b v = f false a (b v)
let mk_rapply2_test f a b v = f false (a v) b

let unit_apply2 f ta tb =
  match ta, tb with
    Closed(a), Closed(b) -> Closed (f a b)
  | Closed(a), Open(vb,bb,b) ->
      Open(vb, bb, mk_lapply2 f a b)
  | Open(va,ba,a), Closed(b) ->
      Open(va, ba, mk_rapply2 f a b)
  | Open(va,ba,a), Open(vb,bb,b) ->
      let vars = merge va vb in
      Open(vars, [],
        mk_apply2 f (select va ba a) (select vb bb b))

let unit_apply2_test f ta tb =
  match ta, tb with
    Closed(a), Closed(b) -> Closed (f true a b)
  | Closed(a), Open(vb,bb,b) ->
      Open(vb, bb, mk_lapply2_test f a b)
  | Open(va,ba,a), Closed(b) ->
      Open(va, ba, mk_rapply2_test f a b)
  | Open(va,ba,a), Open(vb,bb,b) ->
      let vars = merge va vb in
      Open(vars, [],
        mk_apply2_test f (select va ba a) (select vb bb b))

let unit_apply3 f t t' t'' = apply (unit_apply2 f t t') t''

let build_pair x y = unit_apply2 (fun x y -> x,y) x y

let build_list l =
  List.fold_right
    (fun x l -> unit_apply2 (fun x l -> x::l) x l)
    l
    (unit [])

(* this one is a bit tricky because of the imperative nature of arrays *)
let mk_array t v = Array.of_list (t v)
let build_array a =
  let rec fold_array fn a i a' =
    if i < Array.length a then
      fn a.(i) i (fold_array fn a (i+1) a')
    else
      a'
  in
  match
    fold_array
      (fun x _ a' -> unit_apply2 (fun x a' -> x::a') x a')
      a 0 (unit [])
  with
    Closed(t) -> Closed (Array.of_list t)
  | Open(vt,bt,t) ->
      Open(vt,bt,mk_array t)


module type Map =
  sig
    type 'a t
    val map : ('a -> 'b) -> 'a t -> 'b t
  end

module type S =
  sig
    type 'a t
    val fn : ('a pre_term -> 'b pre_term t) -> ('a,'b) binder pre_term t
    val fn_val : ('a pre_term -> 'a) -> ('a pre_term -> 'b pre_term t) ->
                     ('a,'b) binder pre_term t
  end

module Bind_struct(M: Map) =
  struct
    type 'a t = 'a M.t
    let fn fpt =
      let v = new_var () in
      M.map (bind_aux v) (fpt (mk_var v))

    let fn_val bv fpt =
      let v = new_var () in
      M.map (bind_aux v) (fpt (mk_var_val v bv))
  end

module type Map2 =
  sig
    type ('a, 'b) t
    val map : ('a -> 'b) -> ('c -> 'd) -> ('a, 'c) t -> ('b, 'd) t
  end

module type S2 =
  sig
    type ('a, 'b) t
    val fn : ('a pre_term -> ('b pre_term, 'c pre_term) t) ->
                   (('a,'b) binder pre_term, ('a,'c) binder pre_term) t
    val fn_val :
             ('a pre_term -> 'a) ->
                   ('a pre_term -> ('b pre_term, 'c pre_term) t) ->
                   (('a,'b) binder pre_term, ('a,'c) binder pre_term) t
  end

module Bind_struct2(M: Map2) =
  struct
    type ('a, 'b) t = ('a, 'b) M.t
    let fn fpt =
      let v = new_var () in
      M.map (bind_aux v) (bind_aux v) (fpt (mk_var v))

    let fn_val bv fpt =
      let v = new_var () in
      M.map (bind_aux v) (bind_aux v) (fpt (mk_var_val v bv))
  end


module Pair = struct
   type ('a, 'b) t = 'a * 'b
   let map f g (x, y) = (f x, g y)
end

module Bind_pair = Bind_struct2(Pair)

let bind_pair = Bind_pair.fn

let bind_pair_val  = Bind_pair.fn_val


module Map_list =
  struct
    type 'a t = 'a list
    let map = List.map
  end

module Bind_list = Bind_struct(Map_list)

let bind_list = Bind_list.fn
let bind_list_val = Bind_list.fn_val
