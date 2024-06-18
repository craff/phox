open Data_base
open Object
open Type
open Lambda_util
open Af2_basic

module type Key =
  sig
    type t
    val compare : t -> t -> int
    val coef : t -> float
  end

module type Hilbert =
  sig
    type t
    val zero : t
    val (++) : t -> t -> t
    val (--) : t -> t -> t
    val upper : t -> t -> t
    val (@@) : float -> t -> t
    val scalar_product : t -> t -> float
  end

module type Full_Hilbert =
  sig
    include Hilbert
    val norm2 : t -> float
    val norm : t -> float
    val distance2 : t -> t -> float
    val distance : t -> t -> float
    val angle : t -> t -> t -> float
  end

module type Embed_Hilbert =
  sig
    include Full_Hilbert
    val term_to_vector : expr -> t
  end

module Make (H:Hilbert) =
  struct
    include H
    let norm2 x = scalar_product x x
    let norm x = sqrt (norm2 x)
    let distance2 x y = norm2 (x -- y)
    let distance x y = norm (x -- y)
    let angle e f g =
      let x = f -- e and y = g -- e in
      let a = scalar_product x y /. (norm x *. norm y) in
      let a = if a > 1.0 then 1.0 else if a < -1.0 then -1.0 else a in
      acos a
  end

module Merge (Key : Key) =
  struct
    open Key

    let rec merge_map f l l' = match l, l' with
	[], l -> l
      | l, [] -> l
      | ((k,x as c)::l0), ((k',x' as c')::l0') ->
	  match compare k k' with
	    0 -> (k, f x x')::merge_map f l0 l0'
	  | x when x < 0 -> c::merge_map f l0 l'
	  | _ -> c'::merge_map f l l0'

    let rec merge_fold a f l l' = match l, l' with
	[], _ | _, [] -> a
      | ((k,x)::l0), ((k',x')::l0') ->
	  match compare k k' with
	    0 -> f (merge_fold a f l0 l0') k x x'
	  | x when x < 0 -> merge_fold a f l0 l'
	  | _ -> merge_fold a f l l0'

  end

module CartProd (Key : Key) (H:Hilbert) =
  struct
    type t = (Key.t * H.t) list
    module M = Merge(Key)
    open M
    let zero = []
    let (++) = merge_map H.(++)
    let upper = merge_map H.upper
    let (--) = merge_map H.(--)
    let (@@) a = List.map (fun (k,x) -> k, H.(@@) a x)
    let scalar_product =
      merge_fold 0.0 (fun a k x x' ->
	a +. Key.coef k *. H.scalar_product x x')
  end

type 'a tree = T of ('a * (float * 'a tree)) list [@@unboxed]

module Tree (Key : Key) =
  struct
    type t = Key.t tree
    module M = Merge(Key)
    open M
    let zero = T []
    let rec (++) (T t) (T t') =
      T (merge_map (fun (x,t) (x',t') -> (x +. x', t ++ t')) t t')
    let rec upper (T t) (T t') =
      T (merge_map (fun (x,t) (x',t') -> (max x x', upper t t')) t t')
    let rec (--) (T t) (T t') =
      T (merge_map (fun (x,t) (x',t') -> (x -. x', t -- t')) t t')
    let rec (@@) a (T t) =
      T (List.map (fun (k,(x,t)) -> (k, (a *. x, a @@ t))) t)
    let rec scalar_product (T t) (T t') =
      merge_fold 0.0
	(fun a k (x,t) (x',t') ->
	  a +. x*.x' +. Key.coef k *. scalar_product t t')
	t t'
  end

type atom =
    AtomVar of int
  | AtomCst of int
  | AtomUVar
  | AtomAtom of af2_obj
  | AtomAbs
  | Root

let compare_atom a a' = match a, a' with
  | Root, Root -> 0
  | Root, _ -> -1
  |_, Root -> 1
  | AtomVar n, AtomVar n' -> n - n'
  | AtomVar _, _ -> -1
  |_, AtomVar _ -> 1
  | AtomCst n, AtomCst n' -> n - n'
  | AtomCst _, _ -> -1
  |_, AtomCst _ -> 1
  | AtomUVar, AtomUVar -> 0
  | AtomUVar, _ -> -1
  |_, AtomUVar -> 1
  | AtomAbs, AtomAbs -> 0
  | AtomAbs, _ -> -1
  |_, AtomAbs -> 1
  | AtomAtom o, AtomAtom o' -> get_key o - get_key o'

module AKey =
  struct
    type  t = atom
    let compare = compare_atom
    let coef _ = 1.0
  end

module FKey =
  struct
    type  t = atom * int * int
    let compare (o,_,p) (o',_,p') =
      match compare_atom o o', p - p' with
	0, d |
        d, _ -> d
    let coef (_,a,_) = 1.0 /. float_of_int a
  end

module TermHilbert1 = struct
  module TermHilbert =
    Make(CartProd(AKey)(Tree(FKey)))

  include TermHilbert

  let term_to_vector' f t =
    let rec fn a path = function
	EVar n -> f a [AtomVar n, path]
      | EAtom(o,_) -> f a [AtomAtom o, path]
      | UCst(n,_) -> f a [AtomCst n, path]
      | UVar _ -> f a [AtomUVar, path]
      | EAbs(_,e,_) -> fn a (T [(AtomAbs,1,0),(1.0,path)]) e
      | EApp _ as e ->
	  let rec gn nb args = function
	      EApp(t,u) -> gn (nb+1) ((nb,u)::args) t
	    | t ->
		let hn = function
		    EVar n -> AtomVar n
		  | EAtom(o,_) -> AtomAtom o
		  | UCst(n,_) -> AtomCst n
		  | UVar _ -> AtomUVar
		  | _ -> assert false
		in
		let k = hn t in
		List.fold_left
		  (fun a (p, u) -> fn a (T[(k,nb,p),(1.0,path)]) u)
		  a args
	  in gn 0 [] e
      | FVar _ | Path _ | Syntax _ | EData _ -> assert false
    in fn zero (T[(Root,1,0),(1.0,T[])]) t

  let term_to_vector = term_to_vector' upper

end

module GKey =
  struct
    type  t = atom * int
    let compare (o,p) (o',p') =
      match compare_atom o o', p - p' with
	0, d |
        d, _ -> d
    let coef _ = 1.0
  end

module TermHilbert2 = struct

  module TermHilbert =
    Make(Tree(GKey))

  include TermHilbert

  let term_to_vector t =
    let rec fn = function
	EVar n -> T[(AtomVar n,0), (1.0,T[])]
      | EAtom(o,_) -> T[(AtomAtom o,0), (1.0,T[])]
      | UCst(n,_) -> T[(AtomCst n,0), (1.0,T[])]
      | UVar _ -> T[(AtomUVar,0), (1.0,T[])]
      | EAbs(_,e,_) -> T[(AtomAbs,0),(1.0,fn e)]
      | EApp _ as e ->
	  let rec gn nb args = function
	      EApp(t,u) -> gn (nb+1) ((nb,u)::args) t
	    | t ->
		let hn = function
		    EVar n -> AtomVar n
		  | EAtom(o,_) -> AtomAtom o
		  | UCst(n,_) -> AtomCst n
		  | UVar _ -> AtomUVar
		  | _ -> assert false
		in
		let k = hn t in
		T(List.rev_map
		  (fun (p, u) -> (k,p),(1.0,fn u)) args)
	  in gn 0 [] e
      | FVar _ | Path _ | Syntax _ | EData _ -> assert false
    in T[(Root,0),(1.0, fn t)]

end

let distance match_local result e1 e2 =
  let opend oe =
    if (List.memq oe match_local.local_close_tbl) then false else
      try
	let _ = symhash_find tbl_close_def oe in
	false
      with Not_found -> not (Base.is_recursive oe)
  in
  let openc n =
      try
        Some (fst (List.assoc n match_local.cst_eq))
      with Not_found -> None
  in
  let e1 = norm_ldexpr result opend openc e1 in
  let e2 = norm_ldexpr result opend openc e2 in
  let d1 =
    TermHilbert1.distance (TermHilbert1.term_to_vector e1) (TermHilbert1.term_to_vector e2)
  in
  let d2 =
    TermHilbert2.distance (TermHilbert2.term_to_vector e1) (TermHilbert2.term_to_vector e2)
  in
  sqrt (d1 *. d2)
