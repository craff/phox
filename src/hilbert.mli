open Type

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

module Make : functor (H : Hilbert) -> Full_Hilbert with type t = H.t

module Merge :
  functor (Key : Key) ->
    sig
      val merge_map :
        ('a -> 'a -> 'a) ->
        (Key.t * 'a) list -> (Key.t * 'a) list -> (Key.t * 'a) list
      val merge_fold :
        'a ->
        ('a -> Key.t -> 'b -> 'b -> 'a) ->
        (Key.t * 'b) list -> (Key.t * 'b) list -> 'a
    end

module CartProd :
  functor (Key : Key) ->
    functor (H : Hilbert) -> Hilbert
      with type t = (Key.t * H.t) list

type 'a tree = T of ('a * (float * 'a tree)) list [@@unboxed]

module Tree :
  functor (Key : Key) -> Hilbert
    with type t = Key.t tree

type atom =
    AtomVar of int
  | AtomCst of int
  | AtomUVar
  | AtomAtom of af2_obj
  | AtomAbs
  | Root

module AKey : Key with type t = atom
module FKey : Key with type t = atom * int * int
module GKey : Key with type t = atom * int

module TermHilbert1 : Embed_Hilbert
  with type t = CartProd(AKey)(Tree(FKey)).t

module TermHilbert2 : Embed_Hilbert
  with type t = Tree(GKey).t

val distance : local_defs -> expr Basic.Map.t -> expr -> expr -> float
