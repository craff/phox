(* $State: Exp $ $Date: 2006/02/24 17:01:52 $ $Revision: 1.8 $ *)
(*######################################################*)
(*			basic.ml			*)
(*######################################################*)

open List
open Format

let print_endline str =
  open_hbox (); print_string str; print_newline ()

module Int_ord = struct
  type t = int
  let compare = (-)
end
module Map = Map.Make(Int_ord)
module Set = Set.Make(Int_ord)


(*
  Quelsques fonctions d'interet general
*)

(* ce fichier n'a pas d'interface ! *)

let union l l0 =
  let rec f = function
    [] -> l
  | a::l0 -> if mem a l then f l0 else a::f l0
  in f l0

let inter l l0 =
  let rec f = function
    [] -> []
  | a::l0 -> if mem a l then a::f l0 else f l0
  in f l0

let subtract l0 l =
  let rec f =  function
    [] -> []
  | a::l0 -> if mem a l then f l0 else a::(f l0)
  in f l0

(* operation ensembliste "physique" sur les listes *)

let unionq l l0 =
  let rec f = function
    [] -> l
  | a::l0 -> if memq a l then f l0 else a::f l0
  in f l0

let interq l l0 =
  let rec f = function
    [] -> []
  | a::l0 -> if memq a l then a::f l0 else f l0
  in f l0

let subtractq l0 l =
  let rec f =  function
    [] -> []
  | a::l0 -> if memq a l then f l0 else a::(f l0)
  in f l0

(* operation ensembliste sur les listes d'assotiations *)

let uniona l l0 =
  let rec f = function
    [] -> l
  | (a,_) as c::l0 -> if List.mem_assoc a l then raise (Invalid_argument "uniona")
                      else c::(f l0)
  in f l0

let subtracta l0 l =
  let rec f =  function
    [] -> []
  | (a,_) as c::l0 -> if List.mem_assoc a l then f l0 else c::(f l0)
  in f l0

let rma l0 b =
  let rec f =  function
    [] -> []
  | (a,_) as c::l0 -> if a = b then l0 else c::(f l0)
  in f l0

let best f l =
  match l with
    [] -> raise (Invalid_argument "best")
  | x::l ->
      let rec fn b s acc  = function
        [] -> b, acc
      | x::l ->
          let s' = f x in
          if s' > s then fn x s' (b::acc) l
                    else fn b s  (x::acc) l
      in fn x (f x) [] l

(* nth n [a0;...;ap] = an, raise Invalid_argument "nth" si n > p ou n < 0 *)

let rec nth_try n l = match (n,l) with
  0, (x::_) -> x
| n, (_::l) -> nth_try (n - 1) l
| _, [] -> raise Not_found

(* cons_fst a (l,x) = (a::l),x *)

let cons_fst a (l,x,y) = (a::l),x,y

let cons_nonempty l l' = if l = [] then l' else l::l'

(* select f l returns the list of all element x in l such that f x = true *)

let select f l =
  let rec fn = function
    [] -> []
  | a::l -> if f a then a::(fn l) else fn l
  in fn l

(* generation de nom de variable a partir d'un entier *)

let int_to_alpha b i =
  let c = if b then 65 else 97 in
  let rec f_aux i =
    if i < 26
    then String.make 1 (Char.chr (i+c))
    else (f_aux (i/26) ^ String.make 1 (Char.chr ((i mod 26)+c+1)))
  in f_aux i

(* quelques variations sur la fonction List.assoc *)

let cossa a l0 =
  let rec f = function
    [] -> raise Not_found
  | (b,c)::l -> if a = c then b else f l
  in f l0

let cossaf a l0 =
  let rec f = function
    [] -> raise Not_found
  | (b,(c,_))::l -> if a = c then b else f l
  in f l0

let cossas a l0 =
  let rec f = function
    [] -> raise Not_found
  | (_,(c,b))::l -> if a = c then b else f l
  in f l0

let assoc3 a0 l0 =
  let rec f = function
    [] -> raise Not_found
  | (a,b,c)::l -> if a = a0 then b,c else f l
  in f l0

(* dernier element d'une liste,
      raise Invalid_argument "last" si la liste est vide *)

let rec last = function
  [] -> raise (Invalid_argument "last")
| [a] -> a
| _::l -> last l

(* cons a l'envers (snoc) *)

let snoc a l0 =
  let rec f = function
    [] -> [a]
  | b::l -> b::(f l)
  in f l0

(* rotate [a0;a1;...;an] = [a1;...;an;a0] *)

let rec rev_append l l' =
  match l with
    [] -> l'
  | x::l -> rev_append l (x::l')

let insert n l = match l with
  [] -> []
| x::l ->
  let rec fn n acc l = match n,l with
    0, l -> rev_append acc (x::l)
  | n, (y::l) -> fn (n-1) (y::acc) l
  | _ -> raise (Invalid_argument "insert")
  in fn n [] l

let extract n l =
  let rec fn n acc l = match n,l with
    0, x::l -> x::rev_append acc l
  | n, (y::l) -> fn (n-1) (y::acc) l
  | _ -> raise (Invalid_argument "extract")
  in fn n [] l

let last_in_list n l =
  let rec fn n l = match n,l with
    0, l -> l
  | n, _::l -> fn (n-1) l
  |  _ -> raise (Invalid_argument "last_in_list")
  in
  let p = List.length l in
  if p < n then raise (Invalid_argument "last_in_list");
  fn (p - n) l

let rotate = function
    [] as l -> l
  | [_] as l -> l
  | a::l -> snoc a l

let rec liat = function
    [] | [_] -> []
  | a::l -> a::liat l

(* list_do f [a0;a1;...;an] = f an; ...; f a1; () *)

let list_do f l0 =
  let rec g = function
    [] -> ()
  | a::l -> g l; f a
  in g l0

let rec forall2 f l1 l2 =
  match l1, l2 with
    [], [] -> true
  | (x1::l1), (x2::l2) -> f x1 x2 && forall2 f l1 l2
  | _ -> raise (Invalid_argument "forall2")

let list_count f l =
  let rec fn i l = match l with
      (x::l) -> f i x; fn (i+1) l
    | [] -> ()
  in fn 1 l

let list_bcount f l =
  let rec fn i l = match l with
      (x::l) -> fn (i+1) l; f i x
    | [] -> ()
  in fn 1 l

let cons_option a b = match a with
    None -> b
  | Some x -> x::b

let flat_select_map gn nl l =
  let rec fn d nl l = match nl, l with
    n::nl, x::l when n = d ->
      let r = fn (d+1) nl l in
      List.map (fun x -> (true, x)) (gn (n-1) x)@r
  | [0], x::l ->
      let r = fn (d+1) nl l in
      List.map (fun x -> (true, x)) (gn 0 x)@r
  | nl, x::l ->
      (false, x)::fn (d+1) nl l
  | ([] | [0]), [] -> []
  | _ -> raise Not_found
  in
  fn 1 nl l
