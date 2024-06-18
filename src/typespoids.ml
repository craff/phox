(* Les types *)

type poidsclause = float

type indiceclause = float option



(* fonction d'ordre *)

let ordrepoids p1 p2 =
  compare p1 p2



(* Valeurs initiales *)

let taillecndats = ref 0

let pdsmax_global = ref 500. (* MODIFIABLE *)

let pdsmoy_global () = min 1. ( !pdsmax_global /. 5. )

let pds_min = 1

let lower_indice = None

let val_lower_indice = 1.

let val_default_indice = 1.3

let default_indice = Some val_default_indice

let pdsmax_cndats = ref 0.

(* Une fonction qui va servir *)

let listmax l =

  let rec f_aux l n =
    match l with
    | [] -> n
    | i::l -> if (compare i n)=1 then f_aux l i else f_aux l n
  in

  f_aux l 0



(* Deux fonctions de transition *)

let indice_of_int n =
  if
    n=0
  then
    None
  else
    Some ((float_of_int n)*.val_default_indice)

let int_of_indice ind =
  match ind with
  | None -> 0
  | Some n -> int_of_float n



(* initialise un poids en fonction d'un entier de départ *)

let initpoids n = match n with
| Some n -> let n = float_of_int (max pds_min n) in max n (pdsmoy_global ())
| None -> pdsmoy_global ()



(* calcule le poids d'une clause après résolution *)
(* plus l'unificateur est gros, plus c'est lourd *)
(* plus l est grand, moins c'est lourd *)
(* n est la taille de l'unificateur *)
(* ciw sont les poids des clauses parents *)
(* nci sont les cardinaux des clauses parents *)
(* l est la taille du littéral résolu *)
(* les indices sont ceux des clauses *)
(* les hist sont les historiques de la clause obtenue *)

let pds_res ~n ~indice1 ~rhist:_ ~chist ~c1w ~nc1 ~indice2 ~c2w ~nc2 ~l =

  if
    (nc1 = nc2 && nc1= 0)
  then
    0.
  else
(*    if
      n = 0
    then
      float_of_int ((min nc1 nc2) + 1)
    else *)
      let  n  =  float_of_int  n  in
      let nbre = float_of_int (listmax (List.map (fun (_,(ind,nb)) -> (int_of_indice ind)*nb) chist)) in

      let nc1 =  float_of_int nc1 in
      let nc2 =  float_of_int nc2 in

      let  l  =  float_of_int  l  in
      let n1 = match indice1 with None -> 0. | Some i -> i-.val_lower_indice in
      let n2 = match indice2 with None -> 0. | Some j -> j-.val_lower_indice in
      let nm = max n1 n2 in

  max 1. ((abs_float (
	   (c1w +. 1.)*. nc1
	     +. (c2w +. 1.)*. nc2
	     +. nm*.nbre
	     -. l))
	    +. n)

(*      ((min c1w c2w) +. 1.)
	+.
	(max
	   0.
	   ((nm *. nbre)
	      -. (l /. (nc1 +. nc2))
    	      +. n))
*)


(* Indice après résolution *)

let indice_res ~i1 ~i2 ~rhist ~chist =

  let n1 = (listmax (List.map (fun (_,(ind,nb)) -> (int_of_indice ind)*nb) chist)) in
  let n2 = (listmax (List.map (fun (_,(ind,nb)) -> (int_of_indice ind)*nb) rhist)) in
  let nm = float_of_int (max n1 n2) in
    match i1,i2 with
  | (None,None)     -> None
  | (Some i,None)   -> Some (i*.nm)
  | (None,Some j)   -> Some (j*.nm)
  | (Some i,Some j) -> Some ((max i j) *. nm)



(* Poids d'une clause après utilisation d'une règle *)
(* rindice est l'indice de la règle *)
(* rpds est le poids de la règle *)
(* indice est l'indice de la clause *)
(* pds est le poids de la clause *)
(* nbre est le nombre d'apparition *)
(* de la règle dans la clause *)

let pds_rule ~rindice ~rpds ~nbre ~indice:_ ~pds =
  let nbre = float_of_int nbre in
  let rpds = float_of_int rpds in
  let n = match rindice with None -> 0. | Some i -> (i-. val_lower_indice) in

(*   max val_lower_indice (pds +. n +. rpds +. (n**nbre)) *)
  max val_lower_indice ((pds +. n)*. rpds +. (n**nbre))



(* poids après contraction *)

let pds_cont ~wpere ~l:_ =
  wpere



(* Indice après décomposition *)

let indice_rule ~i ~hist =
  indice_of_int (max (int_of_indice i) (listmax (List.map (fun (_,(ind,nb)) -> (int_of_indice ind)*nb) hist)))



(* Fonctions d'affichage *)

let affpds w =
  Format.print_string " #" ;
  Format.print_float w


let affind i =
  match i with
  | None -> ()
  | Some i ->  Format.print_string " %" ; (Format.print_float i)
