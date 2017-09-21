(* $State: Exp $ $Date: 2004/05/24 08:23:24 $ $Revision: 1.5 $ *)
(*######################################################*)
(*			poids.ml        		*)
(*######################################################*)

open Flags

let initweight = 0.

let greatest_weight = ref initweight

let max_weight () = float_of_int !cndats_max_weight

let more_than_max_weight w = w > (max_weight ())

let inferior_to_greatest_weight w = w <= !greatest_weight

let updt_greatest_weight w = greatest_weight:=w

let order_weight w1 w2 =
  let o =
    if
      w1 < w2
    then 
      -1
    else
      if
	w1 > w2
      then
	1
      else
	0
  in
  o
    
let weight_merge pds1 pds2 l = 0.
