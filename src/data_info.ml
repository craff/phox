(* $State: Exp $ $Date: 2001/01/03 12:52:32 $ $Revision: 1.3 $ *)
(*######################################################*)
(*			data_info.ml			*)
(*######################################################*)

open Format
open Basic
open Data_base.Object
open Type.Base
open Type
open Print
open Lambda_util
open Typunif

let rec get_last = function
  [] -> max_level
| [Arg l] -> l
| _::l -> get_last l


let string_syntax = function
  Prefix (sy,_) -> "Prefix["^(level_to_string (get_last sy))^"]"
| Infix (ll,lr,sy,_,_,_) ->
            if level_leq lr ll then
              "lInfix["^(level_to_string (idelta' lr))^"]"
            else if level_leq lr (get_last sy) then
              "rInfix["^(level_to_string lr)^"]"
            else
              "Infix["^(level_to_string lr)^"]"
| _ -> ""

let get_prior o = match get_syntax o with
  Prefix (sy,_) -> get_last sy
| Infix (_,lr,_,_,_,_) -> lr
| _ -> max_level


let tab n s =
  let p = String.length s in
  if p >= n then print_string "  " else
    let rec fn = function
      0 -> ()
    | n -> print_char ' '; fn (n-1)
    in fn (n - p)

let print_sym (local,o) =
    open_hbox ();
    if local then print_string "(local) ";
    let s = get_name o in
    print_string s;
    tab 20 s;
    let s = string_syntax (get_syntax o) in
    print_string s;
    tab 20 s;
    reset_kind_var ();
    print_kind (get_kind o);
    close_box ();
    print_cut ()

let do_prior l =
  let filter o = match get_syntax o with
    Infix _ | Prefix _ -> true
  | _ -> false in
  let l = if l = [] then filter_base filter !the_base else l in
  let l = List.fold_left (fun l (_,o) -> if filter o then (true,o)::l else l)
                  (List.map (fun o -> false, o) l) !cur_local.caps_def in
  let l = List.sort (fun (_,o1) (_,o2) ->
    level_cmp (get_prior o1) (get_prior o2)) l in
  open_vbox 0; List.iter print_sym l; close_box ()

let contain s1 s2 =
  let n1 = String.length s1 and n2 = String.length s2 in
  let rec fn n =
    if n + n2 > n1 then false
    else if (String.sub s1 n n2) = s2 then true else fn (n+1)
  in fn 0

let hastype o k =
  (* let k = kind_copy k in *)
  let k' = get_safe_kind o in
  try
    unif k k'; true
  with Clash -> false

let not_hiden o = match get_syntax o with
  Hiden _ -> false
| _ -> let s = get_name o in
       if (String.length s) < 2 then true else
       if String.sub s 0 2 = "##" then false else true

let do_search s k =
  let filter o =
    contain (get_name o) s && hastype o k && not_hiden o in
  let l = filter_base filter !the_base in
  let l = List.fold_left (fun l (_,o) -> if filter o then (true,o)::l else l)
                  (List.map (fun o -> false, o) l) !cur_local.caps_def in
  if l = [] then
    print_endline "Search failed."
  else
    let l = List.sort (fun (_,o1) (_,o2) ->
       compare (get_name o1) (get_name o2)) l in
    open_vbox 0; List.iter print_sym l; close_box ()

let sp_describe e =
  match get_ext_tbl e with
    Equations tbl -> let tr = function Eq_theo o -> get_name o
                                 | _ -> failwith "bug in sp_describe" in
                    eqhash_it_table (fun all k l ->
                      List.flatten (List.map (fun (_,_,_,_,_,_,eqtl) ->
                           List.map (fun (eqt,_,_,_,_,_) ->
                             match k with Oneq o ->
                               tr eqt ^ " (" ^ get_name o ^")"
                             | _ ->  failwith "bug in sp_describe"
                      ) eqtl) l)@ all) [] tbl
  | Rules tbl -> symhash_it_table (fun all k l ->
                        (List.map (fun (_,(_,e,_,_,_,_,_)) ->
                               get_name e ^ " (" ^ get_name k ^")"
                        ) l) @ all) [] tbl
  | Trivial_Hacks tbl -> symhash_it_table (fun all k _ ->
                           get_name k::all) [] tbl
  | Tex_syntax tbl -> symhash_it_table (fun all k _ ->
                           get_name k::all) [] tbl

let show_special s = try
  let l = sp_describe (get_table s) in
  let l = List.sort compare l in
  List.iter print_endline l
  with Not_found -> raise (Gen_error ("Unknown table : \""^s^"\"."))
