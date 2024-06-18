
open Logic
open Typespoids
open Ptypes
open Splitting

module Affichage(Logic:Logic) = struct
  open Logic
  module Ty = Types(Logic)

  let print_clause c =

    let rec afflist l b =
      match l,b with
      | [],_       -> ()
      | f::[],true    -> print_formula f
      | f::[],false   -> print_formula (negate_formula f)
      | f::reste,true -> print_formula f; Format.print_string ", "; afflist reste b
      | f::reste,false-> print_formula (negate_formula f); Format.print_string ", "; afflist reste b
    in

    let rec affslist l b =
      match l,b with
      | [],_       -> ()
      | f::[],true    -> print_litname f
      | f::[],false   -> Format.print_string "~"; print_litname f
      | f::reste,true -> print_litname f; Format.print_string ", "; affslist reste b
      | f::reste,false-> Format.print_string "~"; print_litname f; Format.print_string ", "; affslist reste b
    in

    let lp = c.litx_pos in
    let ln = c.litx_neg in
    let lu = c.litx_ukn in
    let poids = c.poids in
    let indice = c.indice in

    let virg = ref false in

    Format.open_hbox ();

    (match lp with
    | [] -> ()
    | _ -> (virg:=true; afflist lp true));
    (match ln with
    | [] -> ()
    | _ -> (if !virg then Format.print_string ", " else virg:=true; afflist ln false));
    (match lu with
    | [] -> ()
    | _ -> (if !virg then Format.print_string ", " else virg:=true; afflist lu true));

    let lps,lns = c.litx_ps,c.litx_ns in
    (match lps with
    | [] -> ()
    | _ -> (if !virg then Format.print_string ", " else virg:=true; affslist lps false));
    (match lns with
    | [] -> ()
    | _ -> (if !virg then Format.print_string ", " else virg:=true; affslist lns true));
    Format.print_string " : ";
    affpds poids;
    affind indice;

    Format.close_box ()



(* Affichage d'une liste de clauses *)

  let print_clause_list lc =
    List.iter (fun c -> print_clause c ; Format.print_newline ()) lc

  let antsl = "\\"

(* Affichage de l'arbre de preuve *)

  let print_proof tree allclause =

    let rec make_proof_tree start =
      match start.vientde with
      | Donne -> Feuille(start)
      | Resol(n1,_,n2,_,l)
	->
	  (let start1 = Hashtbl.find allclause n1 in
	  let start2 = Hashtbl.find allclause n2 in
	  Nr(start,l,make_proof_tree start1,make_proof_tree start2))
      | Decomp(n,_,l,name)
	->
	  (let start1 = Hashtbl.find allclause n in
	  Nd(start,l,name,make_proof_tree start1))
      | Contrac(n,_,l)
	->
	  (let start1 = Hashtbl.find allclause n in
	  Nc(start,l,make_proof_tree start1))
      | Split(n,_,npaquet)
	->
	  (let start1 = Hashtbl.find allclause n in
	  Ns(start,npaquet,make_proof_tree start1))
    in

    let rec tree_printer string string_size tree =
      match tree with
      | Feuille(clause)
	->
	  (Format.print_string ((String.sub string 0 (string_size-1))^antsl);
	   Format.open_box 1;
	   print_clause clause;
           Format.close_box())
      | Nd(clause,l,name,t1)
	->
	  (Format.print_string ((String.sub string 0 (string_size-1))^antsl);
	   Format.open_box 1;
	   print_clause clause;
	   Format.print_string (" $dec "^name^" ");
	   print_formula l;
	   Format.close_box ();
           Format.print_newline ();
           tree_printer (string^" ") (string_size+1) t1)
      | Nr(clause,l,t1,t2)
	->
	  (Format.print_string ((String.sub string 0 (string_size-1))^antsl);
	   Format.open_box 1;
	   print_clause clause;
	   Format.print_string " $res ";
	   print_formula l;
           Format.close_box ();
           Format.print_newline ();
           tree_printer (string^"|") (string_size+1) t1;
           Format.print_newline ();
           tree_printer (string^" ") (string_size+1) t2)
      | Nrs(clause,litsplit,t1,t2)
	->
	  (Format.print_string ((String.sub string 0 (string_size-1))^antsl);
	   Format.open_box 1;
	   print_clause clause;
	   Format.print_string " $res ";
	   print_litname litsplit;
           Format.close_box ();
           Format.print_newline ();
           tree_printer (string^"|") (string_size+1) t1;
           Format.print_newline ();
           tree_printer (string^" ") (string_size+1) t2)
      | Nc(clause,l,t1)
	->
	  (Format.print_string ((String.sub string 0 (string_size-1))^antsl);
	   Format.open_box 1;
	   print_clause clause;
	   Format.print_string (" $contr ");
	   print_formula l;
	   Format.close_box ();
           Format.print_newline ();
           tree_printer (string^" ") (string_size+1) t1)
      | Ns(clause,npaquet,t1)
	->
	  (Format.print_string ((String.sub string 0 (string_size-1))^antsl);
	   Format.open_box 1;
	   print_clause clause;
	   Format.print_string (" $split "^(string_of_int npaquet)^" ");
	   Format.close_box ();
           Format.print_newline ();
           tree_printer (string^" ") (string_size+1) t1)
      | Mktree(clause)
	-> tree_printer string string_size (make_proof_tree clause)
      | Central(clause,litsplit,t1)
	->
	  (Format.print_string ((String.sub string 0 (string_size-1))^antsl);
	   Format.open_box 1;
	   print_clause clause;
	   Format.print_string " $center ";
	   print_litname litsplit;
           Format.close_box ();
           Format.print_newline ();
	   tree_printer (string^" ") (string_size+1) t1)

    in

    tree_printer " " 1 tree ; Format.print_newline ()

end
