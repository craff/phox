(* résolution avec les clauses de littéraux de splitting *)
(* On lance une OL-déduction *)
(* toutes les clauses sont telles que *)
(* litx_* est vide sauf pour les lit de splitting *)


open Typespoids
open Logic
open Ptypes
open Splitting

module Oldeduction(Logic:Logic) = struct
  open Logic
  module Ty = Types(Logic)
  open Ty

  exception Prooftree of ((litteral,contrainte) clause, litteral) tree


  type 'a info = Quadr of 'a | Simpl of 'a



  type lit = { nom : litname ; pol : bool }



  type oclause = { elts : (lit info) list ; num : int }



  let to_oclause c =
    {
     elts =
     (List.map (fun n -> Simpl { nom = n ; pol = true} ) c.litx_ps)
     @
       (List.map (fun n -> Simpl {nom = n ; pol = false} ) c.litx_ns) ;
     num = c.numero
   }


  let clausevide =
    { litx_pos   = []                         ;
      litx_neg   = []                         ;
      litx_ukn   = []                         ;
      litx_ps    = []                         ;
      litx_ns    = []                         ;
      poids      = initpoids (Some 0)         ;
      vientde    = Donne                      ;
      numero     = -1                         ;
      contr      = ref (empty_constraints ()) ;
      indice     = default_indice             ;
      histclist  = []                         ;
      histrlist  = []                         ;
    }

  let to_clause oc =

    let rec pos_negs list acpos acneg =
      match list with
      | [] -> List.rev acpos, List.rev acneg
      | e::list
	->
	  (match e with
	  | Quadr _ -> pos_negs list acpos acneg
	  | Simpl e
	    ->
	      if
		e.pol
	      then
		pos_negs list (e.nom::acpos) acneg
	      else
		pos_negs list acpos (e.nom::acneg))
    in

    let pos,neg = pos_negs oc.elts [] [] in

    { clausevide with
      litx_ps    = pos                        ;
      litx_ns    = neg                        ;
    }


  (* liste d'ensemble de littéraux non encadrés des clauses déjà vues *)
  let alloclauses = ref []

  let rec makelist list =
    match list with
    | [] -> []
    | (Quadr _)::list -> makelist list
    | (Simpl lit)::list -> lit::(makelist list)



  let eliminate oc = (* ne conserve pas l'ordre *)
    let list = makelist oc.elts in

    let rec elim l acc =
      match l with
      | [] -> acc
      | e::l -> if list = e then acc@l else elim l (e::acc)
    in

    alloclauses:=elim !alloclauses []



  let is_redundant_or_change oc =

    let list = (makelist oc.elts) in

    let rec cont l1 l2 = (* l1 contient l2, listes ordonnées *)
      match l1,l2 with
      | _,[] -> true
      | [],_ -> false
      | e1::l1p,e2::l2p
	->
	  (match compare e1 e2 with
	  | -1 -> cont l1p l2
	  | 0  -> cont l1p l2p
	  | _  -> cont l1p l2)
    in

    let tauto l1 =
      let rec posneg l p n =
	match l with
	| [] -> p,n
	| e::l -> if e.pol then posneg l ((e.nom)::p) n else posneg l p ((e.nom)::n)
      in

      let test l1 l2 =
	List.exists (fun e1 -> List.exists (fun e2 -> e1=e2) l2) l1
      in

      let pos,neg = posneg l1 [] [] in

      test pos neg
    in

    if
      tauto list || List.exists (cont list) !alloclauses
    then
      true
    else
      (alloclauses:=list::(!alloclauses);
       false)


  let proof_search sat_set c =

    let sat_oset = List.map to_oclause sat_set in
    let oc = to_oclause c in

    let real_clause oc = let n = oc.num in List.find (fun c -> c.numero = n) sat_set in

    let find_and_give l name bool =

      let rec aux l acc name bool =
	match l with
	| [] -> raise Not_found
	| e::l
	  ->
	    (match e with
	    | Quadr _ -> aux l (e::acc) name bool
	    | Simpl lit
	      ->
		if
		  (lit.nom = name && lit.pol = bool)
		then
		  (List.rev_append acc l)
		else
		  aux l (e::acc) name bool)
      in

      aux l [] name bool
    in

    let simplify oc =

      let rec simpl_quadr oc =
	match oc.elts with
	| [] -> failwith "proved"
	| e::relts ->
	    (match e with
	    | Quadr _ -> simpl_quadr { oc with elts = relts }
	    | _ -> oc)
      in

      let simpl_unique oc =

	let rec simpl_unique_set set =
	  match set with
	  | [] -> []
	  | e::set ->
	      if
		List.mem e set
	      then
		simpl_unique_set set
	      else e::(simpl_unique_set set)
	in

	{ oc with elts = simpl_unique_set oc.elts }
      in

      simpl_quadr (simpl_unique oc)
    in

    let test_central oc =
      let name,bool,tl = match oc.elts with | (Simpl hd)::tl -> hd.nom,(not hd.pol),tl | _ -> assert false in
      List.exists
	(fun e ->
	  match e with
	  | Quadr li
	    ->
	      if
		(li.nom = name && li.pol = bool)
	      then
		true
	      else
		false
	  | _ -> false)
	tl
    in

    let rec search_tree (oc,tree) =

      if
	test_central oc
      then
	let name = match (List.hd oc.elts) with | Simpl e -> e.nom | _ -> assert false in
	try
	  let newoc = simplify {elts = List.tl oc.elts ; num = -1} in
	  if
	    is_redundant_or_change newoc
	  then
	    []
	  else
	    let newc = to_clause newoc in
	    [(newoc,Central(newc,name,tree))]
        with
        | Proved -> raise (Prooftree (Central(clausevide,name,tree)))
      else
	(let list = ref [] in
	let name,bool,tl = match oc.elts with | (Simpl e)::tl -> e.nom,(not e.pol),tl | _ -> assert false in
	List.iter
	  (fun coc ->
	    (try
	      let rest = find_and_give coc.elts name bool in
	      (try
		let newoc =
		  simplify
		    { elts = rest@((Quadr { nom = name ; pol = not bool})::tl) ;
		      num = -1
		  } in
		if
		  is_redundant_or_change newoc
		then
		  ()
		else
		  let newc = to_clause newoc in
		  list:=
		    (newoc,Nrs(newc,name,Mktree(real_clause coc),tree))
		    ::
		      (!list)
	      with
	      | Proved -> raise (Prooftree (Nrs(clausevide,name,Mktree(real_clause coc),tree))))
	    with
	    | Not_found -> ())
	  )
	  sat_oset;
	!list)

    and search linear_tree_list acc =
      try
	(match linear_tree_list with
	| [] -> (match acc with | [] -> raise Noprinting | _ -> search acc [])
	| ((oc,tree) as e)::l
	  ->
	    if
	      oc.elts=[]
	    then
	      tree
	    else
	      (eliminate oc;
	      search l ((search_tree e)@acc)))
      with
      | Prooftree(tree) -> tree
    in

    match c.litx_ps,c.litx_ns with
    | [],[] -> Mktree(c)
    | _,_ ->
	alloclauses:=[];
	search [(oc,Mktree(c))] []

end
