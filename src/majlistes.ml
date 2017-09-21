(* gestion de la liste des candidats *)
(* c'est ici que se fait le test de tautologie *)
(* et une subsomption pour les candidates *)

open Typespoids
open Logic
open Ptypes

module Majlistes(Logic:Logic) = struct
  open Logic
  module Ty = Types(Logic)
  open Ty



(* teste si a est une tautologie *)
(* on ne regarde que les litéraux standards *)
(* car le prouveur test pour les lits de splitting *)

  let tauto c =

    let non_vide_inter_f l1 l2 =
      List.exists (fun g -> List.exists (fun f -> equal_formula f g) l1) l2
    in

    let lp = c.litx_pos in
    let ln = c.litx_neg in

    non_vide_inter_f lp ln



(* teste la subsomption *)
(* avec l'unification *)
(* if faut aussi regarder les littéraux de splitting *)

  let subsume c1 c2 =

    let varsc2 = List.fold_left
	(fun a b -> union_varset a (vars_of_formula b))
	empty_varset
	(c2.litx_ukn@(c2.litx_pos@c2.litx_neg)) in

    let subst = vars_to_constants varsc2 in

    let apply_subst_clause subst clause =

      let lp = List.map (fun f -> apply_subst subst f) clause.litx_pos in
      let ln = List.map (fun f -> apply_subst subst f) clause.litx_neg in
      let lu = List.map (fun f -> apply_subst subst f) clause.litx_ukn in
      {clause with
       litx_pos = lp;
       litx_neg = ln;
       litx_ukn = lu}
    in

    let c2=apply_subst_clause subst c2 in

    let list_iter_exists f list =
      let rec iterator f acc rest =
	match rest with
	| [] -> false
	| e::rest -> (f (acc@rest) e) || (iterator f (e::acc) rest) (* l'ordre n'est ici pas important *)
      in
      iterator f [] list
    in

    let rec test_sub c1 c2 = (* teste la subsomption pour les littéraux pos et neg *)
      match c1.litx_pos,c1.litx_neg with
      | [],[] -> true (* ceci est faux s'il y a des littéraux dans ukn *)
      | [],l1::ln ->
	  list_iter_exists
	    (fun others l2
	      ->
		try
		  (let _,subst,_,_,_,l = unif Subsume l1 l2 in
		  match l with
		  | []
		    ->
		      test_sub (apply_subst_clause subst {c1 with litx_neg = ln}) {c2 with litx_neg = others}
		  | _ -> false)
  with
  | Unif_fails -> false)
	    c2.litx_neg
      | l1::lp,_ ->
	  list_iter_exists
	    (fun others l2
	      ->
		try
		  (let _,subst,_,_,_,l = unif Subsume l1 l2 in
		  match l with
		  | []
		    ->
		      test_sub (apply_subst_clause subst {c1 with litx_pos = lp}) {c2 with litx_pos = others}
		  | _ -> false)
  with
  | Unif_fails -> false)
	    c2.litx_pos
    in

    let rec sub_slit l1 l2 = (* subsomption sur les littéraux de splitting *)
      match l1 with
      | [] -> true
      | f::l1
	->
	if
	  List.exists (fun g -> f = g) l2
	then
	  sub_slit l1 l2
	else
	  false
    in

    test_sub c1 c2 && (sub_slit c1.litx_ps c2.litx_ps) && (sub_slit c1.litx_ns c2.litx_ns)



(* Mise à jour de la liste cndats en fonction de la clause donnée *)

  let majcndats cdt cndts djvus =

    let b = ref true in

    let rec ajoute c liste nmax =

     (* nmax    : on a le droit d'ajouter nmax éléments a priori *)
     (* c,liste : on ajoute c à liste, si on a le droit *)
     (*         on trie la liste par poids croissants *)

      match (nmax,liste) with
      | (0,_) (* on n'a pas le droit : la liste doit être coupée *)
	->let _ = taillecndats:= (!maxcndts) in []
      | (_,[]) (* on a le droit d'ajouter à partir d'ici *)
	->
	  if
	    !b=true
	then (* on peut ajouter l'élément *)
	    let _ = taillecndats:= (!taillecndats +1) in
	    let _ = pdsmax_cndats:=c.poids in
	    [c]
	  else (* on n'a plus rien à ajouter *)
	    []
      | (n,a::reste)
	->
	  match (ordre a c) with
	  | neg when neg<0 (* la candidate est plus lourde *)
	    ->
	      if
		subsume c a
	      then (* on enlève a *)
		let _ = taillecndats:= (!taillecndats -1) in
		ajoute c reste n
	      else (* on garde a *)
		let _ = pdsmax_cndats:=a.poids in
		a::(ajoute c reste (n-1))
	  | 0 (* le poids est le même - est-ce important ici ? même chose pour l'instant *)
	    ->
	      if
		subsume c a
	      then (* on enlève a *)
		let _ = taillecndats:= (!taillecndats -1) in
		ajoute c reste n
	      else (* on garde a *)
		let _ = pdsmax_cndats:=a.poids in
		a::(ajoute c reste (n-1))
	  | pos when pos>0 (* la candidate est plus légère *)
	    ->
	      if
		!b=true
	      then (* on n'a pas encore ajouté la clause *)
		let _ = b:=false in (* on l'ajoute alors *)
		let _ = taillecndats:= (!taillecndats +1) in
		let _ = pdsmax_cndats:=c.poids in
		c::(ajoute c liste (n-1))
	      else (* on l'a ajouté *)
		if
		  subsume c a
		then
		  let _ = taillecndats:= (!taillecndats -1) in
		  ajoute c reste n
		else
		  let _ = pdsmax_cndats:=a.poids in
		  a::(ajoute c reste (n-1))
	  | _ -> assert false
    in

    let majaux cdt =
      match cdt with
      | c when List.exists (fun (cd,_) -> subsume cd c) djvus
            (* c ne doit pas être subsumée par une déjà vue *)
	->cndts
      | c when List.exists (fun cd -> subsume cd c) cndts
            (* idem pour les candidats *)
	->cndts
      | _
	->(ajoute cdt cndts !maxcndts)
    in

    b:=true; (* indique que l'on doit ajouter la clause *)
    if
      cdt.litx_neg=[] && cdt.litx_pos=[]
    then
      (empty_clause:=cdt.numero;
       if
	 cdt.litx_ns=[] && cdt.litx_ps=[]
       then
	 raise Proved
       else
	 raise EmptySplit);
    if
      not (tauto cdt)
    then
      if
	(ordrepoids cdt.poids !pdsmax_global)<=0 (* le poids ne doit pas être trop important *)
      then
	if
	  (compare !taillecndats !maxcndts)<0
	then  (* on n'a pas atteint la taille limite de cndats *)
	  majaux cdt
	else  (* on l'a atteint *)
	  if
	    (ordrepoids cdt.poids !pdsmax_cndats)<=0 (* il faut alors que le poids soit plus faible que le max *)
	  then
	    majaux cdt
	  else
	    cndts
      else
	cndts
    else
      cndts



(* gestion de la liste des djvues *)
(* le candidat est sensé ne pas être subsumé *)
(* mais il peut subsumer *)

  let rec majdjvues a l =

    match l with
    | []
      ->[]
    | (e,d)::reste
      ->
	if
	  subsume a e
	then
	  majdjvues a reste
	else
	  (e,d)::(majdjvues a reste)



(* enlève toutes les clauses subsumées *)
(* dans les deux listes par c, clause vide avec lit de split *)
(* renvoie donc les deux listes *)

  let add_empty_with_split c cndts djvus =

    let rec chcndts c liste =
      match liste with
      | [] -> []
      | a::liste
	->
	  if subsume c a
	  then
	    (taillecndats:=(!taillecndats-1);
	    chcndts c liste)
	  else
	    (pdsmax_cndats:=a.poids;
	    a::(chcndts c liste))
    in

    (chcndts c cndts),(majdjvues c djvus)


  (* mise à jour des clauses vides de splitting *)
  (* le candidat peut subsumer d'autres clauses *)
  (* et n'est pas subsumé *)

  let rec majesclauses a l =

      match l with
      | []
	->[]
      | e::reste
	->
	  if
	    subsume a e
	  then
	    majesclauses a reste
	  else
	    e::(majesclauses a reste)

end
