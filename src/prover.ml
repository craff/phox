open Logic
open Typespoids
open Ptypes
open Splitting

module Prover(Logic:Logic) = struct
  open Logic
  module Ty = Types(Logic)
  open Ty
  module Af = Affichage.Affichage(Logic)
  open Af
  module Maj = Majlistes.Majlistes(Logic)
  open Maj
  module Oldd = Oldeduction.Oldeduction(Logic)
  open Oldd


(* Avoir deux poids ? Un structurel, et un de 'hint' ? *)
(* peut aider pour la subsomption ?? *)

  exception Build_fails



(* clause de base vide *)

  let initclause =
    { litx_pos   = []                         ;
      litx_neg   = []                         ;
      litx_ukn   = []                         ;
      litx_ps    = []                         ;
      litx_ns    = []                         ;
      poids      = initpoids (Some 0)         ;
      vientde    = Donne                      ;
      numero     = 0                          ;
      contr      = ref (empty_constraints ()) ;
      indice     = default_indice             ;
      histclist  = []                         ;
      histrlist  = []                         ;
    }



(* crée un nouveau numéro de clause *)

  let new_num_clause =
    let c = ref 0 in
    (fun () -> let n = !c+1 in  c:=n; n)



(* méthode utilisée *)
(* par défaut aucune "n" pour none *)
(* hyper-res neg : "nhr" *)
(* hyper-res pos : "phr" *)

  let met = ref "n"



(* enlève un élément à une liste et donne cet élément en même temps *)

  let list_delete_nth l n =

    let rec aux l acc n =
      match l,n with
      | e::l,0
	->
	  (List.rev_append acc l),e
      | e::l,_
	->
	  aux l (e::acc) (n-1)
      | _
	->raise (Failure "list_delete")
    in

    aux l [] n

(* Comparaison de formules *)

  let compare_formula f1 f2 =
    if equal_formula f1 f2 then 0 else compare f1 f2



(* trie une liste en otant les doubles et en utilisant une fonction de comparaison *)
(* A priori non utilisée *)

(*
  let setifie cmp l =

    let rec canonical lis =
      match lis with
	x::(y::_ as rest) -> cmp x y < 0 & canonical rest
      | _ -> true
    in

    let rec unique l =
      match l with
	(x::(y::_ as ys)) -> if cmp x y = 0 then unique ys else x::(unique ys)
      | _ -> l

    in

    if canonical l then l else unique (List.sort cmp l)
*)



(* fonction de merge qui évite de créer des paires *)
(* en mergeant deux listes triées sans paires *)
(* sans unification *)

  let rec merge_perso cmp l1 l2 =

    match l1, l2 with
    | [], l2 -> l2
    | l1, [] -> l1
    | h1 :: t1, h2 :: t2 ->
	(match cmp h1 h2 with
	| -1 -> h1 :: merge_perso cmp t1 l2
	| 1  -> h2 :: merge_perso cmp l1 t2
	| _  -> h1 :: merge_perso cmp t1 t2)



(* élimine une formule d'une liste triée *)

  let rec except l liste =
    match liste with
    | [] -> []
    | e::listep
      ->
        (match compare_formula e l with
        | -1 -> e:: except l listep (* e<l *)
        | 0 -> listep (* e=l *)
        | _ -> liste) (* e>l *)


(* ajoute des informations d'historique lors d'une règle *)
(* la liste est triée par ordre décroissant *)

  let rec add_hist_r hr name =
    match hr with
    | [] -> [(name,(indice_of_int (indice_regle name),1))]
    | (s,(i,n))::hr ->
	(match compare s name with
	| 0 -> (name,(i,n+1))::hr
	| 1 -> (s,(i,n))::(add_hist_r hr name)
	| _ -> (name,(i,1))::hr)

  let rec add_hist_c hr c =
    match hr with
    | [] -> [(c.numero,(c.indice,1))]
    | (nc,(i,n))::hr ->
	(match compare nc c.numero with
	| 0 -> (nc,(i,n+1))::hr
	| 1 -> (nc,(i,n))::(add_hist_c hr c)
	| _ -> (c.numero,(i,1))::hr)



(* merge des informations d'historique lors d'une résolution *)
(* les listes sont triées par ordre décroissant *)

  let rec merge_hist h1 h2 =
    match h1,h2 with
    | [],[] -> []
    | [],h2 -> h2
    | h1,[] -> h1
    | (nc1,(i1,n1))::h1p,(nc2,(i2,n2))::h2p
      ->
	(match compare nc1 nc2 with
	| 1 -> (nc1,(i1,n1))::(merge_hist h1p h2)
	| 0 -> (nc1,(i1,n1+n2))::(merge_hist h1p h2p)
	| _ -> (nc2,(i2,n2))::(merge_hist h1 h2p))



(* Transforme une liste de formules en deux listes *)
(* Sans négation, liste des positives et liste des négatives *)
(* et triées *)


  let pos_neg_list liste =

    let rec p_n_l liste lp ln lu =
      match liste with
      | [] -> (lp,ln,lu)
      | f::liste
	->
	  try
	    if
	      negative_formula f
	    then
	      p_n_l liste lp (merge_perso compare_formula [elim_all_neg f] ln) lu
	    else
	      p_n_l liste (merge_perso compare_formula [elim_all_neg f] lp) ln lu
	  with
	    Metavar -> p_n_l liste lp ln (merge_perso compare_formula [f] lu)
    in

    p_n_l liste [] [] []



(* applique une substitution à une clause *)
(* on ne sait pas si la substitution conserve l'ordre *)

  let apply_subst_clause subst clause =

    let lp = List.map (fun f -> apply_subst subst f) clause.litx_pos in
    let ln = List.map (fun f -> apply_subst subst f) clause.litx_neg in
    let lu = List.map (fun f -> apply_subst subst f) clause.litx_ukn in
    let lpp,lnp,lu = pos_neg_list lu in
    {clause with
     litx_pos = merge_perso compare_formula lpp lp;
     litx_neg = merge_perso compare_formula lnp ln;
     litx_ukn = lu}



(* donne une liste de renommage à partir d'une clause *)
(* C'est à dire donne un renommage pour les variables libres de l'autre clause *)

  let get_renaming_clause rename clause =

    let get_renaming_formula_list rena flist =
      let ren = ref rena in
      List.iter (fun f -> ren:= get_renaming_formula (!ren) f) flist;
      !ren
    in

    let rename = get_renaming_formula_list rename clause.litx_neg in
    let rename = get_renaming_formula_list rename clause.litx_pos in
    let rename = get_renaming_formula_list rename clause.litx_ukn in
    let rename = get_renaming_constraints rename !(clause.contr) in
    rename



(* donne de nouveaux noms aux variables libres de l'autre clause *)
(* se fait avant toute unification, ie toute résolution *)
(* on ne sait pas si un renommage conserve l'ordre *)

  let rename_clause rename clause =

    {clause with
     litx_neg = List.map (fun f -> rename_formula rename f) clause.litx_neg ;
     litx_pos = List.map (fun f -> rename_formula rename f) clause.litx_pos ;
     litx_ukn = List.map (fun f -> rename_formula rename f) clause.litx_ukn ;
     contr = ref (rename_constraints rename !(clause.contr)) }



(* crée la liste des clauses hypothèses *)
(* inutile de renomer les variables *)
(* met à jour la valeur de maxpds_cndats *)

  let rec add_hyplist_to_cndats hyps =
    match hyps
    with
    | [] -> ()
    | (e,n,c,i)::hyps
      ->
	try
	  let b = negative_formula e in
	  let e = elim_all_neg e in
	  if
	    b
	  then
	    if
	      is_true e
	    then
	      raise Proved (* cela signifie que la formule est Faux donc on a la clause vide *)
	    else
	      (let pds = initpoids n in
	      let cdt = {initclause
				with
				 litx_neg = [e] ;
				 numero = new_num_clause () ;
				 poids = pds ; contr = ref c ;
				 indice = indice_of_int i;
			       } in
	      if
		!trace_proof || !splitting
	      then
		Hashtbl.add allclauses cdt.numero cdt;
	      cndats:=majcndats cdt !cndats !djvues;
	      pdsmax_cndats := max !pdsmax_cndats pds;
	      add_hyplist_to_cndats hyps)
	  else
	    if
	      is_true e
	    then
	      add_hyplist_to_cndats hyps (* cela signifie que la formule est Vrai donc pas de nouvelle clause *)
	    else
	      (let pds = initpoids n in
	      let cdt = {initclause
				with
				 litx_pos = [e] ;
				 numero = new_num_clause () ;
				 poids = pds ; contr = ref c ;
				 indice = indice_of_int i; } in
		if
		  !trace_proof || !splitting
		then
		  Hashtbl.add allclauses cdt.numero cdt;
		cndats:=majcndats cdt !cndats !djvues;
              pdsmax_cndats := max !pdsmax_cndats pds;
	      add_hyplist_to_cndats hyps)
  with
  | Metavar ->
      (let pds = initpoids n in
      let cdt = {initclause
			with
			 litx_ukn = [e] ;
			 numero = new_num_clause () ;
			 poids = pds ;
			 contr = ref c; } in
	if
	  !trace_proof || !splitting
	then
	  Hashtbl.add allclauses cdt.numero cdt;
	cndats:=majcndats cdt !cndats !djvues;
      pdsmax_cndats := max !pdsmax_cndats pds;
      add_hyplist_to_cndats hyps)



(* crée la clause pour le but *)
(* On doit mettre une négation devant le but *)
(* pour faire la clause *)

  let add_goal_to_cndats goal =
    try
      let b = negative_formula goal in
      let goal = elim_all_neg goal in
      if
	not b (* le but est-il positif ? *)
      then
	if
	  is_true goal
	then
	  raise Proved (* cela signifie que le but est Vrai donc on a la clause vide *)
	else
	  (let cdt = {initclause
			    with
			     litx_neg = [goal] ;
			     numero = new_num_clause ();
			   } in
	  if
	    !trace_proof || !splitting
	  then
	    Hashtbl.add allclauses cdt.numero cdt;
	  cndats:=majcndats cdt !cndats !djvues)
      else
	if
	  is_true goal
	then
	  () (* cela signifie que le but est Faux, donc on est en train de faire une preuve par l'absurde *)
	else
	  (let cdt = {initclause
			    with
			     litx_pos = [goal] ;
			     numero = new_num_clause ();
			   } in
	  if
	    !trace_proof || !splitting
	  then
	    Hashtbl.add allclauses cdt.numero cdt;
	  cndats:=majcndats cdt !cndats !djvues)
  with
  | Metavar
    -> (let cdt = {initclause
			 with
			  litx_ukn = [goal] ;
			  numero = new_num_clause ();
			} in
	 if
	    !trace_proof || !splitting
	  then
	    Hashtbl.add allclauses cdt.numero cdt;
	cndats:=majcndats cdt !cndats !djvues)



(* fonction de merge qui évite de créer des paires *)
(* en mergeant deux listes triées sans paires *)
(* et élimine un élément l s'il est dans les listes *)

  let rec merge_except l l1 l2 =

    match l1, l2 with
    | [], l2 -> except l l2
    | l1, [] -> except l l1
    | h1 :: t1, h2 :: t2
      ->
        (match compare_formula h1 l,compare_formula h2 l with
        | 0,0 -> merge_perso compare_formula t1 t2
        | 0,_ -> merge_except l t1 l2
        | _,0 -> merge_except l l1 t2
        | _,_
          ->
            (match compare_formula h1 h2 with
	    | -1 -> h1 :: merge_except l t1 l2
	    | 1  -> h2 :: merge_except l l1 t2
	    | _  -> h1 :: merge_except l t1 t2))



(* merge trois listes sans paires en une liste sans paires *)

  let rec merge_3 l1 l2 l3 =

    match l1,l2,l3 with
    | [],[],l3 -> l3
    | [],l2,[] -> l2
    | l1,[],[] -> l1
    | [],l2,l3 -> merge_perso compare_formula l2 l3
    | l1,[],l3 -> merge_perso compare_formula l1 l3
    | l1,l2,[] -> merge_perso compare_formula l1 l2
    | h1::t1,h2::t2,h3::t3
      ->
        (match compare_formula h1 h2 with
        | -1 (* h1<h2 *)
          ->
            (match compare_formula h1 h3 with
            | -1 -> h1 :: merge_3 t1 l2 l3 (* h1<h3 *)
            | 0 -> h1 :: merge_3 t1 l2 t3 (* h1=h3 *)
            | _ -> h3 :: merge_3 l1 l2 t3) (* h1>h3 *)
        | 0 (* h1 = h2 *)
          ->
            (match compare_formula h2 h3 with
            | -1 -> h1 :: merge_3 t1 t2 l3 (* h2<h3 *)
            | 0 -> h1 :: merge_3 t1 t2 t3 (* h2=h3 *)
            | _ -> h3 :: merge_3 l1 t2 t3) (* h2>h3 *)
        | _ (* h1>h2 *)
          ->
            (match compare_formula h2 h3 with
            | -1 -> h2 :: merge_3 l1 t2 l3 (* h2<h3 *)
            | 0 -> h2 :: merge_3 l1 t2 t3 (* h2=h3 *)
            | _ -> h3 :: merge_3 l1 l2 t3)) (* h2>h3 *)



(* recollement de deux clauses après une résolution *)
(* On suppose que l est positif pour c1 et négatif pour c2 *)
(* autrement dit, on fait disparaître l positif en c1 et négatif en c2 *)
(* n est la taille de l'unificateur *)
(* lp, ln et lu sont des listes de formules à ajouter, conditions à l'unification *)

  let merge n l c1 c2 lp ln lu =
    (* attention : peut-on avoir True ou False ? *)
    (* A priori non... *)
    (* Sinon ça change, car la clause peut être une tautologie (cas True) *)
    (* ou contenir des éléments inutiles (False) *)

    let clause =
      { c2 with
	litx_pos = merge_3 lp (except l c1.litx_pos) c2.litx_pos ;
	litx_neg = merge_3 ln c1.litx_neg (except l c2.litx_neg) ;
	litx_ukn = merge_3 lu c1.litx_ukn c2.litx_ukn ;
	litx_ps = merge_perso compare c1.litx_ps c2.litx_ps ;
	litx_ns = merge_perso compare c1.litx_ns c2.litx_ns ;
      }
    in

    let rhist = merge_hist c1.histrlist c2.histrlist in

    let chist = merge_hist c1.histclist c2.histclist in

    let chist = add_hist_c chist c1 in

    let chist = add_hist_c chist c2 in

    let i1 = c1.indice in

    let i2 = c2.indice in

    let pds =
      pds_res
	~n:n
	~indice1:i1
	~indice2:i2
	~rhist:rhist
	~chist:chist
	~c1w:c1.poids
	~nc1:((List.length c1.litx_pos) + (List.length c1.litx_neg) + (List.length c1.litx_ukn))
	~c2w:c2.poids
	~nc2:((List.length c2.litx_pos) + (List.length c2.litx_neg) + (List.length c2.litx_ukn))
	~l:(size l)
    in

    let ind =
      indice_res
	~i1:i1
	~i2:i2
	~chist:chist
	~rhist:rhist
    in

    {clause with
     poids = pds;
     numero = new_num_clause () ;
     indice = ind;
     histclist = chist ;
     histrlist = rhist ;
   }



(* recollement de deux clauses après une contraction *)
(* On suppose que l est positif pour c1 et négatif pour c2 *)
(* autrement dit, on fait disparaître l positif en c1 et négatif en c2 *)
(* lp, ln et lu sont des listes de formules à ajouter, conditions à l'unification *)
(* clause est la clause parent, dont on prend les historiques *)

  let merge_contr l clause c1 c2 lp ln lu =

    let clause =
      { clause with
	litx_pos = merge_3 lp (except l c1.litx_pos) c2.litx_pos ;
	litx_neg = merge_3 ln c1.litx_neg (except l c2.litx_neg) ;
	litx_ukn = merge_3 lu c1.litx_ukn c2.litx_ukn ;
	litx_ps = merge_perso compare c1.litx_ps c2.litx_ps ;
	litx_ns = merge_perso compare c1.litx_ns c2.litx_ns ;
      }
    in

    let chist = add_hist_c clause.histclist clause in

    let pds =
      pds_cont
	~wpere:clause.poids
	~l:(size l)
    in

    {clause with
     poids = pds;
     numero = new_num_clause () ;
     histclist = chist ;
   }



(* Pour traiter du cas particulier du splitting *)
(* une fonction qui lance la mise à jour particulière *)
(* le type de a3 est rajouté pour raisons de compilation *)

  let premajcndats cdt lcndts (ldjvues : ((Logic.formula, 'b) Ptypes.clause * 'c) list) =

    try
      majcndats cdt lcndts ldjvues
    with
    | EmptySplit (* on sait déjà que ce n'est pas une tautologie par build_resolvante *)
      ->
	 if
	   List.exists (fun cd -> subsume cd cdt) !empty_s_clauses
	 then (* cette clause est subsumée *)
	   lcndts
	 else
	   (let list =
	     (List.map (fun n -> mklit n true) cdt.litx_ps)
	     @
	       (List.map (fun n -> mklit n false) cdt.litx_ns) in
	   try
	     split_add list; (* on rappelle qu'il y a au moins un littéral i.e. list est non vide *)
	     empty_s_clauses := cdt::(majesclauses cdt !empty_s_clauses);
	     let cndts,djvs = add_empty_with_split cdt lcndts ldjvues in
	     djvues:=djvs;
	     cndts
	   with
	   | Unsat -> raise Proved)



(* Fait le splitting d'une clause *)
(* Coupe en le plus possible de morceaux *)

  let split_clause c =

    let fait_morceaux accu liste2add pol ukn =
      (* morceaux_courant de type (pos list,neg list,ukn list,varset) list *)
      (* ukn est pour savoir si l'on traite des metavars *)
      (* pol est dans les autres cas, pos ou neg *)

      let rec enroleur lp ln lu set acc l =
	match l with
	| []
	  ->(lp,ln,lu,set)::acc
	| ((lpp,lnp,lup,setp) as e)::l
	  ->if is_empty_inter_varset set setp
	     then
	       enroleur lp ln lu set (e::acc) l
	     else
	       enroleur
		 (merge_perso compare_formula lp lpp)
		 (merge_perso compare_formula ln lnp)
		 (merge_perso compare_formula lu lup)
		 (union_varset set setp)
		 acc
		 l
      in

      let en_cours = ref accu in

      if
	ukn
      then
	List.iter (fun f -> en_cours:=enroleur [] [] [f] (vars_of_formula f) [] !en_cours) liste2add
      else
	if
	  pol
	then
	  List.iter (fun f -> en_cours:=enroleur [f] [] [] (vars_of_formula f) [] !en_cours) liste2add
	else
	  List.iter (fun f -> en_cours:=enroleur [] [f] [] (vars_of_formula f) [] !en_cours) liste2add;
      !en_cours
    in


    let current = ref (current_litname ()) in

    let rec make_clauses morceaux num =

      if
	num=1
      then
	match morceaux with
	| [_]
	  ->
	    [c] (* on est certain ainsi du bon tri des littéraux *)
	| m::morceaux
	  ->
	    (let (pl,nl,ul,_)=m in
	    let n =
	      (match (pl,nl,ul) with
	      | ([f],[],[] | [],[f],[] | [],[],[f])
		->
		  (try
		    MapSplit.find f !memory_split
		  with
		  | Not_found
		    ->
		      (let n = new_litname () in
		      memory_split:=MapSplit.add f n !memory_split;
		      n))
	      | _,_,_
		->
		  new_litname ())
	    in
	    current:=n;
	    let cl = {c with
		      litx_pos = pl;
		      litx_neg = nl;
		      litx_ukn = ul;
		      litx_ps = merge_perso compare [n] c.litx_ps;
		      litx_ns = c.litx_ns;
		      numero = new_num_clause ();
		      vientde = Split(c.numero,c.vientde,num)
		    } in
	    Hashtbl.add allclauses cl.numero cl;
	    cl::(make_clauses morceaux (num+1)))
	| _
	  ->
	    assert false
      else
	match morceaux with
	| [m] (* il s'agit du dernier *)
	  ->
	    let cn = !current in
	    let (pl,nl,ul,_)=m in
	    let cl = {c with
		      litx_pos = pl;
		      litx_neg = nl;
		      litx_ukn = ul;
		      litx_ps = c.litx_ps;
		      litx_ns = merge_perso compare [cn] c.litx_ns;
		      numero = new_num_clause ();
		      vientde = Split(c.numero,c.vientde,num)
		    } in
	    Hashtbl.add allclauses cl.numero cl;
	    [cl]
	| m::morceaux
	  ->
	    (let (pl,nl,ul,_)=m in
	    let cn = !current in
	    let n =
	      (match (pl,nl,ul) with
	      | ([f],[],[] | [],[f],[] | [],[],[f])
		->
		  (try
		    MapSplit.find f !memory_split
		  with
		  | Not_found
		    ->
		      (let n = new_litname () in
		      memory_split:=MapSplit.add f n !memory_split;
		      n))
	      | _,_,_
		->
		  new_litname ())
	    in
	    current:=n;
	    let cl = {c with
		      litx_pos = pl;
		      litx_neg = nl;
		      litx_ukn = ul;
		      litx_ps = merge_perso compare [n] c.litx_ps;
		      litx_ns = merge_perso compare [cn] c.litx_ns;
		      numero = new_num_clause ();
		      vientde = Split(c.numero,c.vientde,num)
		    } in
	    Hashtbl.add allclauses cl.numero cl;
	    cl::(make_clauses morceaux (num+1)))
	| _
	  ->
	    assert false
    in

    let m = fait_morceaux [] c.litx_pos true false in
    let m = fait_morceaux m c.litx_neg false false in
    let m = fait_morceaux m c.litx_ukn false true in

    make_clauses m 1


(* itère decompose_literal sur la clause *)

  let decompose_clause cla =

    let decomposees = Hashform.create 200 in

    let rec decompose_litteral litteral b c =
      (* fait des décompositions successives sur un litteral avec les règles *)
      (* b est un booléen qui indique si le littéral est positif ou négatif ( true / false ) *)
      (* c est le reste de la clause *)

      if
	ordrepoids c.poids !pdsmax_global=1
      then
	() (* le poids est déjà trop important, on coupe la branche *)
      else
	(let k = (head_symbol litteral,b) in

	Hashform.add decomposees k (c,litteral);

	let decomp_list = get_rules !(c.contr) litteral b in

	let apply_decompose_litteral cl lp ln = (* lp et ln sont déjà setifiées *)

	   (* nous venons de décomposer le littéral l *)
	   (* nous continuons à décomposer *)
	   (* applique decompose_literal aux littéraux de lp,ln *)

	  let f_pos c l =
	    for i=0 to ((List.length l)-1)
	    do
	      let l_p,elt = list_delete_nth l i in
	      decompose_litteral elt true {c with litx_pos = merge_except elt l_p c.litx_pos }
	    done
	  in

	   let f_neg c l =
	     for i=0 to ((List.length l)-1)
	     do
	       let l_n,elt = list_delete_nth l i in
	       decompose_litteral elt false {c with litx_neg = merge_except elt l_n c.litx_neg }
	     done
	  in

	  match lp,ln with
	  | [],[] ->
		cndats:=premajcndats cl !cndats !djvues
		    (* le littéral disparaît (equiv à Faux) ; si la clause est vide alors prouvé *)
	  | _,_ ->
	      (f_pos { cl with litx_neg = merge_perso compare_formula ln cl.litx_neg} lp;
	      f_neg { cl with litx_pos = merge_perso compare_formula lp cl.litx_pos} ln)
	in

	let use_rules declist =
	  List.iter
	    (fun (name,rw,subst,contr,ll)
	      ->
	      let lp,ln,lu = pos_neg_list ll in
              (* on triera lp en mettant true devant *)
              (* on peut utiliser un try with *)
              (* puis on triera (si true n'a pas été trouvé) ln en mettant true devant aussi *)
	      if
		List.exists (fun f -> is_true f) lp
	      then
		()
	      else
		(let histrlist=add_hist_r c.histrlist name in

		let rindice,nbre = List.assoc name histrlist in

		let i = c.indice in

		let pds =
		  pds_rule
		    ~rindice:rindice
		    ~indice:i
		    ~nbre:nbre
		    ~pds:c.poids
		    ~rpds:rw
		in

		let ind =
		  indice_rule
		    ~i:i
		    ~hist:histrlist
		in

		let cl = { (apply_subst_clause subst c)
			with
			  poids = pds ;
			  vientde = Decomp(c.numero,c.vientde,litteral,name) ;
			  numero = new_num_clause () ;
			  contr = ref contr ;
			  histrlist = histrlist ;
			  indice = ind ;
			  litx_ukn = merge_perso compare_formula lu c.litx_ukn ;
			}
		in

		let ln = List.filter (fun f -> not (is_true f)) ln in

		if
		  !trace_proof || !splitting
		then
		  (Hashtbl.add
		     allclauses
		     cl.numero
		     {cl with
		      litx_pos = merge_perso compare_formula lp cl.litx_pos ;
		      litx_neg = merge_perso compare_formula ln cl.litx_neg ;
		    };
		   Hashtbl.add
		     initallclauses
		     cl.numero
		     {cl with
		      litx_pos = merge_perso compare_formula lp cl.litx_pos ;
		      litx_neg = merge_perso compare_formula ln cl.litx_neg ;
		    });

		apply_decompose_litteral cl lp ln
	    ))
	    declist
	in

	use_rules decomp_list)
    in

    let aux_p l =
      for i=0 to ((List.length l)-1)
      do
	let l_p,elt = list_delete_nth l i in
	decompose_litteral elt true {cla with litx_pos = l_p}
      done
    in

    let aux_n l =
      for i=0 to ((List.length l)-1)
      do
	let l_p,elt = list_delete_nth l i in
	decompose_litteral elt false {cla with litx_neg = l_p}
      done
    in

    aux_p cla.litx_pos;
    aux_n cla.litx_neg;

    cla,decomposees



(* teste si une clause est dans un sous-cas de l'autre *)
(* les littéraux de splitting sont supposés être triés *)

  let subcase l1p l1n l2p l2n =

    let rec fst_sub_snd l1 l2 =
      match l1,l2 with
      | [],[] -> true
      | [],_::_ -> true
      | _::_,[] -> false
      | a1::l1,a2::l2
	->
	  if
	    a1=a2
	  then
	    fst_sub_snd l1 l2
	  else
	    fst_sub_snd (a1::l1) l2
    in

    let rec which_one_sub l1 l2 =
      match l1,l2 with
      | [],[] -> "both"
      | [],_::_ -> "1"
      | _::_,[] -> "2"
      | a1::l1,a2::l2
	->
	  if
	    a1=a2
	  then
	    which_one_sub l1 l2
	  else
	    if
	      fst_sub_snd (a1::l1) l2
	    then
	      "1"
	    else
	      if
		fst_sub_snd (a2::l2) l1
	      then
		"2"
	      else
		"none"
    in

    match which_one_sub l1p l2p with
    | "both"
      ->
	(match which_one_sub l1n l2n with
	| "none" -> false
	| _ -> true)
    | "1"
      -> fst_sub_snd l1n l2n
    | "2"
      -> fst_sub_snd l2n l1n
    | _
      -> false



(* construit la résolvante entre deux clauses connaissant les littéraux *)
(* On suppose que l1 est positif pour c1 et l2 négatif pour c2 *)
(* renvoie n,c1,c2,lit après l'unif s'il y a un resolvant *)
(* où n est la taille de l'unificateur *)
(* lève l'exception Build_fails sinon *)
(* lit est utile pour merge *)

  let build_resolvante c1 l1 c2 l2 =

    try

      (* cas des résolutions négative et positive *)

      if
	((!met="nhr" && c2.litx_pos!=[]) || (!met="phr" && c1.litx_neg!=[]))
      then
	raise Unif_fails;

      (* on regarde si on ne va pas faire une tautologie avec les lits de splitting *)
      (* alors inutile de le regarder dans la mise à jour des listes *)

      if
	!splitting
      then
	(let l1p = c1.litx_ps in
	let l1n = c1.litx_ns in
	let l2p = c2.litx_ps in
	let l2n = c2.litx_ns in
	let lps = l1p@l2p in
	let lns = l1n@l2n in
	if
	  List.exists (fun g -> List.exists (fun f -> f=g) lps) lns
	then
	  raise Unif_fails (* ce serait une tautologie *)
	else
	  if
	    !check_subcase && not (subcase l1p l1n l2p l2n)
	  then
	    raise Unif_fails (* ce n'est pas un sous-cas *)
	);


      (if
	!verbose>=5
      then
	(Format.print_string "On tente l'unif de '";
	 print_formula l1;
	 Format.print_string "' et '";
	 print_formula l2;
	 Format.print_string"'";
	 Format.print_newline ();
	 Format.print_string "Le reste des clauses :";  Format.print_newline ();
	 Format.print_string "c1 = ";
	 print_clause c1 ; Format.print_newline ();
	 Format.print_string "c2 = ";
	 print_clause c2 ; Format.print_newline ()));

      (* on renomme d'abord les littéraux *)

      let ren = get_renaming_formula (empty_renaming ()) l1 in
      let ren = get_renaming_clause ren c1 in
      let ren = get_renaming_constraints ren !(c1.contr) in
      let l2 = rename_formula ren l2 in
      let contr2 = rename_constraints ren !(c2.contr) in

      (if
	!verbose>=5
      then
	(Format.print_string "l2 devient ";
	 print_formula l2;
	 Format.print_string"'";
	 Format.print_newline ()));
      let n,subs,contrcouple,cont,l,ll = unif (Unification(!(c1.contr),contr2)) l1 l2 in
      let cont1,cont2 = match contrcouple with Unification(a,b) -> a,b | _ -> assert false in

      let lp,ln,lu = pos_neg_list ll in

      (* on renome ensuite le reste des clauses *)

      let c2 = rename_clause ren c2 in
      (if
	!verbose>=5
      then
	(Format.print_string "c2 est devenue "; Format.print_newline ();
	 print_clause c2 ; Format.print_newline ()));

      (* on applique la substitution aux clauses *)

      let c1 = apply_subst_clause subs c1 in
      let _ = c1.contr:=cont1 in
      let c2 = apply_subst_clause subs c2 in
      let _ = c2.contr:=cont2 in

      n,l,c1,c2,lp,ln,lu,cont

  with
  | Unif_fails -> raise Build_fails



(* fait les contractions en unifiant un littéral bien précis *)
(* sur les positifs de la première clause *)
(* et sur les négatifs de la seconde *)
(* Donne la liste des lit,clause1,clause2,contr_avant,contr_maintenant,lp,ln,lu tout déjà substitué *)

let contract l c1 c2 contrainte =

  let rec aux l lp1 ln2 c1 c2 lp ln lu actucont =
    match lp1,ln2 with
    | [],[] -> []
    | e::lp1,_
      ->
	(try
	  let _,subs,changecont,newcont,newl,ll = unif (Contraction(actucont)) l e in
	  (aux l lp1 ln2 c1 c2 lp ln lu actucont) (* on passe *)
	  @
	  let l = newl in
	  let lpp,lnp,lup=pos_neg_list ll in
	  let changecont = match changecont with | Contraction(a) -> a | _ -> assert false in
	  let lp = merge_perso compare_formula lpp (List.map (fun f -> apply_subst subs f) lp) in
	    (* on n'est pas certain que la subs conserve l'ordre *)
	  let ln = merge_perso compare_formula lnp (List.map (fun f -> apply_subst subs f) ln) in (* idem *)
	  let lu = merge_perso compare_formula lup (List.map (fun f -> apply_subst subs f) lu) in (* idem *)
	  let c1 = apply_subst_clause subs c1 in
	  let c2 = apply_subst_clause subs c2 in
	  let lp1 = except l (List.map (fun f -> apply_subst subs f) lp1) in
	  let ln2 = except l (List.map (fun f -> apply_subst subs f) ln2) in
	  ((l,c1,c2,changecont,newcont,lp,ln,lu)::(aux l lp1 ln2 c1 c2 lp ln lu newcont)) (* on s'arrête / on continue *)
	with
	| Unif_fails -> aux l lp1 ln2 c1 c2 lp ln lu actucont)
    | _,e::ln2
      -> (* c'est la même chose *)
	(try
	  let _,subs,changecont,newcont,newl,ll = unif (Contraction(actucont)) l e in
	  (aux l lp1 ln2 c1 c2 lp ln lu actucont) (* on passe *)
	  @
	  let l = newl in
	  let lpp,lnp,lup=pos_neg_list ll in
	  let changecont = match changecont with | Contraction(a) -> a | _ -> assert false in
	  let lp = merge_perso compare_formula lpp (List.map (fun f -> apply_subst subs f) lp) in
	    (* on n'est pas certain que la subs conserve l'ordre *)
	  let ln = merge_perso compare_formula lnp (List.map (fun f -> apply_subst subs f) ln) in (* idem *)
	  let lu = merge_perso compare_formula lup (List.map (fun f -> apply_subst subs f) lu) in (* idem *)
	  let c1 = apply_subst_clause subs c1 in
	  let c2 = apply_subst_clause subs c2 in
	  let lp1 = except l (List.map (fun f -> apply_subst subs f) lp1) in
	  let ln2 = except l (List.map (fun f -> apply_subst subs f) ln2) in
	  ((l,c1,c2,changecont,newcont,lp,ln,lu)::(aux l lp1 ln2 c1 c2 lp ln lu newcont))
	with
	| Unif_fails -> aux l lp1 ln2 c1 c2 lp ln lu actucont)
  in

  aux l c1.litx_pos c2.litx_neg c1 c2 [] [] [] contrainte


(* crée et ajoute une clause candidate obtenue par résolution *)
(* On suppose que l1 est positif pour r1 *)
(* et l2 est négatif pour r2 *)

  let add_resol c1 l1 c2 l2 =

    try
      let n,l,c1,c2,lp,ln,lu,cont = build_resolvante c1 l1 c2 l2 in
      if
	!verbose>=4
      then
	(Format.print_string "unification réussie\n";
	 Format.print_string "l = ";
	 print_formula l;
	 Format.print_newline();
	 Format.print_string "c1 = ";
	 print_clause c1 ; Format.print_newline ();
	 Format.print_string "c2 = ";
	 print_clause c2 ; Format.print_newline ());
      let clause = { (merge n l c1 c2 lp ln lu) with
		     vientde = Resol(c1.numero,c1.vientde,c2.numero,c2.vientde,l) ;
		     contr = ref cont ;
		   } in
      if
	!trace_proof || !splitting
      then
	Hashtbl.add allclauses clause.numero clause;
      if
	!verbose>=4
      then
	(Format.print_string "clause obtenue = ";
	 print_clause clause ; Format.print_newline ());
      cndats:=premajcndats clause !cndats !djvues;
      let contrac_list = contract l c1 c2 cont in
      List.iter
	(fun (l,c1,c2,_contravant,contrapres,lp,ln,lu)
	  ->
	    let cl = { (merge_contr l clause c1 c2 lp ln lu) with
	      vientde = Contrac(clause.numero,clause.vientde,l) ;
	      contr = ref contrapres ;
	      } in (* la gestion des contraintes est mauvaise *)
	    if
	      !trace_proof || !splitting
	    then
	      Hashtbl.add allclauses cl.numero cl;
	    cndats:=premajcndats cl !cndats !djvues;
	)
      contrac_list
  with
  | Build_fails -> ()



(* Fait toutes les résolutions possibles *)
(* d'abord entre les décompositions de la clause *)
(* puis entre les décompositions et les djvues *)
(* fait la mise à jour des candidates au début *)
(* puis y ajoute la candidate à la fin *)

  let all_resol e =

    let c,dec = e in

    djvues:=e::(majdjvues c !djvues);

    (* on fait les résolutions entre les propres décompositions de c *)
    (* puis celles avec les décompositions des autres clauses *)

    Hashform.iter
      (fun (s,b) (c1,l1)
	->
		  if b
		  then
		    (List.iter
		      (fun (c2,l2)
			->
			   add_resol c1 l1 c2 l2
		      )
		      (Hashform.find_all dec (s,false));
		    List.iter
		      (fun (_,dec2)
			->
			  List.iter
			    (fun (c2,l2)
			      ->
				add_resol c1 l1 c2 l2
			    )
			    (Hashform.find_all dec2 (s,false))
		      )
		      (List.tl !djvues))
		  else
		    List.iter
			(fun (_,dec2)
			  ->
			    List.iter
			      (fun (c2,l2)
				->
				  add_resol c2 l2 c1 l1
			      )
			      (Hashform.find_all dec2 (s,true))
			)
			(List.tl !djvues)
      )
      dec



(* prendre au maximum n éléments d'une liste *)

  let rec list_sub l n =
    match (l,n) with
    | (_,0)        -> []
    | ([],_)       -> []
    | (a::reste,_) -> a :: (list_sub reste (n-1))



(* ajoute un axiome aux djvues (plus précisément à initdjvues) *)
  exception NotAxiom
  exception AlwaysTrue

  let axiom (e,n,c,i) =

    try
      let clause =
	(try
	  (let b = negative_formula e in
	  let e = elim_all_neg e in
	  if
	    b
	  then
	    if
	      is_true e
	    then
	      raise NotAxiom (* cela signifie que la formule est Faux donc on a la clause vide *)
	    else
	      let pds = initpoids n in
	      {initclause
	      with
	       litx_neg = [e] ;
	       numero = new_num_clause () ;
	       poids = pds ; contr = ref c ;
	       indice = indice_of_int i
	     }
	  else
	    if
	      is_true e
	    then
	      raise AlwaysTrue
	    else
	      let pds = initpoids n in
	      {initclause
	      with
	       litx_pos = [e] ;
	       numero = new_num_clause () ;
	       poids = pds ; contr = ref c ;
	       indice = indice_of_int i
	     })
  with
  | Metavar -> raise NotAxiom)

      in

      let hash = decompose_clause clause in
      initdjvues:=hash::(!initdjvues);
      Hashtbl.add initallclauses clause.numero clause

  with
  | NotAxiom -> (Format.print_string "Ce ne peut pas être un axiome"; Format.print_newline())
  | AlwaysTrue -> (Format.print_string "Vrai ne peut être ajoutée"; Format.print_newline())



(* réinitialise complètement les djvues *)

let real_init _ =
  initdjvues:=[];
  Hashtbl.clear initallclauses

exception TimeOut

(* initialise les valeurs au départ de la preuve *)
let init _ =
  djvues:=!initdjvues;
  cndats := [];
  taillecndats := 0;
  empty_s_clauses := [];
  if
    !trace_proof || !splitting
  then
    (Hashtbl.clear allclauses;
     Hashtbl.iter (fun a b -> Hashtbl.add allclauses a b) initallclauses;
     Hashtbl.add allclauses 0 initclause;
     empty_clause:=0);
  if
    !splitting
  then
    (init_lit_state ();
     memory_split:= MapSplit.empty)



(* foncion qui arrête le processus si le temps est fini *)

  let time_out _ =
    Format.print_flush();
    Format.print_string "Temps imparti écoulé\n";
    Format.print_flush();
    raise TimeOut



(* fonction principale de résolution *)

  let prove ?(methode="n") hyp_list goal =

    Sys.catch_break true;
    (match !timemax,!verbose with
    | n,v when (v<2 && n>0)
      ->
	(let _ = Unix.alarm n in
        Sys.set_signal Sys.sigalrm (Sys.Signal_handle time_out);
	())
    | _,_ -> ());

    met:=methode;

    let rec res _ =
      match !cndats with
      | []
	->raise Prove_fails
      | _
	->
	  (let cdt = List.hd !cndats in
	  cndats := List.tl !cndats;
	  taillecndats:= (!taillecndats)-1;

	  if
	    !verbose>=3
	  then
            (Format.print_string "La clause ajoutée :";
	     Format.print_newline();
	     Format.print_newline();
	     print_clause cdt;
	     Format.print_newline();
	     Format.print_newline());


	  let cdts_list = (* plus tard, ajouter les contractions ici *)
	    if
	      !splitting
	    then
	      (let lsplit = split_clause cdt in
	      if
		!verbose>=3
	      then
		(Format.print_string "Le splitting de la clause donne :";
		 Format.print_newline();
		 Format.print_newline();
		 print_clause_list lsplit;
		 Format.print_newline();
		 Format.print_newline());
	      lsplit)
	    else
	      [cdt]
	  in

	  let decomp_list = List.map decompose_clause cdts_list in
	  (* fait les décompositions des clauses de la liste *)
	  (* en gardant en mémoire les clés (symb de tête,signe) *)
	  (* Une décomposée est une table de Hash *)


	  if
	    !verbose>=3
	  then
	    (Format.print_string "Les décompositions :";
	     Format.print_newline();
	     Format.print_newline();
	     print_clause_list
	       (List.flatten
		  (List.map
		     (fun (_,dec)
		       ->
			 let temp = ref [] in
			 Hashform.iter
			   (fun (_,b) (c,l)
			     ->
			       temp:=
				 (if
				   b
				 then
				   {c with litx_pos = l::(c.litx_pos)}
				 else
				   {c with litx_neg = l::(c.litx_neg)})
				 ::(!temp))
			   dec;
			 !temp )
		     (list_sub decomp_list 10)));
	     Format.print_newline();
	     Format.print_newline(););


	  List.iter all_resol decomp_list;
	  (* all_resol doit mettre à jour les djvues *)
	  (* puis ajouter chaque clause dans  djvues *)
	  (* travaille sur décomposees *)

	  if
	    !verbose>=2
	  then
            (Format.print_string "Les clauses déjà vues :";
	     Format.print_newline();
	     Format.print_newline();
	     print_clause_list (List.map fst (list_sub !djvues 10));
	     Format.print_newline();
	     Format.print_newline();
	     Format.print_string "Les clauses candidates :";
	     Format.print_newline();
	     Format.print_newline();
	     print_clause_list (list_sub !cndats 10);
	     Format.print_newline();
	     Format.print_newline();
	     Format.print_string "taille !djvues : ";
	     Format.print_int (List.length !djvues);
	     Format.print_newline();
	     Format.print_string "taille taillecndats : ";
	     Format.print_int !taillecndats;
	     Format.print_newline();
	     Format.print_newline();
             (if
               !pause
             then
  	       (Format.print_string "?(exit pour arrêter - c pour ne plus arrêter - entrée sinon) ";
		Format.print_flush();
		let c = read_line () in
		match c with
		| "exit" -> raise Exit
		| "c" -> (verbose:=1; res ())
		| _ -> res ())
	     else
	       res ()))
	  else
	    res ())
    in

    let v = !verbose in

    try
      init ();

      add_hyplist_to_cndats hyp_list;
      add_goal_to_cndats goal;

      res ();

    with
    |e
      ->Sys.set_signal Sys.sigalrm Sys.Signal_ignore;
        (match e with
        | Exit
          ->(Format.print_string "Calcul arrêté";
	     Format.print_newline();
	     verbose:=v;
	     raise Prove_fails)
        | TimeOut
          ->raise Prove_fails
        | Prove_fails
          ->(Format.print_string "La formule n'est pas prouvée (plus de candidats)";
	     Format.print_newline();
	     verbose:=v;
	     raise Prove_fails)
        | Proved
          ->(Format.print_string "La formule est vraie";
	     Format.print_newline();
	     verbose:=v;
	     if
	       !verbose>=1 && !trace_proof
	     then
	       (let last_empty_clause = Hashtbl.find allclauses !empty_clause in
	       (if
	         !splitting && !verbose>=3
	       then
		 (Format.print_string "L'ensemble satisfaisable :";
		  Format.print_newline();
		  print_clause_list !empty_s_clauses;
		  Format.print_string "La clause C :";
		  Format.print_newline();
		  print_clause last_empty_clause;
		  Format.print_newline()));
	       Format.print_string "Voici la preuve :";
	       Format.print_newline();
	       (try
		 print_proof (proof_search !empty_s_clauses last_empty_clause) allclauses
	       with
	       | Noprinting ->
	           Format.print_string "Désolé, pas de preuve :";
	           Format.print_newline())))
        | Sys.Break
          ->(Format.print_string "Preuve annulée";
	     Format.print_newline();
	     raise Prove_fails)
        | e
          ->raise e)

end
