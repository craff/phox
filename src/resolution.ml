(* $State: Exp $ $Date: 2004/05/24 08:23:24 $ $Revision: 1.9 $ *)
(*######################################################*)
(*			resolution.ml			*)
(*######################################################*)

(* Notes : - il faudra peut-être trier les clauses *)
(*         - faire en sorte que le lit1 soit positif et lit2 negatif *)

(* A faire :                                  *)
(*         - iter1 (relation avec les règles) *)
(*         - add_resol                        *)
(*         - contraction                      *)


open Basic
open Format
open Type.Base
open Data_base.Object
open Type
open Parser
open Lambda_util
open Af2_basic
open Local
open Print
open Typunif
open Typing
open Safe_add
open Type_check
open Pattern
open Flags
open Undo
open Poids

(* clause vide *)

let initclause =
  {
    literals = [];
    weight = initweight;
  }

(* listes des clauses déja vues et candidates *)

let seen : clause list ref = ref []

let cndats : clause list ref = ref []

(* longueur des candidats *)

let cndats_length = ref 0

let localdefs = ref
    {
     cst_def = [];
     caps_def = [];
     local_ctex_tbl = [];
     local_tex_tbl = [];
     local_close_tbl = [];
     cst_eq = []
   }

(* Exception pour sortir du calcul quand la formule est prouvée *)

exception Vraie



(* Prend le début d'une liste de longueur min(n,longueur liste) (pour l'affichage) *)

let rec list_sub l n =
  match (l,n) with
   | (_,0)        -> []
   | ([],_)       -> []
   | (a::reste,_) -> a :: (list_sub reste (n-1))


(* List_iterb anonce à f que l'on a atteint le dernier élément en envoyant false *)

let rec list_iteri f l =
  match l with
  | [] -> ()
  | [a]-> f false a
  | a::l -> f true a; list_iteri f l



(* affiche une clause *)

let print_clause c =
  List.iter
    (fun l ->
      let (e,n,r)=l in
      Format.open_hbox ();
      (* (if
	r
      then
	Format.print_string "rigid "
      else
	Format.print_string "flexible ");
      *)
      (if
	n
      then
	Format.print_string "~");
      print_expr e;
      Format.print_newline (); Format.close_box ())
    c.literals

(* affiche une liste de clauses (va à la ligne ensuite) *)

let print_clause_list cl =
  Format.print_string "--top_list--"; Format.print_newline ();
  list_iteri (fun b c -> print_clause c ; if b then print_string "-----------\n") cl;
  Format.print_string "--end_list--"; Format.print_newline ()



(* Crée un nouveau numéro de clause (pour plus tard) *)

let new_clause () =
  let c = ref 0 in
  (fun () -> let n = !c+1 in  c:=n; n)



(* ajoute un élément (litteral) à une liste *)
(* plus tard c'est ici que l'on fera le tri *)

let add_elt elt liste = elt::liste

(* ajoute un élément à une liste en faisant *)
(* en sorte de ne pas remettre e si sa négation est b *)
(* plus tard c'est ici que l'on fera le tri *)

let add_elt_s elt liste e b = let (exp,n,_)=elt in if (exp=e & n=b) then liste else elt::liste

(* Ajoute un litteral dans une clause, en éliminant les double négations *)
(* b doit être false (pas de négation) , sauf à l'ajout d'un but à l'initialisation *)

let add_literal clause b e =

  let rec fn stack b e =
    match e, stack with
    | EApp(e,a),[] ->
	fn [a] b e
    | EApp(_,_),[a] ->
	{clause with literals = add_elt ((EApp(e,a)),b,true) clause.literals}
    | EAtom(o,_),[a] when o = !not_obj ->
	fn [] (not b) a
    | EAtom(o,k),[] ->
	begin
	  try
	    if !fis_close o then raise Not_found;
	    let e = kind_inst o k in
	    fn stack b e
	  with
	  Not_found ->
            {clause with literals = add_elt (e,b,true) clause.literals}
	end
    |  EAtom(o,k),[a] ->
	begin
	  try
	    if !fis_close o then raise Not_found;
	    let e = kind_inst o k in
	    fn stack b e
	  with
	    Not_found ->
	      {clause with literals = add_elt ((EApp(e,a)),b,true) clause.literals}
	end
    | EAbs(_,_,_), _::_-> let nse = norm_sexpr e stack in fn [] b nse
    | UVar(n,k),_ ->
	begin
	  try
	    let e = (getuvar n) in
	    fn stack b e
	  with Not_found ->
	    {clause with literals = add_elt (e,b,false) clause.literals}
	end
    | EVar _,_ ->
	assert false
    | _,_ ->
	{clause with literals = add_elt (e,b,true) clause.literals}

  in
  fn [] b e



(* Généralise une formule en donnant de nouveaux noms aux variables d'unification *)

let rec generalize_formule renaming expr =
  match expr with
    EApp(e1, e2) ->
      let renaming, e1' = generalize_formule renaming e1 in
      let renaming, e2' = generalize_formule renaming e2 in
      if e1' == e1 && e2' == e2 then renaming, expr
      else renaming, EApp(e1',e2')
  | UVar(n,k) ->
      begin
	try
	   generalize_formule renaming (getuvar n)
	with Not_found -> begin
	  try
            renaming, List.assoc n renaming
	  with Not_found ->
	    let e = UVar(new_uvar(),k) in
	    ((n,e)::renaming), e
	end
      end
  | EAbs(s,e,k) ->
      let renaming, e' = generalize_formule renaming e in
      if e == e' then renaming, expr
      else renaming, EAbs(s,e',k)
  | Path _ -> assert false
  | e -> renaming, e



(* Généralise une clause en donnant de nouveaux noms aux variables d'unification *)

let generalize_clause renaming clause =

  let rec fn renaming lcl clause =
    match lcl with
    | [] -> renaming,clause
    | (e,n,_)::lcl
      -> let renaming,e = generalize_formule renaming e in
      fn renaming lcl (add_literal clause n e)
  in

  fn renaming (List.rev clause.literals) initclause


(* Initialise les premières clauses avec *)
(* la liste des hypothèses (en déja vues) *)
(* et la liste du but (en candidate) *)
(* on triera ici par poids croissant la liste des hypothèses *)

let initsetclauses hyps concl =

  let rec add_hyp hyps clause =
    match hyps with
    | [] -> []
    | e::hyps
      ->(add_literal clause false e)::(add_hyp hyps clause)
  in

  let add_concl concl clause =
    add_literal clause true concl
  in

  let hypsclauses = add_hyp (List.rev hyps) initclause in
  hypsclauses,[add_concl concl initclause]



(* recollement de deux clauses après une unification *)
(* On suppose que e est positif pour c1 et négatif pour c2 *)

let merge c1 c2 e =

  let l1 = List.fold_right (fun a b -> add_elt_s a b e true) c2.literals [] in
  let l = List.fold_right (fun a b -> add_elt_s a b e false) c1.literals l1 in
  let w =  weight_merge c1.weight c2.weight e in
  { literals = l;
    weight = w
  }



(* Fait la résolution quand c'est possible, sinon lève l'exception Clash *)
(* renvoie clause1,clause2,lit s'il y a un resolvant *)
(* lève l'exception Clash sinon *)
(* e est utile pour merge *)

let build_resolvante clause1 e1 clause2 e2  =
  let save_ulocal = get_ulocal () in
  let upos = get_undo_pos () in
  try
    let _ = smatch !localdefs e1 e2 in
    let renaming,clause1 = generalize_clause [] clause1 in
    let renaming,clause2 = generalize_clause renaming clause2 in
    let _,e = generalize_formule renaming e1 in
    set_ulocal save_ulocal; do_undo upos;
    clause1,clause2,e
  with
    Fail_matching ->
      set_ulocal save_ulocal; do_undo upos; raise Clash



(* Fait la contraction quand c'est possible sinon lève l'exception Clash *)

let build_contract accg e1 accd e cd =
  let save_ulocal = get_ulocal () in
  let upos = get_undo_pos () in
  let rec map renaming acc list =
    match list with
    | [] -> renaming,List.rev acc
    | (e,n,r)::list
      ->
	let renaming,e = generalize_formule renaming e in
	map renaming ((e,n,r)::acc) list
  in
  try
    let _ = smatch !localdefs e e1 in
    let renaming,accg = map  [] [] accg in
    let renaming,accd = map renaming [] accd in
    let renaming,cd = map renaming [] cd in
    let _,e = generalize_formule renaming e in
    set_ulocal save_ulocal; do_undo upos;
    accg,accd,e,cd
  with
    Fail_matching ->
      set_ulocal save_ulocal; do_undo upos; raise Clash



(* Itère une fonction sur une expression d'un littéral et le reste de sa clause *)
(* en faisant des résolutions avec les règles *)
(* Attention : flexible a changé... *)

let rec iter1 lit c f =

  (*
  let iter_resolved_rule c1 c2 e = * c1 est le reste de la clause de règle, c2 est c après résolution,
					e est l'expression de lit après resolution *

    let rec aux_p cg e cd =
    match cd with
    | []
      ->
	let c = {c with literals = (List.rev cg)} in
	let c' = * pour merge, la clause de gauche doit avoir le lit positif *
	  if
	    b
	  then
	    merge c c2 lit
	  else
	    merge c2 c lit
	in
	iter1 l false bf c' f
    | l'::cd'
      ->
	let c = {c1 with pos_lit = ((List.rev cg)@cd)} in
	let c' =
	  if
	    b
	  then
	    merge c c2 lit
	  else
	    merge c2 c lit
	in
	iter1 l false bf c' f;
	aux_p (l::cg) l cd'
    in

    let l = c1.literals in

    (match l with
    | [] -> ()
    | hd::tl -> aux [] hd tl);

  in
  *)

  f lit c;
  ()



(* Itère iter1 sur une clause *)

let iter2 c f =

  let rec aux cg cd =
    match cd with
    | []
      ->assert false
    | [l]
      ->iter1 l {c with literals = (List.rev cg)} f
    | l::cd
      ->
	iter1 l {c with literals = ((List.rev cg)@cd)} f;
	aux (l::cg) cd
  in

  let l = c.literals in

  match l with
  | [] -> raise Vraie
  | l -> aux [] l



(* Met à jour les cndats, i.e. ajoute ou non la clause *)
(* si necessaire, et si le poids ne dépasse pas la limite *)
(* Difficulté : comment savoir si deux clauses sont égales *)
(* en effet, les poids ne le disent pas à priori *)

let update_cndats clause =

  let b = ref true in (* indique si l'on doit encore ajouter clause *)

  let not_tauto a = (* A faire *)
    if false
    then
      raise (Failure "tauto")
    else
      true
  in

  let rec add_cdt c liste nmax =
    match (nmax,liste) with
    | (0,_)
      ->let _ = cndats_length:= (!cndats_max_length) in []
    | (_,[])
      ->
	if
	  !b=true
	then
	  let _ = cndats_length:= (!cndats_length +1) in
	  let _ =  updt_greatest_weight c.weight in
	  [c]
	else
	  []
    | (n,a::reste)
      ->
	match (order_weight a.weight c.weight) with
	| -1
	  ->
	    let _ = updt_greatest_weight a.weight in
	    a::(add_cdt c reste (n-1))
	| 0
	  ->
	    if
	      c.literals = a.literals
	    then
	      let _ = cndats_length:= (!cndats_length -1) in
	      add_cdt c reste n
	    else
	      let _ = updt_greatest_weight a.weight in
	      a::(add_cdt c reste (n-1))
	| 1
	  ->
	    if
	      !b=true
	    then
	      let _ = b:=false in
	      let _ = cndats_length:= (!cndats_length +1) in
	      let _ = updt_greatest_weight c.weight in
	      c::(add_cdt c liste (n-1))
	    else
	      let _ =  updt_greatest_weight a.weight in
	      a::(add_cdt c reste (n-1))
	| _ -> assert false
  in

  let updt cdt =
    match cdt with
    | c when List.mem c !cndats
      ->()
    | c when List.mem c !seen
      ->()
    | _
      ->cndats:=(add_cdt cdt !cndats !cndats_max_length)
  in

  b:=true;
  if
    clause.literals = []
  then
    raise Vraie;
  if
    not_tauto clause
  then
    if
      not (more_than_max_weight clause.weight)
    then
      if
	!cndats_length = !cndats_max_length
      then
	(if
	  inferior_to_greatest_weight clause.weight
	then
	  updt clause)
      else
	updt clause



(* regarde s'il y a résolution, si oui regarde s'il faut ajouter *)
(* la clause aux candidats. On suppose que e1 est positif pour r1 *)
(* et e2 est négatif pour r2 *)

let add_resol r1 e1 r2 e2 =

  try
    let r1,r2,e = build_resolvante r1 e1 r2 e2 in
    let clause = merge r1 r2 e in
    update_cndats clause
  with
  | Clash -> ()



(* Fait toutes les résolutions possibles entre deux clauses *)

let all_resol c1 c2 =
  iter2
    c1
    (fun l1 r1
      ->iter2
	  c2
	  (fun l2 r2
	    ->
	      let (e1,n1,ri1)=l1 in
	      let (e2,n2,ri2)=l2 in
	      match n1,n2,(ri1 || ri2) with
	      | (true,false,true) -> add_resol r2 e2 r1 e1
	      | (false,true,true) -> add_resol r1 e1 r2 e2
	      | (_,_,_) -> () ))



(* Fait la contraction sur une clause *)
(* Pour l'instant sur la candidate *)
(* Et positive *)

let contraction c =

  let rec aux cg cd =

    let rec fn accg accd e cd =
      match accd with
      | []-> (List.rev accg),e,cd
      | ((e0,n,r) as l)::accd
	->
	  if (r & (not n))
	  then
	    try
	      let accg,accd,e,cd = build_contract accg e0 accd e cd in
	      fn accg accd e cd
	    with
	    | Clash -> fn (l::accg) accd e cd
	  else
	    fn (l::accg) accd e cd
    in

    match cd with
    | []
      ->assert false
    | [(e,n,r) as l]
      ->
	if
	  (r & not (n))
	then
	  let cg,e,cd = fn [] cg e cd in
	  {c with literals = List.rev ((e,n,r)::cg)}
	else
	  {c with literals = List.rev (l::cg)}
    | ((e,n,r) as l)::cd
      ->
	if
	  (r & not (n))
	then
	  let cg,e,cd = fn [] cg e cd in
	  aux ((e,n,r)::cg) cd
	else
	  aux (l::cg) cd
  in

  match c.literals with
  | [] -> raise Vraie
  | l -> aux [] l


(* Fonction qui ajoute un candidat à seen, *)
(* plus tard enlèvera les clauses de seen qu'elle subsume *)

let add_to_seen cdt =

  let rec aux a l =
    l
      (*
	 match l with
	 | []
	 ->[]
	 | e::reste
	 ->
	 if
	 EnsForm.subset a e.litteraux
	 then
	 aux a reste
	 else
	 e::(aux a reste)
       *)
  in

  cdt::(aux cdt !seen)



(* Règle de résolution appelée de l'exterieur *)

let rule_resolution gl st =
  let concl = gl.concl in
  let hyps = List.map (fun (_,(h,_,_,_,_)) -> h) gl.hyp in
  let _ = localdefs := gl.local in
  let se,cdts = initsetclauses hyps concl in
  let _ = seen := se in
  let _ = cndats := cdts in
  let _ = cndats_length := 1 in

  let rec res () =
    if
      !resol_verbose=1
    then
      (print_clause_list !seen;
       print_clause_list !cndats;);
    match !cndats with
    | []
      ->print_string "La formule est fausse\n"
    | _
      ->
	(let cdts = !cndats in
	let cdt = contraction (List.hd cdts) in
	let _ = cndats := List.tl cdts in
	try
	  (let _ = seen:= add_to_seen cdt in
	  List.iter
	    (fun a -> all_resol a cdt)
            (!seen);
	  res ())
	with
	| Vraie -> print_string "La formule est vraie\n")
  in

  res ();

  [gl,st],[]
