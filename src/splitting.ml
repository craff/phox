(* Gestion des clauses vides avec littéraux de splitting *)



(* les types pour le splitting *)



(* type de nom de litéral *)

type litname = int

let print_litname n =
  Format.print_string ("sp"^string_of_int n)

(* type de litéral *)

type slit = { name : litname ; pol : bool }



(* type d'arbre *)

type truetree = Nil of bool | Nodtt of litname * truetree * truetree



(* crée un litéral par son nom et sa polarité *)

let mklit n b = { name=n ; pol=b}



(* crée un nouveau nom de litéral, donne le nom courant *)

let new_litname,current_litname,reinit_litnames =
  let c = ref 0 in
  (fun () -> let n = !c+1 in c:=n; n),
  (fun () -> !c),
  (fun () -> c:=0)



(* l'état de la preuve *)
(* soit l'arbre de vérité *)

let lit_state = ref (Nil true)



(* initialise l'état de la preuve *)

let init_lit_state () =
  lit_state:=(Nil true);
  reinit_litnames ()



(* cherche et enlève un élément d'une liste *)

exception NotMember

let mem_remove e l =

  let rec mem_rem e acc l =
    match l with
    | []
      -> raise NotMember
    | elt::l
      ->
	if e=elt.name then (List.rev_append acc l),elt else mem_rem e (elt::acc) l
	  (* on garde l'ordre, mais est-ce necessaire ? *)
  in

  mem_rem e [] l



(* ajoute une liste de disjonctions à un arbre *)
(* la liste est non vide *)

let rec add list tree =

    match tree with
    | Nodtt (a,t1,t2)
      ->
	(try
	  (
	   let l,e = mem_remove a list in
	   match l with
	   | []
	     ->
	       if e.pol
	       then Nodtt(a,t1,Nil false)
	       else Nodtt(a,Nil false,t2)
	   | _
	     ->
	       if e.pol
	       then Nodtt(a,t1,add l t2)
	       else Nodtt(a,add l t1,t2)
	  )
	with
	| NotMember -> Nodtt(a,add list t1,add list t2)
	)
    | Nil false -> Nil false
    | Nil true
      ->
	(
	 let l,e = match list with | e::l -> l,e | _ -> assert false in
	 match l with
	 | []
	   ->
	     if e.pol
	     then Nodtt(e.name,Nil true,Nil false)
	     else Nodtt(e.name,Nil false,Nil true)
	 | _
	   ->
	     if e.pol
	     then Nodtt(e.name,Nil true,add l (Nil true))
	     else Nodtt(e.name,add l (Nil true),Nil true)
	)



(* Simplification d'un arbre *)

let rec simpltree t =

  match t with
  | Nodtt (a,t1,t2)
    ->
      (let t1 = simpltree t1 in
      let t2 = simpltree t2 in
      match (t1,t2) with
      | (Nil false, Nil false) -> Nil false
      | _ -> Nodtt(a,t1,t2))
  | Nil true -> Nil true
  | Nil false -> Nil false



(* ajoute une liste de littéraux pour l'arbre lit_state *)
(* C'est cette fonction que l'on utilise depuis le prouveur *)

exception Unsat

let split_add list =

  let t = simpltree (add list !lit_state) in
  match t with
  | Nil false
    -> raise Unsat
  | _
    -> lit_state:=t



(* test l'insatisfaisabilité d'une liste de clauses propositionnelles *)
(* si elle est sat, renvoie l'arbre simplifié *)
(* si elle est insat, lève une exception *)

let test_insat list =

  let list = List.sort (fun a b -> compare (List.length a) (List.length b)) list in
  (* ordonne de manière à prendre les clauses les plus petites en premier *)

  let t = ref (Nil true) in

  List.iter
    (
     fun l
       ->
	 t:= simpltree (add l !t);
	 match !t with
	 | Nil false -> raise Unsat
	 | _ -> ()
    )
    list;
  !t
