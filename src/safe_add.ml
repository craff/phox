(*######################################################*)
(*			safe_add.ml			*)
(*######################################################*)

open Format
open Type.Base
open Type
open Basic
open Lambda_util
open Typing
open Print
open Local
open Typunif

exception Illegal_prior
exception Two_args
exception Redef of string

let key_kind = Unknown

let illegal_kwd = ref ["";":";":<";"\\]";"\\]]";"\\}";"\\}}"]

let rec add_key b lock = function
  (Key s)::l ->
    if List.mem s !illegal_kwd then raise (Failure
        ("Def. Error: cannot use \""^s^"\" as keyword."));
    (try
      let o = sym_get s in
      match get_syntax o with
        Hiden true  -> ()
      | Hiden false -> if b then
          if is_capsule o then
            failwith ("Def. Error: conflict with the local key \""^s^"\".")
          else set_value o
                {fkind = key_kind;
                 fvalue = VKey;
                 syntax = Hiden b;
                 poly = 0;
                 exported = false;
                 origin = Idtren}
      | _ ->
          if b then failwith
            ("Def. Error: cannot re-use \""^s^"\" as keyword.");
          if is_capsule o then
            failwith ("Def. Error: conflict with the local symbol \""^s^"\".")
    with Not_found ->
      let _ = sym_add s {fkind = key_kind;
			 fvalue = VKey;
			 syntax = Hiden b;
			 poly = 0;
			 exported = false;
			 origin = Idtren} lock in ());
    add_key false lock l
| (IKey s)::l ->
    if List.mem s !illegal_kwd then raise (Failure
        ("Def. Error: cannot use \""^s^"\" as keyword."));
    (try
      let o = sym_get s in
      match get_syntax o with
        Hiden true  -> ()
      | Hiden false ->
          if is_capsule o then
            failwith ("Def. Error: conflict with the local key \""^s^"\".")
          else set_value o
                {fkind = key_kind;
                 fvalue = VKey;
                 syntax = Hiden b;
                 poly = 0;
                 exported = false;
                 origin = Idtren}
      | _ ->
          if b then failwith
            ("Def. Error: cannot re-use \""^s^"\" as keyword.");
          if is_capsule o then
            failwith ("Def. Error: conflict with the local symbol \""^s^"\".")
    with Not_found ->
      let _ = sym_add s {fkind = key_kind;
                 fvalue = VKey;
                 syntax = Hiden b;
                 poly = 0;
                 exported = false;
                 origin = Idtren} lock in ());
    add_key false lock l
| (Arg _)::l -> add_key true lock l
| (Bind (_,coma,semi))::l -> add_key (coma <> Nocoma || semi <> Nosemi) lock l
| (Space _::l) -> add_key b lock l
| [] -> ()

let check_range lr =
  if level_le lr min_level then raise Illegal_prior;
  if level_le (delta' max_level) lr then raise Illegal_prior

let test_arity warn kind sy =
  let nb_args =
    match sy with
      Hiden _ -> raise (Failure "bug0 in test_arity")
    | Prefix (s,_) ->
        List.fold_left (fun n x -> match x with Arg _ -> n + 1 | _ -> n) 0 s
    | Infix (_,_,s,_,_,_) -> 1 +
        List.fold_left (fun n x -> match x with Arg _ -> n + 1 | _ -> n) 0 s
    | _ -> 0
  in
  let rec fn acc t = match norm2 t with
    KArrow(_,k) -> fn (1+acc) k
  | KAtom (_,_) | KBVar _ ->
      if warn && acc > nb_args then begin
	print_string "Warning: less arguments in the syntax that in the type (you will have to use parentheses for the last arguments).";
	print_newline ();
      end;
      acc >= nb_args
  | _ -> true
  in if nb_args > 0 then fn 0 kind else true

let test_infix ll lr sy =
  check_range lr;check_range ll;
  if level_leq lr min_level then raise Illegal_prior;
  let rec f b = function
    (Arg lvl)::l ->  if b then raise (Two_args);
                     check_range lvl; f true l
  | (Key s)::l ->
      (try match get_syntax (sym_get s) with
        Hiden _ -> f false l
      | _ -> if b then raise (Redef s); f false l
      with Not_found -> f false l)
  | (IKey s)::l ->
      (try match get_syntax (sym_get s) with
        Hiden _ -> f false l
      | _ -> if b then raise (Redef s); f false l
      with Not_found -> f false l)
  | (Bind _)::l -> if b then raise (Two_args); f false l
  | (Space _)::l -> f b l
  | [] -> ()
  in f false sy
(*  if level_scmp lr ll & sy <> [] then raise Illegal_prior;
  let la = last_lvl sy in
  if level_scmp lr la then raise Illegal_prior;
  if (level_cmp lr la) & (level_cmp lr ll) then raise Illegal_prior *)


let test_prefix sy =
  let rec f b = function
    (Arg lvl)::l -> if b then raise (Two_args);
                    check_range lvl; f true l
  | (Key s)::l ->
      (try match get_syntax (sym_get s) with
        Hiden _ -> f false l
      | _ -> if b then raise (Redef s); f false l
      with Not_found -> f false l)
  | (IKey s)::l ->
      (try match get_syntax (sym_get s) with
        Hiden _ -> f false l
      | _ -> if b then raise (Redef s); f false l
      with Not_found -> f false l)
  | (Bind _)::l -> if b then raise (Two_args); f false l
  | (Space _)::l -> f b l
  | [] -> ()
  in f false sy

let no_local t =
  let rec f d = function
    EVar p -> p < d
  | EAtom (o,_) -> if is_capsule o then false else true
  | EApp (t,t') -> (f d t) && (f d t')
  | EAbs (_,t,_) -> f (d+1) t
  | Path (path,t) -> f (d + path_count path) t
  | UCst _ | UVar _ -> false
  | _ -> true
  in
  match t with
    Def t -> f 0 t
  | _ -> true

let iso_value (v,k) (v',k') =
  let lst = ref [] in
  let rec f t1 t2 = match norm2 t1, norm2 t2 with
    KVar ptr, KVar ptr' ->
      if
	(ptr == ptr') ||
	(List.exists (fun (x,x') -> x == ptr && x' == ptr') !lst)
      then
	true
      else if
	(List.exists (fun (_,x) -> x == ptr') !lst) ||
        (List.exists (fun (x,_) -> x == ptr) !lst)
      then
	false
      else
        begin
	  lst:=(ptr,ptr')::!lst; true
	end
  | (KAtom (n,ln)), (KAtom (m,lm)) ->
      n == m && forall2 f ln lm
  | (KBVar n), (KBVar m) -> n = m
  | (KArrow (t1,t2)), (KArrow (t1',t2')) -> (f t1 t1') && (f t2 t2')
  | Unknown, Unknown -> true
  | _ -> false
  and g l1 l2 = match l1, l2 with
    [], [] -> true
  | (LApp::l), (LApp::l') -> g l l'
  | (RApp::l), (RApp::l') -> g l l'
  | ((PAbs (_,k))::l), ((PAbs (_,k'))::l') -> f k k' && g l l'
  | _ -> false
  and h e1 e2 = match e1,e2 with
    (EVar n), (EVar m) -> n = m
  | (UCst (n,_)), (UCst (m,_)) -> n = m
  | (Path (path,e)), (Path (path',e')) -> g path path' && h e e'
  | (UVar (n,_) as t1), (UVar (m,_) as t2) ->
      (try h (getuvar n) t2 with Not_found ->
       try h t1 (getuvar m) with Not_found ->
    n = m)
  | (UVar (n,_)), t2 ->
      (try h (getuvar n) t2 with Not_found -> false)
  | t1, (UVar (m,_)) ->
      (try h t1 (getuvar m) with Not_found -> false)
  | (EAtom (o,k)), (EAtom (o',k')) -> (o == o') && (List.for_all2 f k k')
  | (EApp(t1,t2)), (EApp(t1',t2')) ->
      (h t1 t1') && (h t2 t2')
  | (EAbs (_,t,k)), (EAbs (_,t',k')) -> (f k k') && (h t t')
  | (EAbs (_,t,_)), t' ->
      (h t (EApp((lift t'),EVar 0)))
  | t, (EAbs (_,t',_)) ->
      (h (EApp((lift t),EVar 0)) t')
  | _ -> false
  and kn d1 d2 = match d1,d2 with
    Cst, Cst -> true
  | Def _, Cst -> true
  | Cst, Def _ -> true
  | KCst, KCst -> true
  | KDef _, KCst -> true
  | KCst, KDef _ -> true
  | (Def t), (Def t') -> h t t'
  | (KDef k), (KDef k') -> f k k'
  | (Prg t), (Prg t') -> h t t'
  | _ -> false
  in f k k' && kn v v'

let ftheorem_obj = ref dummy_obj
let ftheorem_list_cons_obj = ref dummy_obj
let fclaim_obj = ref dummy_obj

let add_sym name kind value syntax lock exported origin poly =
  let print_end s = if origin = Idtren then
    print_endline s else () in
  if List.mem name !illegal_kwd then
    raise (Failure
	     ("Def. Error: cannot use \""^name^"\" as keyword."));
  if not (no_local value) then
    raise (Failure
	     "Def. Error: Local symbol appearing in this expression.");
  if not (test_arity (origin = Idtren) kind syntax) then
    raise (Failure
	     "Def. Error: too many arguments in the given syntax");
  try
    let lt = ref (0, []) in
    let kind, value, poly =
      match poly with
	Some n -> kind, value, n
      | None ->
	  let kind = generalize_kind lt kind in
	  let value =
	    match value with
	      Def e -> Def (generalize_expr lt e)
	    | Prg e -> Prg (generalize_expr lt e)
	    | _ -> value
	  in
	  kind, value, fst !lt
    in
    let sy = match syntax with
	Prefix (sy,_) -> test_prefix sy;sy
      | Infix (ll,lr,sy,_,_,_) -> test_infix ll lr sy;sy
      | Trivial -> []
      | _ -> raise (Failure "bug in ass_sym") in
    let (value,kind) = ckind_expr_copy (value,kind) in
   let o =
      try let o' = sym_get name in
      match get_syntax o' with
	Free | Hiden false ->
	  set_value o' {fkind = kind; fvalue = value; syntax = syntax;
			poly = poly; exported = exported; origin = origin};o'
      | sy ->
	  let old = Data_base.Object.get_value o' in
	  let v',k' as c = old.fvalue, old.fkind in
	  match value with
	    Def (EApp(EApp(EAtom(o,_),g),p)) when o == !ftheorem_obj -> (
	      match v' with
		Def (EApp(EApp(EAtom(o,_),g'),p')) when o == !ftheorem_obj -> (
		  if not (equal_expr g g') then raise (Redef name);
		  match p',p with
		    (_ , EAtom(o,_)) when o == !fclaim_obj ->
		      print_end "This symbol already exists (ignored).";o'
		  | (EAtom(o,_), _) when o == !fclaim_obj ->
		      print_end "Instanciating a claim with a theorem.";
		      set_value o' {fkind = kind; fvalue = value;
				    poly = poly; syntax = syntax;
				    exported = exported; origin = origin}; o'
		  | _ ->
		      print_end "This symbol already exists (ignored).";o')
	      | _ -> failwith "bug 10 in add_sym")
	  | _ ->

	  match value with
	    Def (EApp(EApp(EAtom(o,_),_),_) as l)
	    when o == !ftheorem_list_cons_obj -> (
	      match v' with
		Def (EApp(EApp(EAtom(o,_),_),_) as l')
		when o == !ftheorem_list_cons_obj -> (
		  let rec thlist_to_list = function
		      EApp(EApp(EAtom(_,_),th),l) -> th::thlist_to_list l
		    | EAtom(_,_) -> []
		    | _ -> assert false
		  in
		  let l0 = thlist_to_list l in
		  let l0' = thlist_to_list l' in
		  let nl = List.fold_right
		      (fun th nl ->
			if List.exists (equal_expr th) l0' then nl else
			EApp(EApp(aobj !ftheorem_list_cons_obj,th),nl))
		      l0 l'
		  in
		  set_value o' {fkind = kind; fvalue = Def nl;
				syntax = syntax;
				poly = old.poly + poly; exported = exported;
				origin = origin}; o')
	      | _ ->  raise (Redef name))
	  | _ ->

          if iso_value c (value,kind) && sy = syntax then
	    match value, v' with
	      (Cst , Cst) | (Cst, Def _) | (Prg _, Prg _) | (Def _, Def _) |
	      (KCst, KCst) | (KCst, KDef _) | (KDef _, KDef _) ->
		print_end "This symbol already exists (ignored).";o'
	    | (Def _, Cst) | (KDef _, KCst) ->
                print_end "Instanciating a constant with a definition.";
                set_value o' {fkind = kind; fvalue = value; syntax = syntax;
			      poly = poly; exported = exported; origin = origin}; o'
	    | _ -> failwith "bug 30 in add_sym"
          else begin
(*            print_expr (aobj(value)); print_string " <> "; print_expr v';
	    print_newline (); *)
            print_kind kind; print_string " <> "; print_kind k';
            print_newline ();
	    raise (Redef name)
	  end
      with Not_found ->
	sym_add name {fkind = kind; fvalue = value; syntax = syntax;
                      poly = poly; exported = exported; origin = origin} lock
    in add_key true lock sy;
    if origin = Idtren then begin
      match value with
	Cst ->
          let pr _ =
            open_hvbox 0;
	    if syntax <> Trivial then print_char '$';
            print_string name; print_space ();
            print_string ":"; print_space ();
            print_kind kind;
            print_newline ()
          in
          print_pipe_and_stdout pr
      | KCst | KDef _ ->
          let pr _ =
            open_hvbox 0;
	    print_string "Sort"; print_space ();
            print_string name; print_space ();
            print_string "defined";
            print_newline ()
          in
          print_pipe_and_stdout pr
      | Def e ->
          let pr sy =
            open_hovbox 0;
	    if syntax <> Trivial then print_char '$';
            print_string name;
            print_string " ="; print_break 1 3;
            print_expr_sy sy e; print_cut ();
            print_string " : ";
            print_kind kind;
            print_newline ()
          in
          print_pipe_and_stdout pr
      | Prg e ->
          let pr sy =
            open_hovbox 0;
	    if syntax <> Trivial then print_char '$';
            print_string name;
            print_string " ="; print_break 1 3;
            print_expr_sy sy e; print_cut ();
            print_string " : ";
            print_kind kind;
            print_newline ()
          in
          print_pipe_and_stdout pr
      | _ -> ()
    end; o

  with
    Illegal_prior ->
      print_endline "Def. Error: Illegal priorities in definition.";
      raise Error
  | Two_args ->
      print_endline "Def. Error: Two following arguments in definition.";
      raise Error
  | Redef s ->
      open_hbox ();
      print_string "Def. Error: Can not redefine symbol \"";
      print_string s; print_string "\"."; print_newline ();
      (match value with Def e -> print_expr e; print_newline ()
                      | Prg e -> print_expr e; print_newline ()  | _ -> ());
      raise Error
  | All_ready_def ->
      open_hbox ();
      print_string "Def. Error: Can not redefine symbol \"";
      print_string name; print_string "\"."; print_newline ();
      raise Error
  | Rec_def ->
      print_endline "Def. Error: Recursive definition are not allowed.";
      raise Error

let rec add_local_key ld b = function
  (Key s)::l ->
    if List.mem s !illegal_kwd then raise (Failure
        ("Def. Error: cannot use \""^s^"\" as keyword."));
    let nld = try
      let o = sym_get s in
      match get_syntax o with
        Hiden true  -> ld
      | Hiden false -> if b then fst (real_local_add ld s
                {fkind = key_kind;
                 fvalue = VKey;
                 syntax = Hiden b;
                 poly = 0;
                 exported = false;
                 origin = Local_def}) else ld
      | _ -> if b then raise (Failure
        ("Def. Error: cannot re-use \""^s^"\" as keyword.")) else ld
    with Not_found ->
       fst (real_local_add ld s {fkind = key_kind;
                 fvalue = VKey;
                 syntax = Hiden b;
                 poly = 0;
                 exported = false;
                 origin = Local_def}) in
    add_local_key nld false l
| (IKey s)::l ->
    if List.mem s !illegal_kwd then raise (Failure
        ("Def. Error: cannot use \""^s^"\" as keyword."));
    let nld = try
      let o = sym_get s in
      match get_syntax o with
        Hiden true  -> ld
      | Hiden false -> if b then fst (real_local_add ld s
                {fkind = key_kind;
                 fvalue = VKey;
                 syntax = Hiden b;
                 poly = 0;
                 exported = false;
                 origin = Local_def}) else ld
      | _ -> if b then raise (Failure
        ("Def. Error: cannot re-use \""^s^"\" as keyword.")) else ld
    with Not_found ->
      fst (real_local_add ld s {fkind = key_kind;
                 fvalue = VKey;
                 syntax = Hiden b;
                 poly = 0;
                 exported = false;
                 origin = Local_def}) in
    add_local_key nld false l
| (Arg _)::l ->
    add_local_key ld true l
| (Space _)::l ->
    add_local_key ld b l
| (Bind (_,coma,semi))::l ->
    add_local_key ld (coma <> Nocoma || semi <> Nosemi) l
| [] -> ld

let add_rlocal ld name kind value syntax =
  if List.mem name !illegal_kwd then raise (Failure
        ("Def. Error: cannot use \""^name^"\" as keyword."));
  try
  if not (test_arity true kind syntax) then raise (Failure
        "Def. Error: too many arguments in the given syntax");
  let sy = match syntax with
    Prefix (sy,_) -> test_prefix sy;sy
  | Infix (ll,lr,sy,_,_,_) -> test_infix ll lr sy;sy
  | Trivial -> []
  | _ -> raise (Failure "bug in ass_sym") in
  let o =
  try let o' = sym_get name in
    match get_syntax o' with
      Hiden false -> {fkind = kind; fvalue = value; syntax = syntax;
                      poly = 0; exported = false; origin = Local_def}
    | _ -> raise (Redef name)
  with Not_found ->
    {fkind = kind; fvalue = value; syntax = syntax;
     poly = 0; exported = false; origin = Local_def}
  in let ld = add_local_key ld true sy in
  begin
    match value with
     Def e ->
        let pr sy =
          open_hovbox 0;
	  if syntax <> Trivial then print_char '$';
          print_string name;
          print_string " ="; print_break 1 3;
          print_expr_sy sy e; print_cut ();
          print_string " : ";
          print_kind kind;
          print_newline ()
        in
        print_pipe_and_stdout pr
    | Prg e ->
        let pr sy =
          open_hovbox 0;
	  if syntax <> Trivial then print_char '$';
          print_string name;
          print_string " ="; print_break 1 3;
          print_expr_sy sy e; print_cut ();
          print_string " : ";
          print_kind kind;
          print_newline ()
        in
        print_pipe_and_stdout pr
    | _ -> failwith "bug in real_local"
  end;
  real_local_add ld name o

  with
    Illegal_prior ->
      print_endline "Def. Error: Illegal priorities in definition.";
      raise Error
  | Two_args ->
      print_endline "Def. Error: Two following arguments in definition.";
      raise Error
  | Redef s ->
      open_hbox ();
      print_string "Def. Error: Can not redefine symbol \"";
      print_string s; print_string "\"."; print_newline ();
      raise Error
  | All_ready_def ->
      open_hbox ();
      print_string "Def. Error: Can not redefine symbol \"";
      print_string name; print_string "\"."; print_newline ();
      raise Error
  | Rec_def ->
      open_hbox ();
      print_endline "Def. Error: Recursive definition are not allowed.";
      raise Error

(* assume same polymorphism ans same type ! *)
let redef_obj sym value exported =
  let o = Data_base.Object.get_value sym in
  if not (no_local value) then (
    print_endline "Def. Error: Local symbol appearing in this expression.";
    raise Error);
  let kind = o.fkind in
  let (value,kind) = ckind_expr_copy (value,kind) in
  set_value sym {fkind = kind; fvalue = value; syntax = o.syntax;
                 poly = o.poly; exported = exported;
                 origin = Idtren}
