(* $State: Exp $ $Date: 2006/02/24 17:01:54 $ $Revision: 1.15 $ *)
(*######################################################*)
(*			print.ml			*)
(*######################################################*)

open Format
open Flags
open Lexer
open List
open Basic
open Local
open Lambda_util
open Typunif
open Data_base
open Types
open Format
open Option

exception Stack

(* printing function *)

let print_to_string f arg =
  let fsave, psave = get_formatter_output_functions()  in
  try
    let ptr = ref "" in
    let flush () = () in
    let pr s p len =
      ptr := !ptr ^ String.sub s p len
    in
    set_formatter_output_functions pr flush;
    f arg;
    print_flush ();
    set_formatter_output_functions fsave psave;
    !ptr
  with
    e ->
      set_formatter_output_functions fsave psave;
      raise e

let in_mmath = ref false
let in_verb = ref false
let tex_local = ref []
let no_syntax = ref false

let farrow_obj = ref dummy_obj

let reset_kind_var, new_kind_var = let counter = ref 0 in
  (fun () -> counter := 0),
  (fun () -> let s = int_to_alpha false !counter in counter:=!counter+1;s)

let ftbl_tex_syntax = ref (symhash_new 1)

let rec print_kind t =
  reset_kind_var ();
  let lt = ref [] in
  let rec f b b' t = match norm t with
      KVar ptr  ->
	begin
	  try print_string (List.assq ptr !lt)
          with Not_found ->
            let name = "?"^new_kind_var () in
            lt := (ptr, name)::!lt;
	    print_string name
	end
    | KAtom (n,[]) ->
	print_string (get_name n)
    | KAtom (n,l) ->
	let name = get_name n in
	(match name, l with
	  "product", [t;t'] ->
	  if b' then (print_string "("; open_hovbox 0) else
            if invisible_parenthesis then print_string "\171";
            f true true t;
            print_string " *";
	    print_break 1 2;
	    f true false t';
            if b' then (close_box (); print_string ")") else
              if invisible_parenthesis then print_string "\187";
	| _ ->
	    print_string name;
	    print_string "["; open_hovbox 0;
	    let rec fn = function
		[] -> close_box (); print_string "]"
	      | k::l ->
		  f false false k;
		  if l <> [] then (print_string ","; print_break 1 2);
		  fn l
	    in fn l)
    | KArrow (t,t') ->
       if b || b' then (print_string "("; open_hovbox 0) else
         if invisible_parenthesis then print_string "\171";
       f true false t;
       print_string " ->"; print_break 1 2; f false false t';
       if b || b' then (close_box (); print_string ")") else
         if invisible_parenthesis then print_string "\187";
    | KBVar n ->
	print_string ("'"^int_to_alpha false n)
    | Unknown ->
	print_string "??"
in open_hovbox 0;f false false t; close_box ()

let _ =
  fprint_kind := print_kind

let free_name s l =
  if s = "_" then s else
  let len = String.length s in
  let i = ref len in
  let j = ref len in
  (try
    while true do
      match  s.[!i-1] with
	'\'' -> decr i; decr j
      | '0'..'9' -> decr i
      | _ -> raise Exit
    done;
    failwith "bug"
  with Exit -> ());
  let sp = if !j < len then String.sub s !j (len - !j) else "" in
  let sd = String.sub s 0 !i in
  let rec g n =
    let s = sd^(string_of_int n)^sp in
    if List.mem s l then g (n + 1) else
    if List.mem_assoc s !tex_local then g (n + 1) else
    if is_local s then g (n + 1) else
    try let _ = sym_get s in g (n + 1) with Not_found -> s
  in
  if List.mem s l then g 0 else
    if List.mem_assoc s !tex_local then g 0 else
  if is_local s then g 0 else
  try let _ = sym_get s in g 0  with Not_found -> s

type isass =
  Noass
| Ass of expr
| IAss of (expr * expr * string)

type parg =
  PArg of (expr * string list) ref * level
| PBind of (string list * isass) ref * int * coma * semi * kind ref
| PKey of string
| PSpace of string * string

let default_name k env =
let rec fn = function
  KAtom (n,_) ->
    String.make 1 (Char.lowercase_ascii (get_name n).[0])
| KArrow (_,k) -> fn k
| _ -> "#"
in free_name (fn k) env

let rec sysaturate e l = match e,l with
  _, [] -> ()
| t, ((Bind _ | Key _ | IKey _ | Space _)::l) -> sysaturate t l
| (UVar (n,_)), l -> sysaturate (getuvar n) l
| (EApp(t,_)), (Arg _::l)-> sysaturate t l
| _ -> raise Not_found


let print_path env path =
let rec fn env = function
  [] -> env
| LApp::ls -> let r = fn env ls in print_string "L"; r
| RApp::ls -> let r = fn env ls in print_string "R"; r
| (PAbs (s,k))::ls -> let nenv = fn env ls in
(*                  let s = free_name s nenv in *)
                  print_string "\\"; print_string s; print_string "\\";
                  s::nenv

in fn env (List.rev path)

let print_sp = ref ([] : (af2_obj * (expr list -> expr)) list)

let apply_tperm p l0 =
  let rec fn p l = match p,l with
    [], l -> l
  | (n::p), (x::l) -> (List.nth l0 n)::fn p l
  | _, _ -> raise Stack
  in match p with
    Idtperm -> l0
  | Perm(p1,_) -> fn p1 l0

let in_tex = ref false

let rec prime_seq = parser
  [< ' ('\''); n = prime_seq >] -> "'"^n
| [< >] -> ""

type tex_state = Non | Alpha | Num | Special | Under

let is_case o =
  let s = get_name o in
  if String.length s <= 5 then false else
  String.sub s 0 5 = "case_"

let do_texify theo var s =
   let buf = Bytes.make 1024 ' ' in
   let cur = ref 0 in
   let store c =
     if !cur >= 1024 then failwith "Identifier too long";
     Bytes.set buf !cur c; incr cur in
   let store_str s =
     for i = 0 to Bytes.length s - 1 do store s.[i] done in
   let to_close = ref 0 in
   let state = ref Non in
   let rec fn = parser
     [< ' ('A'..'Z' | 'a'..'z' as c); str >] ->
       if !state = Special then (store '}');
       if !state <> Alpha then (
         state := Alpha; store_str "\\text{";
         if var then store_str "\\it " else store_str "\\rm ");
       store c;
       fn str
   | [< ' ('_'); str >] ->
       if !state = Special then (store '}');
       if !state = Alpha then (store '}');
       if not theo && !state <> Under then (state:=Under; incr to_close; store_str "_{");
       if theo then (state:=Non; store_str "\\_");
       fn str
   | [< ' ('.' as c); str >] ->
       if !state = Special then (store '}');
       if !state = Alpha then (store '}');
       state := Non;
       for i = 1 to !to_close do store '}' done;
       to_close:=0;
       store c;
       fn str
   | [< ' ('0'..'9' as c); str >] ->
       if !state = Special then (store '}');
       if !state = Alpha then (store '}');
       if !state <> Under && !state <> Num && not theo then (incr to_close; store_str "_{");
       state:=Num;
       store c; fn str
   | [< c = special; str >] ->
       if !state = Alpha then (store '}');
       if !state <> Special then (state:=Special; store_str "\\text{\\tt ");
       (try
         store_str (List.assoc c ['&', "\\&"])
       with Not_found ->
         store c);
       fn str
   | [< prs = prime_seq >] ->
       if !state = Special then (store '}');
       if !state = Alpha then (store '}');
       for i = 1 to !to_close do store '}' done;
       store_str prs;
       String.sub buf 0 !cur
   in
   fn (Stream.of_string s)

let texify theo var s = if not !in_tex then s else do_texify theo var s


let rec get_arg = function
	[] -> []
  | (PArg (p,_))::al -> p::(get_arg al)
  | _::al -> get_arg al

type tex_name = Tex of string | Notex

let get_rsyntax o =
  if !in_tex then
    try
      let name, sy  = assq o !cur_local.local_tex_tbl in
      Tex name, sy
    with
      Not_found ->
    try
      let name, sy, _  = symhash_find !ftbl_tex_syntax o in
      Tex name, sy
    with
      Not_found -> Notex, get_syntax o
  else Notex, get_syntax o

let get_tex_name o = function
  Notex -> get_name o
| Tex s -> s

let rename e =
  let rec fn depth env = function
      EAbs(x,e,t) ->
	let e', vars = fn (depth+1) ((depth,x)::env) e in
	let vars = List.filter (fun (d,x) -> d <> depth) vars in
	let x' = free_name x (List.map snd vars) in
	EAbs(x',e',t), vars
    | EVar n as e ->
	begin try
	  let vars = [List.nth env n] in
	  e, vars
	with
	  Failure _ -> e, []
	end
    | EApp(e1,e2) ->
	let e1', vars1 = fn depth env e1 in
	let e2', vars2 = fn depth env e2 in
	EApp(e1',e2'), unionq vars1 vars2
    | UCst (n,k) as e ->
	let name =
          try
            if !in_tex then fst (List.assoc n !cur_local.local_ctex_tbl) else raise Not_found
          with not_found -> try
            texify false true (expr_local e)
          with Not_found -> ("UCst"^(string_of_int n))
	in e, [-1, name]
    | EAtom(o,_) as e ->
	let tex, sy = get_rsyntax o in
	e, [-1, get_tex_name o tex]
    | UVar(n,_) as e ->
	begin
	  try fn depth env (getuvar n)
	  with Not_found -> e, []
	end
    | e -> e, []
  in
  fst (fn 0 [] e)

let space_string lvl =
  let a = float (!min_tex_space) and
      b = float (!max_tex_space - !min_tex_space) in
  let space = (a +. (b *. lvl /. 10.0)) /. 100.0 in
  (string_of_float space)^"em"

let fkTheorem = ref Unknown

let rec print_aux llvl rlvl stack env =

let lisp_app = !tex_lisp_app || not !in_tex in

let rec
  do_stack f a stack = match stack with
    [] -> f a
  | _::_ ->
      (if lisp_app then
	if level_leq llvl min_level then
	  if !in_mmath && not !in_verb then print_string "\\left("
          else print_string (if !in_tex then "{(}" else "(")
	else
          if !in_mmath && not !in_verb then print_string "\\prettybox{}");
      open_hovbox 0;
       if invisible_parenthesis && not !in_tex then
	 for i = 1 to List.length stack do print_string "\171" done;
      f a; do_item_stack stack;
      close_box ();
      (if lisp_app then
	if level_leq llvl min_level then
	  if !in_mmath && not !in_verb then print_string "\\right)"
	  else print_string (if !in_tex then "{)}" else ")")
	else
          if !in_mmath && not !in_verb then print_string "\\endprettybox{}"
	  else ())

and do_item_stack stack =
    if stack = [] then () else begin
      let spaces = space_string min_level in
      let indent = space_of_int !tex_indent in
      if lisp_app then begin
        if !in_tex then print_string (
	  if !in_mmath then "\\ibreak{"^spaces^"}{"^indent^"}"
	  else "\\hspace{"^spaces^"}");
        print_break 1 2
      end else print_string (
	if !in_mmath && not !in_verb then "\\left(" else "(");
      let rec fn = function
        [i] ->
          if lisp_app then print_aux min_level min_level [] env i
                      else print_aux max_level max_level [] env i;
	  if not !in_tex && invisible_parenthesis then
	    print_string "\187";
      | i::l ->
          (if lisp_app then print_aux min_level min_level [] env i
                       else print_aux max_level max_level [] env i);
          if !in_tex then print_string (
	    if lisp_app then
	      if !in_mmath then "\\ibreak{"^spaces^"}{"^indent^"}"
  	      else "\\hspace{"^spaces^"}"
	    else
	      if !in_mmath then
		",\\ibreak{"^space_of_int !comma_tex_space^"}{"^indent^"}"
	      else ",\\hspace{"^space_of_int !comma_tex_space^"}")
	  else
	    if invisible_parenthesis then print_string "\187";
          print_break 1 2;
          fn l;
      | _ -> failwith "bug in do_item_stack"
      in fn stack;
      if not lisp_app then print_string (
	if !in_mmath && not !in_verb then "\\right)" else ")")
    end

in let rec print_var n =
    try print_string (texify false true (nth_try n env))
    with Not_found -> print_string "#";print_int n


and print_object tex o =
    if tex = Notex then print_string (if !in_tex then "\\$" else "$");
    let theo = equal_kind (get_kind o) !fkTheorem in
    print_string (if tex = Notex then texify theo false (get_name o)
                 else get_tex_name o tex)


and build_prefix stack = function
    [] -> [],stack
  | (Arg lvl)::al -> (match stack with
  	  [] -> raise Stack
	| e::s -> let l,ns = build_prefix s al in
			  ((PArg (ref (e,env),lvl))::l),ns)
  | (Bind (s,co,se))::al -> let l,ns = build_prefix stack al in
                    ((PBind (ref ([],Noass),s,co,se, ref (KBVar(-1))))::l),ns
  | (Key s)::al -> let l,ns = build_prefix stack al in
                    ((PKey s)::l),ns
  | (IKey s)::al -> let l,ns = build_prefix stack al in
                    ((PKey s)::l),ns
  | (Space (spb,spa))::al -> let l,ns = build_prefix stack al in
                    ((PSpace (spb,spa))::l),ns

and build_infix name stack ll al spb spa = match stack with
  	  [] -> raise Stack
	| e::s -> let l,ns = build_prefix s al in
			  ((PArg (ref (e,env),ll))::(PSpace (spb,spa))::
			     (PKey name)::l),ns

and do_bind lr the_binder al =
  let args = get_arg al in
  let rec do_arg co se ps n kr =
    let p = try List.nth args (n - 1) with e when e <> Out_of_memory
      -> failwith "bug nth 5" in
    match !p with
      EAbs(s,e,k),env ->
        let s = if s = "#" then default_name k env else s (*free_name s env*) in
        let e,ass = fn k se e in
        let e,l = gn k co se ass env [s] e in
        ps := (l,ass); p := (e,l@env); kr := k

     | _ -> raise Stack

  and fn k se e =
    try
      if not !tex_type_sugar && !in_tex then raise Not_found;
      match se with
	Nosemi -> raise Not_found;
      | Semi c ->
          look (texpr_copy c) e
    with Not_found -> e, Noass

  and look c e = try
       let n1 = new_uvar () and n2 = new_uvar () in
       let v1 = UVar(n1,mk_Var ()) and v2 = UVar(n2,mk_Var ()) in
       let pat = norm_expr (EApp(EApp(c,EApp(v1,EVar 0)),v2)) in
       let subst = simpl_match (n2-1) pat e in
       let e1 = List.assoc n1 subst in
       (match head e1 with
         (Uneq _ | Alleq | Uveq),_ -> ()
       | Oneq _,o -> match snd (get_rsyntax o) with
           Trivial | Mute | Free -> ()
         | Prefix (sy,perm) -> sysaturate e1 sy
         | Infix (_,_,sy,perm,_,_) -> sysaturate e1 ((Arg min_level)::sy)
         | Hiden _ -> raise (Failure "bug in look"));
         (List.assoc n2 subst), Ass (unlift e1)
       with Not_found | Exit ->
       let n1 = new_uvar () and n2 = new_uvar () and n3 = new_uvar () in
       let v1 = UVar(n1,mk_Var ()) and v2 = UVar(n2,mk_Var ())
       and v3 = UVar(n3,mk_Var ()) in
       let pat = norm_expr (EApp(EApp(c,EApp(EApp(v1,EVar 0),v2)),v3)) in
       let subst = simpl_match (n3-1) pat e in
       let e1 = List.assoc n1 subst in
       match norm_expr e1 with
           (EAtom (o,k)) ->
             let s = match (get_rsyntax o) with
		 tex, Infix (_,lr',sy,_,_,_) ->
		   if level_leq lr lr' then  raise Not_found;
                   let rec test_sy = function
		       (Space _)::l -> test_sy l
		     | [Arg _] -> ()
		     |  _ -> raise Not_found
		   in test_sy sy;
		   get_tex_name o tex
               | _ -> raise Not_found in
	     (try (List.assoc n3 subst), IAss(e1,unlift (List.assoc n2 subst),s)
	     with Exit -> raise Not_found)
       | _ -> raise Not_found

  and gn k0 co se ass env0 env e =

    if !tex_infix_sugar || not !in_tex then match co with
      Nocoma -> e, env
    | Coma f -> try
       let f = texpr_copy f in
       let n1 = new_uvar () in
       let v1 = UVar(n1,mk_Var ()) in
       let pat = norm_expr (EApp(EApp(f, the_binder),v1)) in
       let subst = simpl_match (n1-1) pat e in
       let e = List.assoc n1 subst in
       let e,s = match e with
         EAbs(s,e,k) when equal_kind_no_unif k k0 ->
	     e, s (*free_name s (env0@env)*)

       | _ -> raise Not_found in
       let n1 = new_uvar () in
       let v1 = UVar(n1,mk_Var ()) in
       let pat = match se,ass with
         Nosemi, Noass -> v1
       | Semi c, Noass -> (
	   try let _ = look (texpr_copy c) e in raise Not_found
	   with Not_found -> v1)
       | Semi c, Ass g -> EApp(EApp((texpr_copy c),EApp(
                            mlift (1 + List.length env) g,EVar 0)),v1)
       | Semi c, IAss (o,g,_) ->
                 EApp(EApp((texpr_copy c),EApp(EApp(o,EVar 0),
                            mlift (1 + List.length env) g)),v1)
       | _ , _ -> raise (Failure "bug in do_bind (printer)") in
       let subst = simpl_match (n1-1) pat (norm_expr e) in
       let e = List.assoc n1 subst in
       gn k0 co se ass env0 (s::env) e
     with Not_found | Clash -> e,env
     else e, env

  and f = function
    [] -> ()
  | (PBind (ps,n,co,se,kr))::al ->
      f al;
      do_arg co se ps n kr;
      let (ls,_) = !ps in
      if ls = [] then raise (Failure "bug2 in do_bind (printer)")
  | _::al -> f al

  in f al

and print_vars  = function
  [] -> ()
| [s] ->
    print_string (texify false true s)
| s::l ->
    print_vars l;
    print_string (
      if !in_tex then
      	",\\hspace{"^space_of_int !comma_tex_space^"}"
      else ",");
    print_string (texify false true s)

and print_ass env = function
    Noass -> ()
  | Ass e ->
      print_string (
	if !in_tex then
	  ":\\hspace{"^space_of_int !comma_tex_space^"}"
      	else
	  ":");
      print_aux min_level min_level [] env e;
      print_break 1 2
  | IAss (_,e,s) ->
      print_string " ";
      print_string (
	if !in_tex then
          let c = space_of_int !comma_tex_space in
	  if !in_mmath then
            let i = space_of_int !tex_indent in
	    "\\ibreak{"^c^"}{"^i^"}"^s^"\\ibreak{"^c^"}{"^i^"}"
	  else
	    "\\hspace{"^c^"}"^s^"\\hspace{"^c^"}"
      	else
	  s);
      print_string " ";
      print_aux min_level min_level [] env e;
      print_break 1 2

and size_print s =
  match proof_general, s with
    true,
    (">=" | "<=" | "!=" | "in" | "notin" | "subset" | "inter" | "union"  | "minus"
          | "/\\" | "\\/" | "or" | "<->" | "->" | "=>") ->
	print_as 1 s
  | _ ->
      print_string s

and print_args lr the_head tex b llvl rlvl = function
    [] -> ()
  | PSpace (spb,spa)::al ->
      (if !in_tex then
	if b && spa <> "" && !in_mmath then
          let spa = match al with
	    [PArg ({contents = e,_},lr')] ->
	      if equal_pos_eq (fst (head e)) the_head && level_leq lr lr'
	      then "0em" else spa
          | _ -> spa
          in
	  print_string ("\\ibreak{"^spb^"}{"^spa^"}")
	else if spb <> "0em" then
          print_string ("\\hspace{"^spb^"}"));
      print_args lr the_head tex b llvl rlvl al
  | (PBind ({contents = ls,ass},_,_,_,kr))::al ->
      if b && not !in_tex then print_string " ";
      print_vars ls;
      if !print_sort then begin
	print_string ":<";
	print_kind !kr
      end else begin
	print_ass env ass
      end;
      print_args lr the_head tex true llvl rlvl al
  | [PArg ({contents = e,env},lvl)]->
(*      let spaces = space_string lvl in *)
        if b then print_break 1 2;
        print_aux lvl rlvl [] env e
  | (PArg ({contents = e,env},lvl))::al ->
(*      let spaces = space_string (if not b then lvl else min_level) in *)
        if b then print_break 1 2;
        if not b then print_aux llvl lvl [] env e else
          print_aux max_level max_level [] env e;
	print_args lr the_head tex true llvl rlvl al
  | (PKey s)::al ->
      if b && not !in_tex then print_space ();
      if !in_tex then
	if tex <> Notex then print_string s else
	print_string ("{\\mathop{"^texify false false s^"}}")
      else size_print s;
      let b =
        let rec fn = function
            PBind _::_ -> (
              let last = s.[String.length s - 1] in
                match last with
                    'A'..'Z' | 'a'..'z' | '_' | '0'..'9' -> true
                  | _ -> false)
	  | PSpace _::l -> fn l
          | _ -> true
	in fn al
      in
      print_args lr the_head tex b llvl rlvl al

and print_lam env = function
    EAbs(s,e,k) ->
      let s = (if s = "#" then default_name k env else s (*free_name s env*)) in
	print_string (
	  if !in_tex then
	    if !in_mmath then
	      ",\\ibreak{"^space_of_int !comma_tex_space^"}{"^
	      (space_of_int !tex_indent)^"}"
	    else
	      ",\\hspace{"^space_of_int !comma_tex_space^"}"
	  else ",");
	print_string (texify false true s);
	if !print_sort then begin
	  print_string ":<";
	  print_kind k
	end;
      	print_lam (s::env) e
  | e ->
      print_break 1 2;
      print_aux min_level rlvl [] env e

and print_syntax the_head the_expr the_name tex = function
    Prefix (al0,perm) ->
      if !no_syntax then raise Stack;
      let stack = apply_tperm perm stack in
      let al,ns = build_prefix stack al0 in
      let fn () =
	let lr = last_lvl al0 in
	do_bind lr the_expr al;
	let al = (PKey the_name)::al in
	let l0 = if ns = [] then rlvl else min_level  in
	let b = level_le l0 lr in
	let b' = !in_mmath && not (approx (inf_level l0 llvl) lr) &&
	  not !in_verb in
	let llvl = if b then max_level else llvl in
	let rlvl = if b then max_level else rlvl in
	(if b then
          print_string (if !in_mmath && not !in_verb then "\\left(" else "(")
	else
	  if b' then print_string "\\prettybox{}" else if invisible_parenthesis then print_string "\171");
	if l0 <> lr then open_hovbox 0;
	print_args lr the_head tex false llvl rlvl al;
	if l0 <> lr then close_box ();
	(if b then
          print_string (
	  if !in_mmath && not !in_verb then "\\right)" else ")")
	else
	  if b' then print_string "\\endprettybox{}" else  if invisible_parenthesis then print_string "\187");
      in
      do_stack fn () ns
  | Infix  (ll,lr,al0,perm,spb,spa)  ->
      if !no_syntax then raise Stack;
      let stack = apply_tperm perm stack in
      let al,ns = build_infix the_name stack ll al0 spb spa in
      let fn () =
	do_bind lr the_expr al;
	let l0 = if ns = [] then (inf_level llvl rlvl) else min_level in
	let b = level_le l0 lr in
	let b' = !in_mmath && not (approx l0 lr) && not !in_verb in
	let llvl = if b then max_level else llvl in
	let rlvl = if b then max_level else rlvl in
	(if b then
          print_string (if !in_mmath && not !in_verb then "\\left(" else "(")
	else
	  if b' then print_string "\\prettybox{}" else if invisible_parenthesis then print_string "\171");
	if l0 <> lr then open_hovbox 0;
	print_args lr the_head tex false llvl rlvl al;
	if l0 <> lr then close_box ();
	(if b then
          print_string (
	  if !in_mmath && not !in_verb then "\\right)" else ")")
	else
	  if b' then print_string "\\endprettybox{}" else if invisible_parenthesis then print_string "\187");
      in
      do_stack fn () ns
  | Trivial ->
       if !no_syntax then raise Stack;
     let theo = match the_head with
	Oneq o -> equal_kind (get_kind o) !fkTheorem
      |	 _ -> false
      in
      do_stack print_string
      	((if tex = Notex then texify theo false else fun x -> x) the_name)
       stack
  | Free ->
      if !no_syntax then raise Stack;
      do_stack print_string
      	((if tex = Notex then texify false true else fun x -> x) the_name)
	stack
  | Mute -> (
      if !no_syntax then raise Stack;
      match stack with
	e::l ->
	  print_aux llvl rlvl l env e
      | [] ->
	  failwith "Impossible to print a TeX-Mute symbol with no argument")
  | Hiden _ -> raise (Failure "bug \"Hiden\" in print")

and print_match stack e =
  let e,matched,stack = match stack with
    t1::t2::t3::stack ->
      EApp(EApp(e,t1),t2), Some t3, stack
  | t1::t2::stack ->
      EApp(EApp(e,t1), t2), None, stack
  | _ -> raise Not_found
  in
  let rec fn acc e =
    match e with
      EApp(EApp(EAtom(oc,_),suit),fail)
      when is_case oc ->
	let case_name = get_name oc in
	let ob =
	  sym_get (String.sub case_name 5 (String.length case_name - 5) ) in
	let nb_args =
	  let rec kn acc = function
	      KArrow(_,k) -> kn (acc+1) k
	    | _ -> acc
	  in kn 0 (get_kind ob)
	in
	let c = gn env [] (aobj ob) nb_args (EApp(suit, UCst(-1,mk_Var ())))
	in
	fn (c::acc) fail
    | EAtom(o,_) when get_name o = "undef" ->
	acc
    | e ->
	let s = free_name "_" env in
	let envl = s::env in
	((envl,EVar 0,EApp(lift e,EVar 0))::acc)

  and gn envl acc o n i =
    match acc, n, norm_expr i with
    | [], 0, t when not (occur (-1) t) ->
	(envl,o, t)
    | ((n,o')::acc), 0, t ->
	let o = EApp(o',o) in
	gn envl acc o n t
    | _, _, EAbs(s,t,k) when n > 0 ->
	let s = if s = "#" then default_name k envl else s (*free_name s envl*) in
	let envl = s::envl in
	gn envl (List.map (fun (n,o) -> n, lift o) acc)
		   (EApp(lift o,EVar 0)) (n-1) t
    | _, _, EApp(EApp(EAtom(oc,k),a),fail) when is_case oc ->
	let case_name = get_name oc in
	let ob =
	  sym_get (String.sub case_name 5 (String.length case_name - 5)) in
	let nb_args =
	  let rec kn acc = function
	      KArrow(_,k) -> kn (acc+1) k
	    | _ -> acc
	  in kn 0 (get_kind ob)
	in
	let acc = (n-1,o)::acc in
	gn envl acc (aobj ob) nb_args (EApp(a,fail))
    | _, _, t when n > 0 ->
        gn envl acc o n (EAbs("x",EApp(lift t, EVar 0),mk_Var ()))
    | _ -> raise Not_found
  in
  let cases = fn [] e in
  let do_print_match matched cases =
    if stack <> [] then print_string "(";
    open_hvbox 0;
    begin match matched with
      Some matched ->
	print_string "match";
	open_hovbox 2;
	print_space ();
	print_aux max_level max_level [] env matched;
	close_box ();
	print_space ();
	print_string "with";
    | None ->
	print_string "function"
    end;
    print_break 0 2;
    let rec fn = function
	(envl, lm, rm)::suit ->
	  open_hovbox 2;
	  print_space ();
	  print_aux 5.0 5.0 [] envl lm;
	  print_space ();
	  print_string "->";
	  print_space ();
	  print_aux max_level max_level [] envl rm;
 	  close_box ();
	  if suit <> [] then begin
	    print_space ();
	    print_string "|";
	    fn suit
	  end
      | [] -> ()
    in
    fn cases;
    close_box ();
    if stack <> [] then print_string ")"
  in
  do_stack (do_print_match matched) (List.rev cases) stack

in function
  EVar n -> do_stack print_var n stack
| EData d -> do_stack
                 (fun s -> print_string (Data.string_of_data s))
                 d stack
| FVar s -> do_stack print_string ("?"^s^"?") stack
| UCst (n,k) as e -> (
    try
      if not !in_tex then raise Not_found;
      let name, sy = List.assoc n !cur_local.local_ctex_tbl in
      try
        print_syntax (Uneq n) e name (Tex name) sy
      with
        Stack -> do_stack print_string name stack
    with Not_found ->
      do_stack print_string (
        try texify false true (expr_local e)
        with Not_found -> ("UCst"^(string_of_int n))) stack)

| UVar (n,k) -> (
    try
      print_aux llvl rlvl stack env (getuvar n)
    with Not_found ->
      let name =
	try get_uvar_name n with Not_found -> string_of_int n
      in
      do_stack print_string ("?"^name) stack)
| Path (p,e1) -> print_string "[[";
                let nenv = print_path env p in
                print_string "<--";
                print_aux max_level max_level [] nenv e1;
                print_string "]]"
| Syntax s -> print_string "_a_syntax_"
| EApp (e1,e2) -> print_aux llvl rlvl (e2::stack) env e1
| EAbs _ as e ->
    if stack <> [] then
      print_aux llvl rlvl [] env (norm_sexpr e stack)
    else (
      match eta_red e with
        EAbs (s,e1,k) ->
        let s = if s = "#" then default_name k env else s (*free_name s env*) in
        print_string (if !in_tex then "\\lambda " else "\\");
        print_string (texify false true s);
	if !print_sort then begin
	  print_string ":<";
	  print_kind k
	end;
        print_lam (s::env) e1
      | e' -> print_aux llvl rlvl stack env e')

| EAtom (o,k) as e ->
    try try try
      print_aux llvl rlvl [] env ((List.assq o !print_sp) stack)
    with Not_found when !print_match_case && is_case o ->
      print_match stack e
    with Not_found when stack <> [] && (get_name o = "start_match") ->
      (match stack with
	[] -> assert false
      | e::stack ->
	print_aux llvl rlvl stack env e)
    with Not_found -> let tex, sy = get_rsyntax o in try
      print_syntax (Oneq o) e (get_tex_name o tex) tex sy
    with Stack ->
      do_stack (print_object tex) o stack

let print_aux' llvl rlvl s e t =
  print_aux llvl rlvl s e (rename t)

let print_expr t =
  open_hovbox 0; in_tex := false;
  let save = !trace_pmatch in trace_pmatch := false;
  print_aux' max_level max_level [] [] t; close_box ();
  trace_pmatch := save

let print_expr_sy b t =
  open_hovbox 0; in_tex := false;
  let save = !trace_pmatch in trace_pmatch := false;
  let save' = !no_syntax in no_syntax := b;
  print_aux' max_level max_level [] [] t; close_box ();
  trace_pmatch := save; no_syntax := save'

let print_expr_sorted t =
  open_hovbox 0; in_tex := false;
  let save = !trace_pmatch in trace_pmatch := false;
  let save_sort = !print_sort in print_sort := true;
  print_aux' max_level max_level [] [] t; close_box ();
  trace_pmatch := save; print_sort := save_sort

let print_expr_env env t =
  let env' = List.fold_left (fun l x -> (free_name x l)::l) env [] in
  open_hovbox 0; in_tex := false;
  let save = !trace_pmatch in trace_pmatch := false;
  print_aux' max_level max_level [] env' t; close_box ();
  trace_pmatch := save

let print_expr_tr t =
  open_hovbox 0; in_tex := false;
  let save = !trace_pmatch in trace_pmatch := false;
  print_aux' max_level max_level [] [] t; close_box ();
  trace_pmatch := save

let print_tex_expr t =
  open_hovbox 0; in_tex := true;
  let save = !trace_pmatch in trace_pmatch := false;
  print_aux' max_level max_level [] [] t; close_box ();
  trace_pmatch := save

let print_object o =
  if (get_sym o).syntax <> Trivial then print_char '$';
  print_string (get_name o);
  print_space ()

let _ =
  fprint_expr := fun ctxt e -> print_expr_tr (norm_lexpr ctxt e)

let print_local loc =
  let rec fn (name, e) =
    print_string name; print_space ()
  in
  List.iter fn loc.caps_def

let print_pipe_and_stdout f =
  f false;
  match pipe_exit with None -> () | Some ch ->
    let save = get_formatter_output_functions () in
    set_formatter_out_channel ch;
    print_string "<phox>";
    print_newline ();
    f true;
    print_string "</phox>";
    print_newline ();
    set_formatter_output_functions (fst save) (snd save)

let print_eq = function
    Eq_theo o -> print_object o
  | Eq_axiom (e,_) -> print_expr e
  | Eq_subgoal (e,_) -> print_expr e
