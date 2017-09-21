(* $State: Exp $ $Date: 2004/05/18 15:55:28 $ $Revision: 1.10 $ *)
(*######################################################*)
(*			module.ml			*)
(*######################################################*)

open Format
open Basic
open Data_base.Object
open Types.Base
open Types
open Typunif
open Typing
open Local
open Lambda_util
open Af2_basic
open Print
open Files
open Data_info
open Safe_add
open Flags
open Option

let local_modules = ref []

let concat_module_names s1 s2 =
  if s1 = s2 then s1 else s1 ^ "." ^ s2

let is_claim o =
  match get_value o with
    Def (EApp(EApp(EAtom(o1,k), _), EAtom(p,_))) ->
      (o1 == theorem_obj) && (p == claim_obj)
  | _ -> false

let phi = ref true

let do_export copy =
  let g e = mod_copy copy e in
  let g' k = mod_kind_copy copy k in
  let rec f = function
    Prefix (l,perm) -> Prefix (h l,perm)
  | Infix (lr,ll,l,perm,spb,spa) -> Infix (lr,ll,h l,perm,spb,spa)
  | e -> e
  and h l = List.map (function
    Bind (n,Nocoma,Nosemi) as e -> e
  | Bind (n,Coma e,Nosemi) -> Bind (n,Coma (g e),Nosemi)
  | Bind (n,Nocoma,Semi e) -> Bind (n,Nocoma,Semi (g e))
  | Bind (n,Coma e,Semi e') -> Bind (n,Coma (g e),Semi (g e'))
  | e -> e) l

  in
  (fun sym obj ->
    let nv = match sym.origin with Idtren ->
      (match sym.fvalue with
        Cst | VKey | Fun _ | KCst as e -> e
      | Imp -> failwith "bug in expr_export"
      | KDef k -> KDef (g' k)
      | Prg e -> Prg (g e)
      | Def e -> Def (match e with
          (EApp(EApp(EAtom(o,k),c),EAtom(o',k'))) when
            o == theorem_obj && o' == claim_obj -> g e
        | (EApp(EApp(EAtom(o,k),c),p)) when o == theorem_obj  ->
            let dep = get_rlink is_claim obj in
              let cl = if !phi then EApp(aobj imported_obj, List.fold_left
                (fun l c -> EApp(EApp(aobj theorem_list_cons_obj, aobj c), l))
                (aobj theorem_list_nil_obj)
                dep) else p in
              if !phi then type_strong cl kProof;
              g (EApp(EApp(EAtom(o,k),c),cl))
        | _ -> g e)
      |	AImp o -> failwith "bug: AImp in do_export")
    | _ -> Imp
    in
     {fkind = g' sym.fkind; fvalue = nv;
      syntax = f sym.syntax; poly=sym.poly; exported = sym.exported;
      origin = sym.origin}),
  (fun sy -> f sy)

let copy_external copy copys newtbl ne =
  let g = mod_copy copy in
  let g' k = mod_kind_copy copy k in
  let oe = get_ext_tbl (get_table (get_ext_name ne)) in
    match oe with
      Equations tbl ->
        eqhash_do_table (fun rf l ->
          List.iter (fun (o2,e1,e2,nl,k,sy,eqtl) ->
            List.iter (fun (e3,perm,andpath,dir,nc,exported) ->
              match e3 with
                Eq_theo e0 ->
                  if exported then
                    let nrf = match rf with
                      Oneq o -> Oneq (copy o)
                    | _ -> failwith "bug in export_external" in
                    let no2 = match o2 with
                      Oneq o -> Oneq (copy o)
                    | Alleq -> Alleq
                    | _ -> failwith "bug in export_external" in
                    let ne3 = Eq_theo (copy e0) in
                    add_Equations ne nrf no2 dir (g e1) (g e2) nl
                      ne3 (g' k) andpath sy nc false;
              | _ -> ()) eqtl) l) tbl

    | Rules tbl ->
        symhash_do_table (fun rf l ->
          List.iter (fun (s,(e,e',pat,n,ln,order,exported)) ->
            if exported then
              let cln = match ln with
                Intro_opt (n, Some o) -> Intro_opt (n, Some (copy o))
              | _ -> ln in
              add_Rules ne (copy rf) s (g e) (copy e') (g pat) n cln order false) l) tbl

    | Trivial_Hacks tbl ->
        symhash_do_table (fun rf (n,exported) ->
          if exported then
            add_Trivial_Hacks ne (copy rf) n false) tbl

    | Tex_syntax tbl ->
        symhash_do_table (fun rf (name,sy,exported) ->
          if exported then
            add_Tex_syntax ne (copy rf) name (copys sy) false) tbl

let is_root o = (get_sym o).exported

let write_one savename roots =
  clear_cache ();
  let new_base = new_base () in
  let rec copy_symbol obj =
    try base_get new_base (get_name obj)
    with Not_found ->
      let o = base_add new_base (get_name obj) dummy_sym true in
      let newv = expr_export (get_sym obj) obj in
      Base.set_value new_base o newv;
      o
  and expr_export a = fst (do_export copy_symbol) a
  and copys a = snd (do_export copy_symbol) a
  in
  List.iter (fun s -> let _ = copy_symbol s in ()) roots;
  do_ext_table new_base (copy_external copy_symbol copys new_base);
  save_base new_base savename

let write_all savename =
(*  save_base !the_base (savename^".pho"); *)
  let roots = filter_base (fun _ -> true) !the_base in
  phi := false;
  write_one (savename^".pho") roots;
  let roots = filter_base is_root !the_base in
  phi := true;
  write_one (savename^".phi") roots

let rec do_import copy =
  let g e = mod_copy copy e in
  let g' k = mod_kind_copy copy k in
  let rec f = function
    Prefix (l,perm) -> Prefix (h l,perm)
  | Infix (lr,ll,l,perm,spb,spa) -> Infix (lr,ll,h l,perm,spb,spa)
  | e -> e
  and h l = List.map (function
    Bind (n,Nocoma,Nosemi) as e -> e
  | Bind (n,Coma e,Nosemi) -> Bind (n,Coma (g e),Nosemi)
  | Bind (n,Nocoma,Semi e) -> Bind (n,Nocoma,Semi (g e))
  | Bind (n,Coma e,Semi e') -> Bind (n,Coma (g e),Semi (g e'))
  | e -> e) l

  in
  (fun sym nsy origin ->
    let nv = match sym.fvalue with
      Cst | VKey | Fun _ | KCst as e -> e
    | Imp -> failwith "Inconsistancy in modules (probably two modules importing different version of the same module)."
    | KDef k -> KDef (g' k)
    | Prg e -> Prg (g e)
    | Def e -> Def (g e)
    | AImp o -> failwith "bug: AImp in do_import"
    in
       {fkind = g' sym.fkind; fvalue = nv;
        syntax = f nsy; poly=sym.poly; exported = true;
        origin = origin}),
  (fun sy -> f sy)

and import_external renaming copy copys oe =
    let g = mod_copy copy in
   let g' k = mod_kind_copy copy k in
   let ne = get_table (get_ext_name oe) in
    match (get_ext_tbl oe) with
      Equations tbl ->
        eqhash_do_table (fun rf l ->
          List.iter (fun (o2,e1,e2,nl,k,sy,eqtl) ->
            List.iter (fun (e3,perm,andpath,dir,nc,ex) ->
              match e3 with
                Eq_theo e0 ->
                    let nrf = match rf with
                        Oneq o -> Oneq (copy o)
                      | _ -> failwith "bug in import_external" in
                      let no2 = match o2 with
                        Oneq o -> Oneq (copy o)
                      | Alleq -> Alleq
                      | _ -> failwith "bug in import_external" in
                      let ne3 = Eq_theo (copy e0) in
                      add_Equations ne nrf no2 dir (g e1) (g e2) nl
                        ne3 (g' k) andpath sy nc ex
                | _ -> ()) eqtl) l) tbl

    | Rules tbl ->
        symhash_do_table (fun rf l ->
          List.iter (fun (s,(e,e',pat,n,ln,order,ex)) ->
            let cln = match ln with
              Intro_opt (n, Some o) -> Intro_opt (n, Some (copy o))
            | _ -> ln in
            let ori = (get_sym rf).origin in
            let ns,_,_ = apply_renaming renaming s Trivial ori in
            add_Rules ne (copy rf) ns (g e) (copy e') (g pat) n cln order ex) l) tbl


    | Trivial_Hacks tbl ->
        symhash_do_table (fun rf (n,ex) ->
            add_Trivial_Hacks ne (copy rf) n ex) tbl

    | Tex_syntax tbl ->
        symhash_do_table (fun rf (name,sy,ex) ->
            let oname = get_name rf in
            let ori = (get_sym rf).origin in
            let nname,_,_ = apply_renaming renaming oname Trivial ori in
            let pred, pnew =
              let i = ref 0 in
              let l = min (String.length oname) (String.length nname) in
              while !i < l && oname.[!i] = nname.[!i] do incr i done;
              String.sub oname !i (String.length oname - !i),
              String.sub nname !i (String.length nname - !i)
            in
            let pred = do_texify false false pred in
            let pnew = do_texify false false pnew in
            let lpred = String.length pred in
            let lname = String.length name in
            if lpred <= lname &&
               String.sub name (lname - lpred) lpred = pred then
              let name = String.sub name 0 (lname - lpred) ^ pnew in
              add_Tex_syntax ne (copy rf) name (copys sy) ex
            else
              tex_list := rf::!tex_list) tbl

and cst_list = ref []
and inst_list = ref []
and claim_list = ref []
and tex_list = ref []

and load_intf origin_list renaming intf_name =
  let base =
    if List.mem intf_name !local_modules then
      load_base [] (Filename.concat dirname
        ((concat_module_names root intf_name)^
         (if keep_proof then ".pho" else ".phi")))
    else
      load_base !path_list
	(intf_name^(if keep_proof then ".pho" else ".phi")) in
  let local_module = !tmp_modules in
  let module_def = intf_name,renaming in
  if List.mem module_def origin_list then raise
    (Failure ("Module \""^intf_name^"\" is recursive !"));
  if List.for_all
       (fun (n,r) -> n <> intf_name || not (compare_renaming base r renaming))
       !imported_modules then begin
    if origin_list = [] then begin
      print_string "Loading ";
      print_endline intf_name
    end;
    let origin_list = module_def :: origin_list in
    imported_modules := module_def :: !imported_modules;
    List.iter (function (i,r) ->
      load_intf origin_list (compose renaming r) i) local_module;
    let test_print b o =
      match get_value o with
        Cst | KCst ->
          if b = None then cst_list := o::!cst_list
      | Def (EApp(EApp(EAtom(o'',_),_),prf)) when o'' == theorem_obj ->
          (match prf with
            EAtom(o',_) when o' == claim_obj ->
              if b = None then claim_list := unionq [o] !claim_list
          | _ ->
              claim_list := subtractq !claim_list [o])
      | Def _ | KDef _ -> (
	  match b with
	    None ->
              cst_list := subtractq !cst_list [o]
	  | Some Cst ->
	      if List.memq o !cst_list then
		cst_list := subtractq !cst_list [o]
	      else inst_list := o::!inst_list
	  | _ -> ())
      | _ -> ()
    in
    let rec copy_obj o =
      let name = get_name o and sym = get_sym o in
      match sym.fvalue with
	AImp oo -> oo
      |	VKey -> o
      |	 _ ->
      	let syn = sym.syntax in
      	let nname,nsyn,_ = apply_renaming renaming name syn sym.origin in
      	let origin = renaming in
      	let ores =
	  try
            let oo = sym_get nname in
            if sym.origin <> Idtren then oo
            else begin
	      let oldv = get_value oo in
	      let oldo = sym.origin in
	      sym.origin <- Being_added;
	      let s =
		try
		  expr_import sym nsyn origin
		with e ->
		  sym.origin <- oldo;
		  raise e
	      in
	      sym.origin <- oldo;
              let no =
              	add_sym nname s.fkind s.fvalue s.syntax
		  true s.exported origin (Some s.poly)
              in test_print (Some oldv) no; no
	    end
      	  with Not_found ->
	    let _ = sym_add nname {fkind = Unknown;
			   fvalue = VKey;
			   syntax = Hiden false;
			   poly = 0;
			   exported = false;
			   origin = Idtren} false in
            let s = expr_import sym nsyn origin in
            let no =
	      add_sym nname s.fkind s.fvalue s.syntax
		true s.exported origin (Some s.poly) in
            test_print None no; no
	in
	sym.fvalue <- AImp ores; ores

    and expr_import a = fst (do_import copy_obj) a
    and copys a = snd (do_import copy_obj) a in
    do_base (fun o -> let _ = copy_obj o in ()) base;
    do_ext_table base (import_external renaming copy_obj copys)

  end else begin
    if origin_list = [] then
      print_endline ("Module \""^intf_name^"\" all ready loaded !")
  end

and compare_renaming base r1 r2 =
  try
    do_base (fun o ->
      let name = get_name o and sym = get_sym o in
      let syn = Trivial in
      let n1,_,_ = apply_renaming r1 name syn sym.origin in
      let n2,_,_ = apply_renaming r2 name syn sym.origin in
      if n1 <> n2 then raise Exit) base;
    true
  with Exit -> false

and apply_renaming renaming n s origin =
  match renaming with
    Idtren -> n,s,origin
  | Kernel -> failwith "bug in apply renaming"
  | Imported (mo,r) ->
      let n,s,origin = apply_renaming r n s origin in
      n,s, compose (Imported (mo,Idtren)) origin
  | Used (rstr,r) -> (
      let n,s,origin = apply_renaming r n s origin in
      match origin with
        Kernel -> n, s, origin
      | Imported (mo,r0) -> (
          try
            let r = List.assoc mo rstr.from in
            apply_renaming r n s r0
          with Not_found -> n, s, origin)
      | _ ->
          try
            let nn,ns = List.assoc n rstr.rlocal in
            let n,s = if nn = "" && ns = Trivial then n,s else nn, ns in
            n,s,Used (rstr,origin)
          with Not_found ->
          let lookfordot s =
            let i = ref 0 in
            let l = String.length s in
            let finddot () =
              while !i < l && s.[!i] <> '.' do
                incr i
              done;
              if !i >= l then raise Not_found
            in
            let rec fn () =
              finddot ();
              let pre, suf =
                String.sub s 0 !i, String.sub s (!i + 1) (l - !i - 1) in
              try
                let nsuf = List.assoc suf rstr.general in
                pre, nsuf
              with Not_found -> incr i; fn ()
            in fn ()
          in
          try
            let pre, nsuf = lookfordot n in
            (if nsuf <> "" then pre^"."^nsuf else pre),s,Used (rstr,origin)
          with Not_found ->
          n^rstr.default,s,Used (rstr,origin))
  | _ -> failwith "bug in apply_renaming"

and compose r r' =
  if r' = Idtren || r' = Kernel then r else
  match r with
    Idtren -> r'
  | Kernel -> failwith "bug in compose"
  | Imported (s,r'') -> (
      match compose r'' r' with
        Imported _ as r0 -> r0
      | r0 -> Imported (s,r0))
  | Used (rstr,r'') -> (
      match compose r'' r' with
        Imported (s,r1) as r0 -> (
          try compose (List.assoc s rstr.from) r1
          with Not_found -> r0)
      | r0 -> Used (rstr,r0))
  | _ -> failwith "bug in compose_renaming"

let do_load_intf b l o n =
  cst_list := [];
  inst_list := [];
  claim_list := [];
  tex_list := [];
  load_intf l o n ;
  let error = b &&
    (!cst_list <> [] || !inst_list <> [] || !claim_list <> []) in
  if !cst_list <> [] then begin
    open_hovbox 2;
    print_string "*** adding constants: ";
    List.iter print_object !cst_list;
    close_box ();
    cst_list := [];
    print_newline ()
  end;
  if !inst_list <> [] then begin
    open_hovbox 2;
    print_string "*** constants instanciated by definition: ";
    List.iter print_object !inst_list;
    close_box ();
    inst_list := [];
    print_newline ()
  end;
  if !claim_list <> [] then begin
    open_hovbox 2;
    print_string "*** adding axioms: ";
    List.iter print_object !claim_list;
    close_box ();
    claim_list := [];
    print_newline ()
  end;
  if !tex_list <> [] then begin
    open_hovbox 2;
    print_string "*** lost tex syntax: ";
    List.iter print_object !tex_list;
    close_box ();
    claim_list := [];
    print_newline ()
  end;
  if error then raise (
    Gen_error "This module extend the theory and you used -n option!")

let import_intf intf_name =
  do_load_intf false [] (Imported (intf_name, Idtren)) intf_name

let use_intf no_extend intf_name ren =
  do_load_intf no_extend [] ren intf_name

let pervasives = ["prop"]

let load_pervasives () =
  try
    if not init && (!compiling || base_name = "")
      then List.iter import_intf pervasives
  with
    Base_failure s ->
                   open_hbox ();
                   print_string "Error: ";
                   print_string s;print_newline ();
                   raise Error

let reset_base () =
  imported_modules := [];
  reset_tables !the_base;
  do_base (function o -> if (get_sym o).origin <> Kernel then
                   rec_remove true !the_base o)
    !the_base
