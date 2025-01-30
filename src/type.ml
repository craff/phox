(*######################################################*)
(*			type.ml				*)
(*######################################################*)


open Format
open Basic
open Data_base
open Object
open Data

(* the basic object manipuled *)

(* the kind of an object *)

(* les sortes (kind) elles memes *)
type kind =
  KArrow of kind * kind     (* arrow *)
| KAtom of symbol o_object * kind list  (* constante de type *)
| KVar of kind ref          (* variable polymorphe *)
| KBVar of int              (* variable liee par un Let, indice de B. *)
| Unknown

(* syntax of symbol *)

and syntax =
  Trivial | Hiden of bool
| Prefix of argkind list * permutation
| Infix of level * level * argkind list * permutation * string * string
| Mute | Free

and permutation =
  Idtperm
| Perm of int list * int list

and level = float

and coma =
  Nocoma
| Coma of expr

and semi =
  Nosemi
| Semi of expr

and argkind =
	Bind of int * coma * semi
|	Arg of level
|	Key of string
|       IKey of string
|       Space of string * string

and assoc = Non_assoc | Left_assoc | Right_assoc

(* Terme du lambda-calcul simplement type *)

and expr =
  EVar of int
                   (* variable liee, indice de Bruijn *)
| FVar of string
                   (* variable libre, disparait apres le parsing *)
| EAtom of symbol o_object * kind list
		   (* reference a la base de donnee (constante ou définition)
		      la "kind list" contient les valeurs
		      des types polymorphes *)
| EApp of expr * expr
	           (* application *)
| EAbs of string * expr * kind
		   (* abstraction, string used for printing only *)
| UCst of int * kind
		   (* constante pour l'unification *)
| UVar of int * kind
		   (* variable pour l'unification *)
| Path of path list * expr
		   (* chemin dans les termes + expression *)
                   (* ceci est un lieur !, on lui donne pourtant
                      le type de l'expression *)
| Syntax of syntax
      (* syntax, pour des raisons étranges à besoin d'être une expression *)
| EData of data
      (* pour avoir des vrais entier, string etc dans les expressions *)


and path =
  LApp
| RApp
| PAbs of string * kind

(* Termes + informations stockes dans la base de donnees *)

and sym_value =
  Cst                   (* une constante *)
| Def of expr           (* objet definit *)
| Prg of expr		(* un programme *)
| Fun of int		(* un programme primitif *)
| KCst                  (* une constante de sorte *)
| KDef of kind          (* une sorte définies *)
(* cas particulier *)
| VKey                  (* un mot clef *)
| Imp                   (* imported (only in interface file) *)
| AImp of symbol o_object

and symbol = {
  fkind : kind;         (* type simple + expr reguliere *)
  mutable fvalue : sym_value;   (* valeur ... *)
                        (* mutability only used for importing *)
  syntax : syntax;      (* la syntaxe: comment parser et afficher *)
  poly : int;          (* le type est-il polymorphe, nombre d'arguments *)
  exported : bool;      (* l'objet doit-il etre exporte *)
  mutable origin : renaming       (* origine ... *)
}

and renaming =
  Imported of string * renaming
| Used of renstruct * renaming
| Idtren
| Kernel
| Local_hyp
| Local_def
| Being_added

and renstruct = {
  default : string;
  rlocal : (string * (string * syntax)) list;
  general : (string * string) list;
  from : (string * renaming) list
}

(* About equations *)

type eq_type =
  Eq_theo of symbol o_object
| Eq_axiom of expr * int
| Eq_subgoal of expr * int

type eq_perm = int list

type pos_eq =
  Alleq
| Uveq
| Oneq of symbol o_object
| Uneq of int

type eqpath = Left_and | Right_and | Open_def

type eqns = (pos_eq * expr * expr * int * kind * bool *
               (eq_type * eq_perm * eqpath list * bool * int * bool) list) list

(* The type pos_eq gives the different possibilities for the head of
   an expr : An object in the context, a constant (UCst) or a variable
   (UVar). The hashtbl of a rewrite rules uses the pos_eq of the
   left term in the equation as an hash-key.
     - 1st arg in eqns : the pos_eq of the right term
     - 2nd arg : left term (form \lambda x1 ... \lambda xn t)
     - 3rd arg : right term (form \lambda x1 ... \lambda xn t)
     - 4th arg : kind of the term (gives the number of lambdas)
     - 5th arg : is the equation symetric
     - 6th arg : List of theorem and hypothesis
           1: what theorem or hypothesis
           2: the permutation
           3: conjunction list
           4: direction
           5: conditionnal
           6: exported *)

exception Error
exception Gen_error of string

(* the function getting the [symbol object] used in an object of type
   [expr] or [sym_value] *)

(* Hashtbl with pos_eq as key *)

let eqhash_hash = function
  Alleq -> 137
| Uveq -> 211
| Uneq n -> abs (n * 401)
| Oneq o -> get_key o * 65559

let eqhash_equal a1 a2 = match a1,a2 with
  Alleq, Alleq -> true
| Uveq, Uveq -> true
| (Uneq n), (Uneq p) -> n = p
| (Oneq o), (Oneq o') -> o == o'
| _ -> false

module Key_eqhash = struct
  type key = pos_eq

  let hash = eqhash_hash
  let eq = eqhash_equal
end

module Eqhashtbl = Myhashtbl.Hashtbl (Key_eqhash)

type 'a eqhash = 'a Eqhashtbl.t

let eqhash_new = Eqhashtbl.create
let eqhash_clear = Eqhashtbl.clear
let eqhash_add = Eqhashtbl.add
let eqhash_remove = Eqhashtbl.remove
let eqhash_find = Eqhashtbl.find
let eqhash_do_table = Eqhashtbl.do_table
let eqhash_it_table = Eqhashtbl.it_table

(* Hashtbl with symbol_object as key *)

module Sym_eqhash = struct
  type key = symbol o_object

  let hash = get_key
  let eq = (==)
end

module Symhashtbl = Myhashtbl.Hashtbl (Sym_eqhash)

type 'a symhash = 'a Symhashtbl.t

let symhash_new = Symhashtbl.create
let symhash_clear = Symhashtbl.clear
let symhash_add = Symhashtbl.add
let symhash_remove = Symhashtbl.remove
let symhash_find = Symhashtbl.find
let symhash_do_table = Symhashtbl.do_table
let symhash_it_table = Symhashtbl.it_table

type rule_option =
  Intro_opt of int * symbol o_object option
| Elim_opt of int list

(* Type clause généralisée *)
(* should stay here *)
type weight = float

type clause =
    {
      (* first bool : true = negative literal *)
      (* second bool : true = rigid literal *)
      literals : (expr * bool * bool) list;
      weight : weight;
    }

type hint =
    Literal_hint of int
  | Or_hint of hint * hint
  | And_hint of hint * hint

type tbl_types =
    (* Equations pour rewrite. DO NOT CHNAGE THIS ONE *)
| Equations of eqns eqhash

    (* Regle d'introduction et d'elimination *)
| Rules of (string *
	      (expr * symbol o_object * expr * int * rule_option * float * bool)) list symhash

    (* Auto_elim et elim_after_intro : optimisations de trivial *)
| Trivial_Hacks of (int * bool) symhash

| Tex_syntax of (string * syntax * bool) symhash


let mk_Var () = KVar (ref Unknown)

let make_args n =
  let rec fn acc = function
      0 -> acc
    | n -> fn (mk_Var ()::acc) (n-1)
  in fn [] n

let aobj o =
  let v = Data_base.Object.get_value o in
    EAtom (o, make_args v.poly)

let rec sub_expr = function
    EVar _ -> []
  | EAtom (o,kl) -> List.fold_left (fun l k -> unionq l (sub_kind k)) [o] kl
  | EApp (e1,e2) -> unionq (sub_expr e1) (sub_expr e2)
  | EAbs (_,e,k) -> unionq (sub_expr e) (sub_kind k)
  | Path(_,e) -> sub_expr e
  | _ -> []

and sub_kind  = function
  KArrow(k1,k2) -> unionq (sub_kind k1) (sub_kind k2)
| KAtom(o, kl) -> List.fold_left (fun l k -> unionq l (sub_kind k)) [o] kl
| KVar ptr -> sub_kind !ptr
| _  -> []

and sub_sym a =
  let l0 = match a.fvalue with
    Def e -> sub_expr e
  | Prg e -> sub_expr e
  | _ -> [] in
  let l1 = unionq l0 (sub_kind a.fkind) in
  let rec g l0 = function
    [] -> l0
  | (Bind (_,c,s))::l' -> h (g l0 l') c s
  | _::l' -> g l0 l'
  and h l c s =
    let l1 = match c with
      Nocoma -> []
    | Coma e -> sub_expr e in
    let l2 = match s with
      Nosemi -> []
    | Semi e -> sub_expr e in
    unionq (unionq l1 l2) l
  in match a.syntax with
    Trivial | Hiden _ | Mute | Free -> l1
  | Prefix (l,_) -> g l1 l
  | Infix (_,_,l,_,_,_) -> g l1 l


let get_Equations = function
    Equations l -> l
  | _ -> raise (Failure "bug in get_special1")

let get_Rules = function
    Rules l -> l
  | _ -> raise (Failure "bug in get_special3")

let get_Trivial_Hacks = function
    Trivial_Hacks l -> l
  | _ -> raise (Failure "bug in get_special4")

let get_Tex_syntax = function
    Tex_syntax l -> l
  | _ -> raise (Failure "bug in get_special5")


let sp_sub e = match get_ext_tbl e with
    Equations tbl -> eqhash_it_table (fun lp _ l ->
                    List.fold_left (fun lp (_,_,_,_,_,_,eqtl) ->
                      List.fold_left (fun lp (eqt,_,_,_,_,_) ->
                        match eqt with Eq_theo o -> unionq [o] lp
                                     | _ -> lp) lp eqtl) lp l) [] tbl
  | Rules tbl -> symhash_it_table (fun lp _ l ->
                    List.fold_left (fun lp (_,(_,o,_,_,_,_,_)) ->
                      unionq [o] lp) lp l) [] tbl
  | Trivial_Hacks tbl -> symhash_it_table (fun l k _ ->
                      unionq [k] l) [] tbl
  | Tex_syntax tbl -> symhash_it_table (fun l k _ ->
                      unionq [k] l) [] tbl

(* suppression dans l'object spécial "o" de toutes références directes a un
    object presents dans link *)

let sp_del link e =
  let name = get_ext_name e in
  let pr = function o' ->
    open_hbox ();
    print_string "delete ";
    print_string (get_name o');
    print_string " from ";
    print_string name;
    print_string ".";
    print_newline ()
  in
  let found = ref false in
  match get_ext_tbl e with
    Equations tbl ->
      let tr = function Eq_theo o -> [o]
        | _ -> raise (Failure "bug in special del") in
      eqhash_do_table (
	fun k l ->
	  if List.exists (
	    fun (_,_,_,_,_,_,eqtl) ->
	      List.exists (
		fun (eqt,_,_,_,_,_) ->
		  let ldel = interq (tr eqt) link in
		  List.iter pr ldel; ldel <> []) eqtl) l
          then
	    let newl =
	      found := true;
              List.fold_right (
		fun (pos,e1,e2,nl,k,sy,eqtl) l ->
		  let neqtl = select (
		    fun (eqt,_,_,_,_,_) ->
		      interq (tr eqt) link = []) eqtl in
		  if neqtl <> [] then (pos,e1,e2,nl,k,sy,neqtl)::l
                  else l) l []
            in eqhash_remove tbl k;
            if newl <> [] then eqhash_add tbl k newl) tbl;
      if not !found then raise Not_found
  | Rules tbl -> symhash_do_table (
      fun k l ->
	if List.exists (
	  fun (_,(_,o,_,_,_,_,_)) ->
	    let ldel = interq [o] link in
      	    List.iter pr ldel; ldel <> []) l
        then
	  let newl =
            found := true;
	    select (fun (_,(_,o,_,_,_,_,_)) ->
		      interq [o] link = []) l
          in symhash_remove tbl k;
          if newl <> [] then symhash_add tbl k newl) tbl;
      if not !found then raise Not_found
  | Trivial_Hacks tbl -> List.iter (function o -> pr o;
                           symhash_remove tbl o) link
  | Tex_syntax tbl -> List.iter (function o -> pr o;
                           symhash_remove tbl o) link

let sp_new () = [|
  mk_ext "equation" (Equations (eqhash_new 23)); 		(* 0 *)
  mk_ext "intro" ( Rules (symhash_new 23));			(* 1 *)
  mk_ext "elim" ( Rules (symhash_new 23));			(* 2 *)
  mk_ext "elim_after_intro" ( Trivial_Hacks (symhash_new 23));	(* 3 *)
  mk_ext "closed" ( Trivial_Hacks (symhash_new 23));		(* 4 *)
  mk_ext "tex" ( Tex_syntax (symhash_new 23))		        (* 5 *)
|]

let reset_table = function
  Equations tbl -> eqhash_clear tbl
| Rules tbl -> symhash_clear tbl
| Trivial_Hacks tbl -> symhash_clear tbl
| Tex_syntax tbl -> symhash_clear tbl

type af2_obj = symbol o_object
type ext = (symbol,tbl_types) o_extern

let imported_modules = ref ([] : (string * renaming) list)

let sp_write ch =
  let str = Marshal.to_string !imported_modules [] in
  output_binary_int ch (String.length str);
  output_string ch str

let sp_read ch =
  let size = input_binary_int ch in
  let str = really_input_string ch size  in
  (Marshal.from_string str 0 : (string * renaming) list)

module Symbol = struct
  type stmp = symbol
  type symbol = stmp
  type obj = af2_obj
  type ttmp = tbl_types
  type tbl_types = ttmp
  type extern = ext
  type nonrec renaming = renaming

  let sub_obj = sub_sym
  let sp_del = sp_del
  let sp_sub = sp_sub
  let sp_new = sp_new

  let sp_write = sp_write
  let sp_read = sp_read

  let recursive = ref false
end

let recursive = Symbol.recursive

module Base = Base (Symbol)

open Base

let reset_tables base =
  do_ext_table base (
    function tx ->
      reset_table (get_ext_tbl tx);
      update_ext_link tx)

(* function to manipulate [level] *)

let level_leq lv lv' =
  lv <= lv'

let level_le lv lv' =
  lv < lv'

let level_cmp = compare

let delta l =
  l -. 1e-10

let delta' l =
  l +. 5e-11
let idelta' l =
  l -. 5e-11
let approx l l' =
   abs_float (l -. l') <= 2e-10

let min_level = 0.0 and max_level = 10.0

let inf_level l1 l2 = if level_le l1 l2 then l1 else l2

let print_level l = print_float l
let level_to_string l = string_of_float l

let dummy_sym = {
             fkind = Unknown;
             fvalue = Cst;
             syntax = Trivial;
             poly = 0;
             exported = false;
             origin = Idtren}

let dummy_obj = dummy_object dummy_sym

let rec path_count = function
  [] -> 0
| PAbs _::l -> 1 + path_count l
| _::l -> path_count l


(* real local definition *)
type local_defs = {
    cst_def : (string * expr) list;
    caps_def : (string * obj) list;
    local_ctex_tbl : (int * (string * syntax)) list;
    local_tex_tbl : (obj * (string * syntax)) list;
    local_close_tbl : obj list;
    cst_eq : (int * (expr * (int * expr * expr * bool * bool) list)) list
}

let empty_local =  {
  cst_def = [];
  caps_def = [];
  local_ctex_tbl = [];
  local_tex_tbl = [];
  local_close_tbl = [];
  cst_eq = []
}

let cur_local = ref empty_local

let the_base = ref (dummy_base () : base)
let get_name = get_name
let sym_get s =
  try List.assoc s !cur_local.caps_def
  with Not_found -> base_get !the_base s
let sym_add s l = base_add !the_base s l
let sym_del s = base_remove false !the_base s
let sym_rename o s = base_rename o s
let sym_rename_undoable o s = rename_capsule o s
let set_value o v = set_value !the_base o v
let get_table s = get_table_byname !the_base s
let get_sym o = get_value o
let is_poly o = (get_value o).poly
let get_syntax o = (get_value o).syntax


let fprint_expr = ref (fun _ -> failwith "print_expr not ready")
let fprint_kind = ref (fun _ -> failwith "print_kind not ready")
