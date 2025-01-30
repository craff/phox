(*######################################################*)
(*			data_base.ml			*)
(*######################################################*)

open List
open Format
open Basic

module Myhashtbl : Myhashtbl.Hashtbl with type key = string =
  Myhashtbl.Poly_Hashtbl (struct type key = string end)

(* commentaire dans l'interface *)

(* the String at the beginnig and the Key at the end prevent
   equality to loop ! *)

module Object = struct
  type 'a o_object = {
    mutable name : string;
    mutable link : 'a o_object list;
    mutable back_link : 'a back_link;
    mutable value : 'a;
    mutable locked : bool;
    generation : int;
    key : int
  }

  and ('a,'b) o_extern = {
    extern_name : string;
    mutable extern_link : 'a o_object list;
    mutable extern_ref : int;
    extern_tbl : 'b
  }

  and extern_ref = int

  and 'a back_link =
    Nil
  | Node of 'a o_object * int ref * 'a back_link ref
  | ENode of extern_ref * int ref * 'a back_link ref

  let get_value x = x.value
  let get_name x  = x.name
  (*  let get_link x = x.link*)
  let get_key x = x.key
  let is_locked x = x.locked

  let mk_ext name tbl =
    {extern_ref = -1; extern_link = []; extern_tbl = tbl; extern_name = name}
  let get_ext_tbl e = e.extern_tbl
  let get_ext_name e = e.extern_name

end

module type Data = sig
  type symbol
  type tbl_types
  type renaming
  type obj = symbol Object.o_object
  type extern = (symbol,tbl_types) Object.o_extern

  val sub_obj : symbol -> obj list
  val sp_new : unit -> extern array
  val sp_sub : extern -> obj list
  val sp_del : obj list -> extern -> unit

  val sp_write : out_channel -> unit
  val sp_read : in_channel -> (string * renaming) list
  val recursive : bool ref

end

module type Base = sig
  type symbol
  type tbl_types
  type renaming
  type obj = symbol Object.o_object
  type extern = (symbol,tbl_types) Object.o_extern

  type base
  exception Base_failure of string
  exception All_ready_def
  exception Rec_def

  val dummy_object : symbol -> obj

  val capsule_object : string -> symbol -> int -> obj
  val is_capsule : obj -> bool
  val rename_capsule : obj -> string -> unit -> unit

  val dummy_base : unit -> base

  val load_base : string list -> string -> base * (string * renaming) list
  val new_base :  unit -> base
  val save_base : base -> string -> unit

  val base_get : base -> string -> obj
  val base_rename : obj -> string -> unit
  val base_add : base -> string -> symbol -> bool -> obj
  val base_remove : bool -> base -> obj -> unit
  val update_ext_link : extern -> unit
  val get_table_byname : base -> string -> extern
  val do_ext_table : base -> (extern -> unit) -> unit
  val rec_remove : bool -> base -> obj -> unit
  val ext_remove : extern -> obj list ->  unit
  val set_value : base -> obj -> symbol -> unit
  val get_rlink : (obj -> bool) -> obj -> obj list
  val get_link : obj -> obj list
  val obj_cmp : obj -> obj -> bool
  val do_base : (obj -> unit) -> base -> unit
  val it_base : (obj -> 'a -> 'a) -> 'a -> base -> 'a
  val filter_base : (obj -> bool) -> base -> obj list
  val is_recursive : obj -> bool
end

module Base (Data:Data) = struct
  open Object
  open Data
  type obj = Data.obj
  type extern = Data.extern
  type symbol = Data.symbol
  type renaming = Data.renaming
  type tbl_types = Data.tbl_types

  type base = {
    objs : obj Myhashtbl.t;
    externs : extern array;
    mutable next_key : int
  }

  exception Base_failure of string
  exception All_ready_def
  exception Rec_def

  let dummy_object a = {
    name = "";
    link = [];
    back_link = Nil;
    value = a;
    locked = false;
    generation = 0;
    key = 0
  }

  let capsule_object name value gen = {
    name = name;
    link = [];
    back_link = Nil;
    value = value;
    locked = false;
    generation = - gen - 1;
    key = -gen - 1;
  }

  let is_capsule o =
    o.generation < 0

  let rename_capsule o name =
    if not (is_capsule o) then raise (Base_failure "illegal renaming");
    let oname = o.name in
    let undo () = o.name <- oname in
    o.name <- name;
    undo

  let dummy_base () = {
    objs = Myhashtbl.create 1;
    externs = [||];
    next_key = 0
  }

  let new_key b = let k = b.next_key in b.next_key<-k+1;k

  let load_base path_list base_name =
    let f base_name =
      let ch = open_in_bin base_name in
      let deps = sp_read ch in
      let size = input_binary_int ch in
      let str = really_input_string ch size in
      let base_root,extern = Marshal.from_string str 0 in
      let key = input_binary_int ch in
      close_in ch;
      {objs = base_root; externs = extern; next_key = key}, deps
    in
    let rec g = function
      [] -> raise (Base_failure ("Fail to load base \""^base_name^"\""))
    | (p::l) -> try f (Filename.concat p base_name)
                with Sys_error _ -> g l
    in g (""::path_list)

  let save_base base base_name =
    print_endline ("Saving \"" ^ base_name ^ "\" ... ");
    try
      let ch = open_out_bin base_name in
      sp_write ch;
      let str = Marshal.(to_string (base.objs,base.externs) []) in
      output_binary_int ch (String.length str);
      output_string ch str;
      output_binary_int ch base.next_key;
      close_out ch
    with Sys_error s ->
      raise (Base_failure ("Fail to write base \""^base_name^"\" : "^s))

  let init_ext sp_sub v =
    for i = 0 to Array.length v - 1 do
      v.(i).extern_ref <- i;
      v.(i).extern_link <- sp_sub v.(i)
    done

  let new_base () =
    let rd = Myhashtbl.create 401 in
    let ext = sp_new () in
    init_ext sp_sub ext;
    {objs = rd; externs = ext; next_key = 0}

  let base_get base name =
    Myhashtbl.find base.objs name

  let add_back_link bl o =
    let rec f = function
      Nil -> Node (o, ref 1, ref bl)
    | Node (o1,p,ls)  -> if o == o1 then (p:= !p+1;bl) else f !ls
    | ENode (_,_,ls)  -> f !ls
    in f bl

  let add_back_ext_link bl e =
    let rec f = function
      Nil -> ENode (e, ref 1, ref bl)
    | ENode (e1,p,ls)  -> if e == e1 then (p:= !p+1;bl) else f !ls
    | Node (_,_,ls)  -> f !ls
    in f bl

  let remove_back_link bl o =
    let rec f pr = match !pr with
      Nil ->
        raise (Base_failure "Bug: Can't back_link which should be there")
    | ENode (_,_,ls)  -> f ls
    | Node (o1,p,ls) ->
        if o == o1 then
          if !p = 1 then pr := !ls
          else p := !p-1
        else f ls
    in let pr = ref bl in f pr; !pr

  let remove_back_ext_link bl e =
    let rec f pr = match !pr with
      Nil ->
        raise (Base_failure "Bug: Can't ext_back_link which should be there")
    | Node (_,_,ls)  -> f ls
    | ENode (e1,p,ls) ->
        if e == e1 then
          if !p = 1 then pr := !ls
          else p := !p-1
        else f ls
    in let pr = ref bl in f pr; !pr

  let do_back f g l =
    let rec fn = function
      Nil -> ()
    | Node (o1,_,ls) ->  f o1; fn !ls
    | ENode (e1,_,ls) ->  g e1; fn !ls
    in fn l

  let base_remove force base o =
    if o.locked && not force then
      raise (Base_failure
        ("object "^o.name^" is locked and can not be deleted."));
    if not !Data.recursive && o.back_link <> Nil then
      raise (Base_failure "Can't remove this object which as link onto it");
    List.iter
      (fun ol -> ol.back_link <- remove_back_link ol.back_link o) o.link;
    Myhashtbl.remove base.objs o.name;
    open_hbox ();
    if not force then begin
      print_string "delete ";print_string o.name; print_newline ()
    end

  let get_table_byname b s =
    let v = b.externs in
    let i = ref 0 in
    while !i < Array.length v && v.(!i).extern_name <> s do
      i := !i + 1
    done;
    if !i >= Array.length v then raise Not_found;
    v.(!i)

  let do_ext_table base f =
    Array.iter f base.externs

  let get_rlink filter x =
    let rec fn acc x =
      let l = subtractq x.link acc in
      let acc = unionq acc l in
      List.fold_left fn acc l
    in select filter (fn [] x)

  let get_link x =
    x.link

  let non_recursive l x0 =
    let rec fn ad l =
      List.fold_left (fun r x -> r && (x != x0) &&
	(List.memq x ad || fn (x::ad) x.link)) true l
    in fn [] l

  let is_recursive o =
    not (non_recursive o.link o)

  let set_value _base o v =
    let link = sub_obj v in
    if !Data.recursive || non_recursive link o then (
      o.value <- v;
      List.iter
        (fun ol -> ol.back_link <- remove_back_link ol.back_link o) o.link;
      List.iter
        (fun ol -> ol.back_link <- add_back_link ol.back_link o) link;
      o.link <- link)
    else raise Rec_def

  let update_ext_link e =
    let old_link = e.extern_link in
    let new_link = sp_sub e in
    let diff = subtractq old_link new_link in
    List.iter (fun ol -> ol.back_link <-
               remove_back_ext_link ol.back_link e.extern_ref) diff;
    let diff = subtractq new_link old_link in
    List.iter (fun ol -> ol.back_link <-
               add_back_ext_link ol.back_link e.extern_ref) diff;
    e.extern_link <- new_link

  let ext_remove e lo =
    sp_del lo e;
    update_ext_link e

  let rec_remove force base o =
    let to_do = ref [] in
    let rec fn o =
    if memq o !to_do then () else (
    to_do := o::!to_do;
    if o.back_link <> Nil then
      (do_back
         (fun o' -> fn o')
         (fun e -> ext_remove base.externs.(e) [o])
         o.back_link;
      if not !Data.recursive && o.back_link <> Nil then
        raise (Failure "Bug in rec_remove")
      else base_remove force base o)
    else base_remove force base o) in
    fn o

  let base_rename o s =
    if o.locked then raise (Base_failure "Can't rename a locked object");
    o.name <- s

  let base_add base name v l =
    try
      let o = Myhashtbl.find base.objs name in
      if o.back_link <> Nil then raise All_ready_def;
      let link = sub_obj v in
      if not (non_recursive link o) then (
        print_endline "Def. Error: Recursive definition are illegal !";
        raise All_ready_def);
      print_endline "Warning: Redefinition of a symbol (not in use).";
      o.value <- v; o.locked <- l;
      List.iter
        (fun ol -> ol.back_link <- remove_back_link ol.back_link o) o.link;
      List.iter
        (fun ol -> ol.back_link <- add_back_link ol.back_link o) link;
      o.link <- link;
      o
    with
      Not_found ->
        let link = sub_obj v in
        let gen = List.fold_left
          (fun x y -> (max x y.generation)) (-1) link in
        let o = {
          name = name;
          link = link;
          back_link = Nil;
          value = v;
          locked = l;
          generation = gen + 1;
          key = new_key base} in
        List.iter
          (fun ol -> ol.back_link <- add_back_link ol.back_link o) link;
        Myhashtbl.add base.objs name o;
        o

  let obj_cmp o1 o2 =
    let x = o1.generation and y = o2.generation in
    if x < 0 then
      if y > 0 then true else x < y
    else if y < 0 then false else x > y

  let do_base fn base = Myhashtbl.do_table (fun _ x -> fn x) base.objs

  let it_base fn init base =
    let res = ref init in
    let gn _ x = res := fn x !res in
    Myhashtbl.do_table gn base.objs;
    !res

  let filter_base fn base =
    let gn x l = if fn x then x::l else l in
    it_base gn [] base

end
