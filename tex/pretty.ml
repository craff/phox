(* $State: Exp $ $Date: 2004/11/22 13:38:04 $ $Revision: 1.4 $ *)

open Genlex


type pretty_tree =
    Box of break array * pretty_tree list
      * (bool list,(float*float)) Hashtbl.t
  | VBox of pretty_tree list
  | Atom of size
  | IBreak of size * size * bool ref
  | LBreak of int * size * size

and break = {
    name : string;
    state : bool ref }

and size = float

let fabs x = if x > 0.0 then x else -. x

let undo_list = ref []

let set p = undo_list := p::!undo_list; p:= true

let save () = !undo_list

let restore l =
  while !undo_list != l do
    match !undo_list with
      [] -> failwith "bug in restore"
    | p::l' -> undo_list := l'; p:= false
  done

let restore_keep l =
  let keep = ref [] in
  while !undo_list != l do
    match !undo_list with
      [] -> failwith "bug in restore"
    | p::l' -> undo_list := l'; p:= false; keep := p::!keep
  done;
  !keep

let redo keep =
  List.iter (function p -> set p) keep

let look_for_name name lb =
  let ret = ref (-1) in
  try
    for i = 0 to Array.length lb - 1 do
      if lb.(i).name = name then (ret := i; raise Exit)
    done;
    failwith (name ^ " not found")
  with Exit -> !ret


let rec read_tree lb = parser
    [<'Ident ("open" | "iopen");
      lb = (fun strm -> Array.of_list (read_break_list strm));
      lt = read_tree_list lb;
      'Ident ("close" | "iclose") >] -> Box(lb,lt,Hashtbl.create 23)
  | [<'Ident "max";
      lt = read_tree_list lb;
      'Ident "endmax" >] -> VBox lt
  | [<'Ident "atom";
      'Kwd":";
      'Float width;
      'Ident "pt" >] -> Atom width
  | [<'Ident "imbreak";
      'Kwd":";
      'Float hwidth;
      'Ident "pt";
      'Kwd",";
      'Float twidth;
      'Ident "pt" >] -> IBreak(hwidth,twidth,ref false)
  | [<'Ident "break";
      'Kwd":";
      'Ident name;
      'Kwd",";
      'Float hwidth;
      'Ident "pt";
      'Kwd",";
      'Float twidth;
      'Ident "pt" >] -> LBreak(look_for_name name lb,hwidth,twidth)

and read_tree_list lb = parser
    [< t = read_tree lb; lt = read_tree_list lb >] -> t::lt
  | [< >] -> []

and read_break_list = parser
    [<'Ident "newbreak";
      'Kwd ":";
      'Ident name;
      lb = read_break_list >] ->
      	{name = name; state = ref false}::lb
  | [<>] -> []

let rec format_failed = function
    Box(lb, lt, _) ->
      Array.iter (function b -> b.state:=true) lb;
      format_failed_aux 0.0 0.0 lt
  | VBox(lt) ->
      List.fold_left (fun m t ->
	let m' = format_failed t in
        max m m') 0.0 lt
  | Atom(size) -> size
  | _ -> failwith "Illegal break"


and  format_failed_aux maxi prev = function
    IBreak(hw,tw,ptr)::suit ->
      if tw < prev+.hw then begin
        ptr := true;
        let maxi = max prev maxi in
        format_failed_aux maxi tw suit
      end else begin
        let maxi = max prev maxi in
        format_failed_aux maxi (prev +. hw) suit
      end
  | Atom(size)::suit ->
        format_failed_aux maxi (prev+.size) suit
  | t::suit ->
      let m = format_failed t in
      format_failed_aux maxi (prev+.m) suit
  | [] -> max prev maxi

let rec compute_size enc lb = function
    Box(lb,lt,memo) ->
      let l = List.map (fun p -> !p) enc in
      (try
	Hashtbl.find memo l
      with Not_found ->
        let r = compute_size_list enc lb 0.0 0.0 0.0 lt in
        Hashtbl.add memo l r; r)
  | VBox(lt) ->
      List.fold_left (fun (mi,ma) t ->
	let (mi',ma') = compute_size enc lb t in
        max mi mi', max ma ma') (0.0, 0.0) lt
  | Atom(size) -> size, size
  | _ -> failwith "Illegal break"

and compute_size_list enc lb best prev aprev = function
    [] -> max best prev, aprev
  | IBreak(hw,tw,ptr)::suit ->
      if tw < prev+.hw then
        compute_size_list enc lb (max best prev) tw (aprev +. hw) suit
      else
        compute_size_list enc lb best (prev +. hw) (aprev +. hw) suit
  | LBreak(i,hw,tw)::suit ->
      let {state = ptr} = lb.(i) in
      if (if List.memq ptr enc then !ptr else tw < prev+.hw) then
        compute_size_list enc lb (max best prev) tw (aprev +. hw) suit
      else
        compute_size_list enc lb best (prev +. hw) (aprev +. hw) suit
  |  x::suit ->
      let mi, ma = compute_size enc lb x in
      compute_size_list enc lb best (prev +. mi) (aprev +. ma) suit

let output_file chout t =
  let rec fn = function
      Box(lb,lt,_) ->
        let bt =
          try
            Array.iter (fun b -> if !(b.state) then raise Exit) lb;
            let rec gn = function
              IBreak(_,_,ptr) when !ptr ->  raise Exit
            | _ -> () in
            List.iter gn lt;
            false
          with Exit -> true in
	output_string chout (if bt then "\\iftrue\n" else "\\iffalse\n");
      	Array.iter (fun b ->
	  output_string chout (if !(b.state) then "\\iftrue\n"
                                             else "\\iffalse\n")) lb;
        List.iter fn lt
    | VBox(lt) ->
	List.iter fn lt
    | IBreak(_,_,ptr) ->
	  output_string chout (if !ptr then "\\iftrue\n" else "\\iffalse\n");
    | _ -> ()
  in fn t

exception Fail_format of bool

let comp s (b,s',cn,n') =  let s'' = s +. s' in max b s'',s'', cn, n'
let compr s (b,s',cn,n') =  let s'' = s +. s' in max b s'',0.0, 0,n'+cn+1
let compf (s,n) (s',n') =  s +. s', n +. n'

let xCoef = 1.33
let dCoef = 5.0
let eCoef = 5.0

(*
  width: largeur totale
*)
let rec format_tree width bp = function
    Box(lb,lt,_) ->
      (try
        let b,p,cn,n =
          format_tree_list width width [] bp bp lb lt in max b p, cn + n
      with Fail_format _ -> raise (Fail_format true))
  | VBox(lt) ->
      (try List.fold_left (fun (s, n) t ->
        let s', n' = format_tree width bp t in
        max s s', n + n')
      	(0.0,0) lt
      with Fail_format _ -> raise (Fail_format true))
  | Atom(size) ->
      if size > width then raise (Fail_format true);
      size, 1
  | _ -> failwith "Illegal break"

(*
  width: largeur totale
  cur: espace restant
  enc: liste des lbreak deja rencontre
  bp0:
  bp:
  lb: environement

retour:
  meilleur des lignes precedente,
  ligne courante,
  nombre de break des sous-boites sur la ligne courante,
  nombre de break total
*)
and format_tree_list width cur enc bp0 bp lb = function
    [] -> (0.0,0.0,0,0)

  | IBreak(hw,tw,ptr)::suit ->
      let s = save () in (
      try
	if cur < hw then  raise (Fail_format true);
        comp hw (format_tree_list width (cur -. hw) enc
		 (bp -. tw) (bp +. hw) lb suit)
      with
        Fail_format b ->
          restore s;
	  if width < tw || width -. cur +. hw +. eCoef <= tw || not b
	  then raise (Fail_format false);
          set ptr;
          try compr tw (format_tree_list width (width -. tw)
			enc 0.0 tw lb suit)
          with Fail_format _ -> raise (Fail_format false))

  | LBreak(i,hw,tw)::suit ->
      let {state = ptr} = lb.(i) in
      let can_break = not (List.memq ptr enc) in
      let s = save () in (
      try
	if cur < hw then raise (Fail_format true);
        comp hw (format_tree_list width (cur -. hw) (ptr::enc)
		 (bp -. tw) (bp +. hw) lb suit)
      with
        Fail_format b when can_break ->
          restore s;
	  if width < tw then raise (Fail_format false);
          set ptr;
          compr tw (format_tree_list width (width -. tw) (ptr::enc)
		    0.0 tw lb suit))

  | Atom(size)::suit ->
      if cur < size then raise (Fail_format true);
      comp size (format_tree_list width (cur -. size) enc
	bp0 (bp +. size) lb suit)

  | t::suit ->
      let rec fn = function
          Atom(size)::suit ->
	    compf (size, size) (fn suit)
      	| (Box _ | VBox _) as t :: suit ->
	    compf (compute_size enc lb t) (fn suit)
        | _ ->
	    (0.0, 0.0)
      in
      let mi, ts = fn suit in
      let mi', ts' = compute_size enc lb t in
      if cur < mi +. mi' then raise (Fail_format true);
      let nw = min (cur *. (ts' /. (ts +. ts'))) (cur -. mi) in
      let sv = save () in
      let s, n = format_tree nw bp0 t in
      let s =
        if n <= 1 then s else
        let best_s = ref nw and prev_s = ref 0.0 and
	  keep = ref (restore_keep sv) in
      	while fabs (!best_s -. !prev_s) > dCoef do
          let nw = (!best_s +. !prev_s) /. 2.0 in
          let sv = save () in
          try
            let ns, n0 = format_tree nw bp0 t in
            if n0 <= n then begin
              best_s := ns; prev_s := !best_s; keep := restore_keep sv
	    end else begin
              restore sv; prev_s := nw
	    end
	  with
	    Fail_format _ ->
              restore sv; prev_s := nw
      	done;
      	redo !keep; !best_s
      in
      if n >= 1 & (s +. bp0) /. s > xCoef then raise (Fail_format true);
      let b, s', cn, n' = format_tree_list width (cur -. s) enc
	bp0 (bp +. s) lb suit in
      let s'' = s +. s' in max b s'', s'', max n cn, n'

let do_tree chout width strm =
  let t = read_tree [||] strm in
  (try
    let _ = format_tree width 0.0 t in ()
  with
    Fail_format _ ->
      prerr_endline "Fail to format one formula !";
      let f = format_failed t in
      prerr_float f;
      prerr_string " > ";
      prerr_float width;
      prerr_endline " !");
  output_file chout t

let do_all filename =
  let filename =
    let l =  String.length filename  in
    let lf = if l > 4 then String.sub filename (l - 4) 4 else "" in
    if (lf = ".af2") || (lf = ".tex") || (lf = ".pout") || (lf = ".dvi")
      then String.sub filename 0 (l - 4) else filename
  in
  let chin = open_in (filename ^ ".pout") in
  let chout = open_out (filename ^ ".pin") in
  let cstrm = Stream.of_channel chin in
  let strm = make_lexer [":";","] cstrm in
  let rec fn = parser
    [< 'Ident "start"; 'Kwd ":"; 'Float width; 'Ident "pt" >] ->
      do_tree chout width strm; fn strm
  | [< >] -> ()
  in
  fn strm;
  close_in chin;
  output_string chout "\\prettyend";
  close_out chout

let _ =
  try
    do_all Sys.argv.(1)
  with
    Failure s -> print_endline s
  | Sys_error s -> print_endline s
