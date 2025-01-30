(*######################################################*)
(*			undo.ml  			*)
(*######################################################*)

open Format

type undo_pos = (unit -> unit) list

let undo_list = ref None

let update v t =
  begin
    let old = !v in
    let undo () = v := old in
    match !undo_list with
      Some l -> undo_list := Some (undo::l)
    | None -> ()
  end;
  v := t

let add_to_undo f =
  begin
    match !undo_list with
      Some l -> undo_list := Some (f::l)
    | None -> ()
  end

let reset_undo_unif () =
  undo_list := None

let init_undo_unif () =
  undo_list := Some []

let get_undo_pos () =
  match !undo_list with
    Some l -> l
  | None -> []

let do_undo l =
  match !undo_list with
    Some l' ->
      let rec fn l' =
	if not (l == l') then begin
	  match l' with
	    f::suit ->
	      f (); fn suit
	  | [] ->
	      failwith "bug in do_undo"
	end
      in fn l'; undo_list := Some l
  | None -> ()

let print_undo_size () =
  (match !undo_list with
    None -> print_int 0
  | Some l -> print_int (List.length l));
  print_newline ()
