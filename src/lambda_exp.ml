open Bindlib
open Format


type term =
    App of term * term
  | Lam of (term, term) binder
  | Cro of stack * term
  | Mu  of (stack, term) binder
  | Side of string
  
  | SVar of string
  | TVar of term pre_term
  | Def of term_val

and term_val = {
  name : string;
  mutable value : term;
}

and stack =
    Stack of term list * stack pre_term
  | SStack of string
 
let bApp = unit_apply2 (fun x y -> App(x,y)) 

let bLam f = unit_apply (fun x -> Lam x) (bind f)

let bCro = unit_apply2 (fun x y -> Cro(x,y)) 

let bMu f = unit_apply (fun x -> Mu x) (bind f)

let bDef t = unit (Def t)

let bSVar name = SVar name

let bSide name = Side name

let cc = 
  start_term (
    bLam (fun x -> bMu (fun a ->
			  bCro a (bApp x (bLam (fun y -> bCro a y))))))

let mkCro a t = match a with
    None -> t
  | Some a -> bCro a t

let idt = start_term (bLam (fun x -> x))

let rec eval' term stack hcr =  match term, stack with
  Lam t, u::stack -> 
    eval' (subst t u) stack hcr
| Lam t, [] ->
    mkCro hcr (bLam (fun x -> eval' (subst t (TVar x)) [] None))
| App(t,u), stack ->
    eval' t (u::stack) hcr
| Side s, _ ->
    print_string s; print_flush (); eval' idt stack hcr
| Mu t, _ ->
    (match hcr with
      None ->  bMu (fun a -> eval' (subst t (Stack(stack, a))) [] None)
    | Some a -> eval' (subst t (Stack(stack, a))) [] None)
| Def t as d, _ ->
    if t.value != d then eval' t.value stack hcr
    else mkCro hcr (List.fold_left (fun h a -> bApp h (eval' a [] None)) (unit term) stack)
| TVar x, _ ->
    mkCro hcr (List.fold_left (fun h a -> bApp h (eval' a [] None)) x stack)
| SVar s, _ ->
    mkCro hcr (List.fold_left (fun h a -> bApp h (eval' a [] None)) (unit (SVar s)) stack)
| Cro (Stack(s,a), t), _ ->
    eval' t s (Some a)
| _ -> failwith "bug in eval"

let eval t =
  start_term (eval' t [] None) 

let rec print_term' b n t =
  match t with
    SVar name -> print_string name
  | Lam t -> 
      if b > 0 then (print_string "("; open_hovbox 1);
      let name = "x"^(string_of_int n) in
      print_string "\\";
      print_string name;
      print_space ();
      print_term' 0 (n+1) (subst t (SVar name));
      if b > 0 then (close_box (); print_string ")")	
  | App(t,u) ->
      if b > 1 then (print_string "("; open_hovbox 1);
      print_term' 1 n t;
      print_space ();
      print_term' 2 n u;
      if b > 1 then (close_box (); print_string ")")	
  | Mu t ->
      if b > 0 then (print_string "("; open_hovbox 1);
      let name = "a"^(string_of_int n) in
      print_string "µ";
      print_string name;
      print_space ();
      print_term' 0 (n+1) (subst t (SStack name));
      if b > 0 then (close_box (); print_string ")");	
  | Cro(SStack name,t) ->
      if b > 0 then (print_string "("; open_hovbox 1);
      print_string "[";
      print_string name;
      print_string "]";
      print_term' 0 n t;
      if b > 0 then (close_box (); print_string ")")	
  | Def t ->
      print_string t.name
  | Side s ->
      print_string "\"";
      print_string (String.escaped s);
      print_string "\""
  | _ -> failwith "bug in print_term'"

let rec print_kvm_term' b n t =
  match t with
    SVar name -> if b then print_string(" ") ; print_string name
  | Lam t -> 
      let name = "x"^(string_of_int n) in
      print_string "\\";
      print_string name;
      print_kvm_term' true (n+1) (subst t (SVar name));
  | App(t,u) ->
      print_string "(";
      print_kvm_term' false n t;
      print_string ")";
      print_kvm_term' false n u;
  | Mu t ->
      let name = "a"^(string_of_int n) in
	if b then print_string(" ") ;	
	print_string "µ";
	print_string name;
	print_kvm_term' false (n+1) (subst t (SStack name));
  | Cro(SStack name,t) ->
      print_string "[";
      print_string name;
      print_string "]";
      print_kvm_term' false n t;
 | Def t ->
      if b then print_string(" ") ; print_string "$" ; 
      print_string t.name
  | Side s ->
      print_string "\"";
      print_string (String.escaped s);
      print_string "\""
  | _ -> failwith "bug in print_kvm_term'"

let print_kvm_term t = 
  print_kvm_term' false 0 t;
  print_newline ()
	
let print_term t = 
  print_term' 0 0 t; 
  print_newline ()
