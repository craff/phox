(* $State: Exp $ $Date: 2000/10/12 09:58:27 $ $Revision: 1.1.1.1 $ *)
(* This program is a small time-profiler for Caml-Light *)

(* It requires the UNIX library *)

(* To use it, link it with the program you want to profile (don not forget
"-lunix -custom unix.zo" among the link options).

To trace a function "f" with ONE argument add the following just after the
definition of "f":

  let f = profile "f" f

(the string is used to print the profile infomation).

If f has two arguments do the same with profile2, idem with 3 and
4. For more than 4 arguments ... modify the function profile yourself,
it is very easy (look the differences between profile and profile2.

If you want to profile two mutually recursive functions, you had better
to rename them :

  let f' = .... f' ... g'
  and g' = .... f' .... g'
  

  let f = profile "f" f'
  let g = profile "f" g'

Before the program quits, you should call "print_profile ()". It
produces a result of the following kind:

  f                5.32    7.10    58%   80% 
  g                4.00    4.00    42%   42%
  main             0.12    9.44     1%   100%
  total           -9.44    0.00   -100%  0%

- The first column is the name of the function.

- The third column give the time (utime + stime) spend inside the function.

- The second column give the time spend inside the function minus the
  time spend in other profiled functions called by it

- the fourth and fifth column give the same information as the second
  and third but in percentage of the total time.

The last line can be ignored (there is a bug if the down-right digit is non
zero)

*)

let tot_ptr = ref 0.0 and tot_ptr' = ref 0.0

let prof_table = ref ["total",tot_ptr,tot_ptr']

let stack = ref [tot_ptr']

let print_profile () =
  let tot = 100.0 /. (-. !tot_ptr') in
  print_newline (); 
  let l = Sort.list (fun (_,_,p) (_,_,p') -> !p > !p') !prof_table in
  List.iter (fun (name,ptr,ptr') ->
    let pc = !ptr *. tot and pc' = !ptr' *. tot in
    Printf.printf "%-20s %8.2f %8.2f %8.2f%% %8.2f%% \n" 
                  name !ptr' !ptr pc' pc) l;
  flush stdout

let addp name = 
  let rec fn = function
  [] -> 
    let ptr = ref 0.0 and ptr' = ref 0.0 in 
    prof_table := (name,ptr,ptr')::!prof_table;
    ptr, ptr'
  | (name',ptr,ptr')::_ when name = name' -> ptr, ptr'
  | _::l -> fn l
  in fn !prof_table

let profile name f =
  let ptr,ptr' = addp name in
  (fun x ->
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    stack := ptr'::!stack;
    try
      let r = f x in
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      r
    with e ->
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      raise e
  )

let profile2 name f =
  let ptr,ptr' = addp name in
  (fun x y ->
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    stack := ptr'::!stack;
    try
      let r = f x y in
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      r
    with e ->
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      raise e
  )

let profile3 name f =
  let ptr,ptr' = addp name in
  (fun x y z ->
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    stack := ptr'::!stack;
    try
      let r = f x y z in
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      r
    with e ->
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      raise e
  )

let profile4 name f =
  let ptr,ptr' = addp name in
  (fun x y z t ->
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    stack := ptr'::!stack;
    try
      let r = f x y z t in
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      r
    with e ->
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      raise e
  )

let profile5 name f =
  let ptr,ptr' = addp name in
  (fun x y z t u ->
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    stack := ptr'::!stack;
    try
      let r = f x y z t u in
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      r
    with e ->
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      raise e
  )

let profile6 name f =
  let ptr,ptr' = addp name in
  (fun x y z t u v ->
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    stack := ptr'::!stack;
    try
      let r = f x y z t u v in
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      r
    with e ->
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      raise e
  )

let profile7 name f =
  let ptr,ptr' = addp name in
  (fun x y z t u v w ->
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    stack := ptr'::!stack;
    try
      let r = f x y z t u v w in
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      r
    with e ->
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      raise e
  )

let profile8 name f =
  let ptr,ptr' = addp name in
  (fun x y z s t u v w ->
    let {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
    stack := ptr'::!stack;
    try
      let r = f x y z s t u v w in
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      r
    with e ->
      let {Unix.tms_utime = ut';Unix.tms_stime = st'} = Unix.times () in
      let t = (ut' -. ut) +. (st' -. st) in
      (match !stack with
        _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
      |  _ -> failwith "bug in profile");
      ptr := !ptr +. t;
      ptr' := !ptr' +. t;
      raise e
  )


