type poidsclause = float
type indiceclause = float option
val ordrepoids : 'a -> 'a -> int
val taillecndats : int ref
val pdsmax_global : float ref
val pdsmoy_global : unit -> float
val pds_min : int
val lower_indice : 'a option
val val_lower_indice : float
val val_default_indice : float
val default_indice : float option
val pdsmax_cndats : float ref
val listmax : int list -> int
val indice_of_int : int -> float option
val int_of_indice : float option -> int
val initpoids : int option -> float
val pds_res :
  n:int ->
  indice1:float option ->
  rhist:'a ->
  chist:('b * (float option * int)) list ->
  c1w:float ->
  nc1:int -> indice2:float option -> c2w:float -> nc2:int -> l:int -> float
val indice_res :
  i1:float option ->
  i2:float option ->
  rhist:('a * (float option * int)) list ->
  chist:('b * (float option * int)) list -> float option
val pds_rule :
  rindice:float option ->
  rpds:int -> nbre:int -> indice:'a -> pds:float -> float
val pds_cont : wpere:'a -> l:'b -> 'a
val indice_rule :
  i:float option -> hist:('a * (float option * int)) list -> float option
val affpds : float -> unit
val affind : float option -> unit
