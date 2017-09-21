type data =
  EInt of Num.num
| EString of string

val eq_data : data -> data -> bool

val compare_data : data -> data -> int

val string_of_data : data -> string

