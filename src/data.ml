type data =
  EInt of Num.num
| EString of string

let eq_data d d' = match d, d' with
  EInt n, EInt n' -> Num.eq_num n n'
| EString s, EString s' -> s = s'
| _ -> false

let compare_data d d' = match d, d' with
  EInt n, EInt n' -> Num.compare_num n n'
| EString s, EString s' -> compare s s'
| _ -> 
    let fn = function 
	EInt _ -> 0
      | EString _ -> 1
    in fn d - fn d'

let string_of_data = function
    EInt n -> Num.string_of_num n 
  | EString s -> "\"" ^ (String.escaped s) ^ "\""
