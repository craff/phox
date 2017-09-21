(* functions and type to use binder *)

(* this exception is raised when you call start_term on a term with free*)
(* variable *)
exception Bindlib_error

(* this is the type of an expression of type 'b with a bound variable of *)
(* type 'a *)
type ('a,'b) binder

(* this is the subtitution function: it takes an expression with a bound*)
(* variable of type 'a and a value for this variable and replace all the*)
(* occurrence of this variable by this value *)
val subst : ('a,'b) binder -> 'a -> 'b

(* the type of an object of type 'a being constructed (this object may have*)
(* free variable *)
type 'a pre_term

(* the function to call when the construction of an expression of type 'a is*)
(* finished. The expression must have no free variable !*)
val start_term : 'a pre_term -> 'a

(* unit allows you to use an expression of type 'a in a larger expression*)
(* begin constructed with free variables *) 
val unit : 'a -> 'a pre_term

(* this is THE function constructing binder. If takes an expression of type*)
(* 'a pre_term -> 'b pre_term in general written (fun x -> expr) (we say that*)
(* x is a free variable of expr). And it construct the binder that build the*)
(* expression where x is bound *)
val bind :
 ('a pre_term -> 'b pre_term) -> ('a,'b) binder pre_term

(* this is another version of the previous function. The first*)
(* argument is a default value for the bound variable. If you write*)
(* (bind_val v (fun x -> expr)), then you may in "expr" use start_term on*)
(* a term using "x", then the value of "x " will be "fn x" *)

val bind_val :
 ('a pre_term -> 'a) -> ('a pre_term -> 'b pre_term) -> ('a,'b) binder pre_term

(* this is THE function that allows you to construct expression by allowing*)
(* the application of a function with free variable to an argument with free*)
(* variable *)
val apply : 
 ('a -> 'b) pre_term -> 'a pre_term -> 'b pre_term

(* Used in some cases ! *)
val bind_apply : 
 ('a, 'b) binder pre_term -> 'a pre_term -> 'b pre_term

(* The following function can be written using unit and apply but are given*)
(* because they are very usefull. Moreover, some of them are optimised *)
val unit_apply : 
 ('a -> 'b) -> 'a pre_term -> 'b pre_term

val unit_apply2 : 
 ('a -> 'b -> 'c) -> 'a pre_term -> 'b pre_term -> 'c pre_term

val unit_apply3 : 
 ('a -> 'b -> 'c -> 'd) -> 'a pre_term -> 
   'b pre_term  -> 'c pre_term -> 'd pre_term

val build_pair :
 'a pre_term -> 'b pre_term -> ('a * 'b) pre_term

val build_list :
 'a pre_term list -> 'a list pre_term

val build_array :
 'a pre_term array -> 'a array pre_term

(* this function tells you if a 'a pre_term is closed. This may be
useful when optimizing a program *)

val is_closed : 'a pre_term -> bool

(* unit_apply_test f t = unit_apply (f (is_closed t)) t *)

val unit_apply_test : 
 (bool -> 'a -> 'b) -> 'a pre_term -> 'b pre_term

(* unit_apply2_test f t1 t2 = 
     unit_apply2 (f (is_closed t1 & is_closed t2)) t1 t2 *)

val unit_apply2_test : 
 (bool -> 'a -> 'b -> 'c) -> 'a pre_term -> 'b pre_term -> 'c pre_term

(* The following functions allow you too bind simultaneously a
 variable in two terms, this is useful when building by recurence two
 terms *) 

val bind_pair : ('a pre_term -> 'b pre_term * 'c pre_term)
   -> ('a,'b) binder pre_term * ('a,'c) binder pre_term

val bind_pair_val : ('a pre_term -> 'a) -> 
   ('a pre_term -> 'b pre_term * 'c pre_term) ->
   ('a,'b) binder pre_term * ('a,'c) binder pre_term

(* The following functions allow you too bind simultaneously a
 variable in a list of terms, this is useful when building by recurence 
 a list of terms *) 

val bind_list : ('a pre_term -> 'b pre_term list) ->
                      ('a,'b) binder pre_term list

val bind_list_val : ('a pre_term -> 'a) -> 
   ('a pre_term -> 'b pre_term list) ->
   ('a,'b) binder pre_term list

(* the following structures allow you to define function like
bind_pair or bind_list for your own types, if you can provide a "map"
function for your types. *)

module type Map = 
  sig
    type 'a t
    val map : ('a -> 'b) -> 'a t -> 'b t
  end

module type S =
  sig
    type 'a t
    val fn : ('a pre_term -> 'b pre_term t) -> ('a,'b) binder pre_term t
    val fn_val : ('a pre_term -> 'a) -> ('a pre_term -> 'b pre_term t) -> 
                     ('a,'b) binder pre_term t
  end

module Bind_struct(M: Map) : (S with type 'a t = 'a M.t)

module type Map2 = 
  sig
    type ('a, 'b) t
    val map : ('a -> 'b) -> ('c -> 'd) -> ('a, 'c) t -> ('b, 'd) t
  end

module type S2 =
  sig
    type ('a, 'b) t
    val fn : ('a pre_term -> ('b pre_term, 'c pre_term) t) -> 
                   (('a,'b) binder pre_term, ('a,'c) binder pre_term) t
    val fn_val : 
             ('a pre_term -> 'a) -> ('a pre_term -> ('b pre_term, 'c pre_term) t) -> 
                   (('a,'b) binder pre_term, ('a,'c) binder pre_term) t
  end

module Bind_struct2(M: Map2) : (S2 with type ('a, 'b) t = ('a, 'b) M.t)


