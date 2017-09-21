(* $State: Exp $ $Date: 2004/05/18 15:55:28 $ $Revision: 1.6 $ *)
(*######################################################*)
(*			lexer.ml			*)
(*######################################################*)

(* the lexical analisys *)

open Local
open Format
open Stream
open Files

type token =
    Lpar | Rpar | Dot | Dol
  | Ident of string
  | Kwd of string
  | Num of Num.num
  | Float of float
  | Str of string
  | Char of char
  | Uid of int
  | Unid of string
  | Kid of string
  | Eof
  | Joker of string
  | Tex of string list * char Stream.t

exception Illegal_char of char

let string_of_token = function
  Lpar ->  "("
| Rpar ->  ")"
| Dot ->  "."
| Dol ->  "$"
| Joker s ->  "_"^s
| Ident s ->  s
| Kwd s ->  s
| Num n -> Num.string_of_num n
| Float x -> string_of_float x
| Str s ->  "\"" ^ (String.escaped s) ^ "\""
| Char c ->  "`" ^  (Char.escaped c) ^ "`"
| Uid n ->  "?" ^ string_of_int n
| Unid n ->  "?" ^ n
| Kid s ->  "'" ^ s
| Eof -> "end of file"
| Tex _ -> "a tex comment"

let print_token t = print_string (string_of_token t)

let initial_buffer = Bytes.make 32 ' '

let buffer = ref initial_buffer
let bufpos = ref 0

let reset_buffer () =
  buffer := initial_buffer;
  bufpos := 0

let store c =
  if !bufpos >= Bytes.length !buffer then begin
    let newbuffer = Bytes.make (2 * !bufpos) ' ' in
    Bytes.blit !buffer 0 newbuffer 0 !bufpos;
    buffer := newbuffer
  end;
  Bytes.set !buffer !bufpos c;
  incr bufpos

let last_char () =
  if !bufpos > 0 then !buffer.[!bufpos - 1] else ' '

let get_string () =
  let s = Bytes.sub !buffer 0 !bufpos in buffer := initial_buffer; s

let special = parser
  [< ' ('!' | '%' | '&' | '*' | '+' | ',' | '-' | '/' | ':' | ';' |
        '<' | '=' | '>' | '@' | '[' | '\\' | ']' | '^' | '`' | '#' |
        '{' | '|' | '}' | '~' | 'µ' ) as c >] -> c

let extra_dot = ref false

let maybe_white s = match s with parser
    [< ' (' '|'\010'|'\013'|'\009'|'\026'|'\012'); s >] -> ()
  | [< >] -> ()

let rec next_token s =
  if !extra_dot then (extra_dot:=false; Dot) else
  match s with parser
    [< ' (' '|'\010'|'\013'|'\009'|'\026'|'\012'); s >] ->
      next_token s
  | [< ' ('A'..'Z' | 'a'..'z' as c); s>] ->
      reset_buffer(); store c; Ident(ident s)
  | [< ' ('0'..'9' as c); s>] ->
      reset_buffer(); store c; number s
  | [< ' ('"'); s >] ->
      reset_buffer(); string s
  | [< ' ('?'); s >] ->
      reset_buffer(); uvar s
  | [< ' ('-'); s >] ->
      neg_number s
  | [< ' ('('); s >] ->
      maybe_comment s
  | [< ' ('\171'); s >] ->
      Lpar
  | [< ' (')'|'\187'); s >] ->
      Rpar
  | [< ' ('.'); _ = maybe_white; s >] ->
      Dot
  | [< ' ('$'); s >] ->
      Dol
  | [< ' ('_');  s >] ->
      reset_buffer(); joker s
  | [< ' ('\''); s >] ->
      reset_buffer(); char_or_kvar s
  | [< ' ('\255'); s>] ->
      Eof
  | [< c = special; s >] ->
      reset_buffer(); store c; ident2 s
  | [< 'c; s >] ->
      raise (Illegal_char c)

  and joker = parser
    [< ' ('.'); s >] ->
      Joker (ident s)
  | [< >] ->
      Joker ""

  and uvar = parser
    [< ' ('0'..'9' as c); s >] ->
      store c; uvar' s
  | [< ' ('A'..'Z' | 'a'..'z' as c); s>] ->
      store c; Unid(ident s)
  | [<  >] ->
      Uid (new_uvar ())

  and uvar' = parser
    [< ' ('0'..'9' as c); s >] ->
      store c; uvar' s
  | [<  >] ->
      Uid (int_of_string (get_string ()))

  and ident = parser
    [< ' ('A'..'Z'|'a'..'z'|'0'..'9'  as c); s>] ->
      store c; ident s
  | [< ' ('_'  as c); s>] ->
      if last_char () = '_' then
        raise (Stream.Error "Consecutive '_' are illegal");
      store c;
      ident' s
  | [< ' ('.' as c); s >] -> (
	match (peek s) with
	  Some ('A'..'Z'|'a'..'z'|'0'..'9') -> store c; ident s
	| _ -> extra_dot := true; get_string())
  | [< s >] -> primeseq s

  and ident' = parser
      [< c = special; s >] -> store c; ident'' s
    | [< s = ident >] -> s

  and ident'' = parser
      [< c = special; s >] -> store c; ident'' s
    | [< ' ('.' as c); s >] -> (
	match (peek s) with
	  Some ('A'..'Z'|'a'..'z'|'0'..'9') -> store c; ident s
	| _ -> extra_dot := true; get_string())
    | [< ' ('_' as c); s >] -> store c; ident' s
    | [< s >] -> primeseq s

  and primeseq = parser
    [< ' ('\'' as c); s >] -> store c; primeseq s
  | [< ' ('.' as c); s >] -> (
	match (peek s) with
	  Some ('A'..'Z'|'a'..'z'|'0'..'9') -> store c; ident s
	| _ -> extra_dot := true; get_string())
  | [< >] -> get_string()

  and ident2 = parser
    [< c = special; s >] -> store c; ident2 s
  | [< ' ('_' as c); s >] -> store c; Kwd (ident s)
  | [< ' ('.' as c); s >] -> (
	match (peek s) with
	  Some ('A'..'Z'|'a'..'z'|'0'..'9'|'_') -> store c; Kwd(ident s)
	| _ -> extra_dot := true; Kwd(get_string()))
  | [< >] -> Kwd (get_string())

  and char_or_kvar = parser
      [< ' ('a'..'z'|'A'..'Z' as c); s >] ->
	store c; char_or_kvar' s
    | [< ' ('\\'); c = escape; ' ('\'') >] -> Char c
    | [< ' c; ' ('\'') >] ->
	Char c

  and char_or_kvar' = parser
    [< ' ('a'..'z'|'A'..'Z' as c); s >] ->
      store c; kvar s
  | [< ' ('\'') >] ->
      Char (get_string ()).[0]
  | [<  >] ->
      Kid (get_string ())

  and kvar = parser
    [< ' ('a'..'z' as c); s >] ->
      store c; kvar s
  | [<  >] ->
      Kid (get_string ())

  and neg_number = parser
    [< ' ('0'..'9' as c); s >] ->
      reset_buffer(); store '-'; store c; number s
  | [< s >] ->
      reset_buffer(); store '-'; ident2 s

  and number = parser
    [< ' ('0'..'9' as c); s >] ->
      store c; number s
  | [< ' ('e'|'E'); s >] ->
      store 'E'; exponent_part s
  | [< ' ('.' as c); s >] -> (
      match (peek s) with
	  Some ('E'|'e'|'0'..'9') -> store c; decimal_part s
	| _ -> extra_dot := true; Num(Num.num_of_string(get_string())))
  | [< >] ->
      Num(Num.num_of_string(get_string()))

  and decimal_part = parser
    [< ' ('0'..'9' as c); s >] ->
      store c; decimal_part s
  | [< ' ('e'|'E'); s >] ->
      store 'E'; exponent_part s
  | [< >] ->
      Float(float_of_string(get_string()))

  and exponent_part = parser
    [< ' ('+'|'-' as c); s >] ->
      store c; end_exponent_part s
  | [< s >] ->
      end_exponent_part s

  and end_exponent_part = parser
    [< ' ('0'..'9' as c); s >] ->
      store c; end_exponent_part s
  | [< >] ->
      Float(float_of_string(get_string()))

  and string = parser
    [< ' ('"') >] -> Str(get_string())
  | [< ' ('\\'); c = escape; s >] -> store c; string s
  | [< ' ('\255') >] -> raise (Stream.Error "Unfinished string")
  | [< ' c; s >] -> store c; string s

  and digit = parser
    [< ' ('0'..'9' as c) >] -> Char.code c - Char.code '0'

  and escape = parser
    [< ' ('n') >] -> '\n'
  | [< ' ('r') >] -> '\r'
  | [< ' ('t') >] -> '\t'
  | [< d1 = digit; d2 = digit; d3 = digit >] ->
      Char.chr (d1 * 100 + d2 * 10 + d3)
  | [< ' c >] -> c

  and maybe_comment = parser
    [< ' ('*'); s >] -> tex_or_comment s
  | [< >] -> Lpar

  and tex_or_comment = parser
    [< ' ('!'); s >] -> start_tex s
  | [< s >] -> comment s; next_token s

  and start_tex s =
    let doc_list = ref [] in
    let rec read_header = parser
      [< ' ('A'..'Z' | 'a'..'z' as c); s>] ->
        reset_buffer(); store c; doc_list := (ident s)::!doc_list;
        read_header s
    | [< ' ('\t' | ' '); s >] -> read_header s
    | [< ' ('\n') >] -> ()
    | [< >] -> failwith "Illegal tex header"
    in
    read_header s;
    if !doc_list = [] then failwith "Illegal tex header";
    Tex (!doc_list, s)

  and comment = parser
    [< ' ('('); s >] -> maybe_nested_comment s
  | [< ' ('*'); s >] -> maybe_end_comment s
  | [< ' ('\255') >] -> raise (Stream.Error "Unfinished comment")
  | [< ' c; s >] -> comment s

  and maybe_nested_comment = parser
    [< ' ('*'); s >] -> comment s; comment s
  | [< ' ('\255') >] -> raise (Stream.Error "Unfinished comment")
  | [< ' c; s >] -> comment s

  and maybe_end_comment = parser
    [< ' (')') >] -> ()
  | [< ' ('*'); s >] -> maybe_end_comment s
  | [< ' ('\255') >] -> raise (Stream.Error "Unfinished comment")
  | [< ' c; s >] -> comment s


let rec reset_lexer tstr =
  let l = !cur_line and c = !cur_col in
  let rec fn = parser
    [< ' ('\n') >] -> ()
  | [< ' ('\r') >] -> ()
  | [< 'c; s >] -> fn s
  | [< >] -> ()
  in
  fn tstr; cur_line := l; cur_col := c
