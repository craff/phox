(*######################################################*)
(*	       		lang.ml	       	                *)
(*######################################################*)

let language = ref `English

let set_language s =
  if String.length s < 2 then  language := `English else
  match String.sub s 0 2  with
    "us" | "en" -> language := `English
  | "fr" -> language := `French
  | _ -> language := `English

let _ =
  try set_language (Sys.getenv "LANG")
  with Not_found -> try set_language (Sys.getenv "LC_LANG")
  with Not_found -> ()

let get_message s = match s, !language with
  `Immediat, `English -> "immediat"
| `Immediat, `French -> "immédiat"

| `Let, `English -> "let"
| `Let, `French -> "soit"

| `And, `English -> "@ and@ "
| `And, `French -> "@ et@ "

| `AndS, `English -> " and "
| `AndS, `French -> " et "

| `LookFor, `English -> "we look for"
| `LookFor, `French -> "cherchons"

| `Then, `English -> "@ then@ "
| `Then, `French -> "@ puis@ "

| `Cases, `English -> "we consider@ %d@ cases:@ "
| `Cases, `French -> "distinguons@ %d@ cas :@ "

| `WeHave, `English -> "we have"
| `WeHave, `French -> "on a"

| `Assume, `English -> "assume"
| `Assume, `French -> "supposons"

| `SuchThat, `English -> "such that"
| `SuchThat, `French -> "tel que"

| `SuchThatS, `English -> "such that"
| `SuchThatS, `French -> "tels que"

| `Prove, `English -> "prove"
| `Prove, `French -> "prouvons"

| `Computes, `English -> "computes to"
| `Computes, `French -> "s'évalue en"

| `From, `English -> "From"
| `From, `French -> "D'après"

| `With, `English -> "with"
| `With, `French -> "avec"

| `Induction, `English -> "By induction on"
| `Induction, `French -> "Par récurrence sur "
let get_format s = Obj.magic (get_message s)
