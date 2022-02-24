signature token = 
sig
datatype token = Key of string | Id of string;

val is_char : int * int * int -> bool
val is_letter_or_digit : int -> bool
val token_of : string -> token
val scan_ident : string list * string -> token * string
val scan: token list * string -> token list
val enclose : string -> string
val tokentoString: token -> string
val lex : string -> token list

(*
val letter_or_digit: (int -> bool) ref
val add_parsable: int -> unit
*)


val add_parse: int -> unit
val add_parse_range: int * int -> unit
val add_range: int * int -> int HOLset.set -> int HOLset.set
val letter_or_digits: int HOLset.set ref
val letter_or_digits0: int HOLset.set
val int_of: string -> int

end
