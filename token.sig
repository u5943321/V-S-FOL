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


end
