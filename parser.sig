signature parser = 
sig
datatype psort = datatype pterm_dtype.psort   
datatype pterm = datatype pterm_dtype.pterm
datatype pform = datatype pterm_dtype.pform
type sort = term.sort
type term = term.term
structure Env: sig 
    type env
    val empty : env
    val insert_ps: string -> psort -> env -> env
    val insert_pt: string -> pterm -> env -> env
    val dps_of: env -> (string,psort)Binarymap.dict 
    val dpt_of: env -> (string,pterm)Binarymap.dict 
    val fresh_var: env -> string * env
    val lookup_pt: env -> string -> pterm option
    val lookup_ps: env -> string -> psort option
end  

datatype ast = 
         aId of string 
         | aApp of string * ast list
         | aInfix of ast * string * ast
         | aBinder of string * ast (*variable and sort*) * ast (*body*)


val parse_ast: token list -> ast * token list
val check_wffv: (string * sort) list -> bool
val map_HOLset: ('a -> 'b) -> 'a set -> ('b * 'b -> order) -> 'b set
val rapf: string -> form
val rastt: string -> term
val read_ast_f:
   string ->
       form * (string list * string list * string list * string list * int)
val read_ast_t:
   string ->
       term * (string list * string list * string list * string list * int)
val readfq: 'a HOLPP.frag list -> form
val try_until_ok: int -> string set -> string
val anno_cont_ast: (string * sort) set -> ast -> ast
val parse_term_with_cont: (string * sort) set -> string -> term
val parse_form_with_cont: (string * sort) set -> string -> form

end
