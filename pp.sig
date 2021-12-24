signature pp = 
sig

datatype gravity = LR of int option * int option

val int_option_leq: int * int option -> bool
val int_option_less: int * int option -> bool
val is_infix: string -> bool

end
