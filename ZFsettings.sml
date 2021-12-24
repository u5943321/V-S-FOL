val _ = new_sort "set" [];

val set_sort = mk_sort "set" []

val _ = new_pred "isRel" [("f",set_sort),("A",set_sort),("B",set_sort)]
val _ = new_pred "isFun" [("f",set_sort),("A",set_sort),("B",set_sort)]
val _ = new_fun "Dom" (set_sort,[("f",set_sort)])
val _ = new_fun "Cod" (set_sort,[("f",set_sort)])
val _ = new_fun "Im" (set_sort,[("f",set_sort)])

(*Axiom 5 (Collection): For any set A and any property P which can obtain of an element of A and a set, there exists a set B, function p:B→A, and a B-indexed family of sets M:B↬Y such that (1) P(p(b),Mb) holds for any b∈B, and (2) for any a∈A, if there exists a set X with P(a,X), then a∈im(p).

Theorem 3.1. The sets, elements, and relations in a model of ZF satisfy the Collection axiom of SEAR.


*)

val _ = new_fun "Rto" (set_sort,[("R",set_sort),("a",set_sort)])
val _ = new_fun "Eval" (set_sort,[("f",set_sort),("a",set_sort)])

val _ = new_pred "In" [("a",set_sort),("A",set_sort)]


val Thm_3_1 = 
“!A.?B f M Y. isFun(f,A,B) & isRel(M,B,Y) &
 !b. In(b,B) ==> P(Eval(p,b),Rto(M,b)) &  
 !a. In(a,A) & (?X. P(a,X)) ==> In(a,Im(p))”
