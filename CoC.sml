
val _ = new_sort "cat" [];

val _ = new_sort "func" [("A",mk_sort "cat" []),("B",mk_sort "cat" [])]

val _ = new_sort_infix "func" "=>"

val cat_sort = mk_sort "cat" []
fun func_sort A B = mk_sort "func" [A,B]
fun mk_cat A = mk_var(A,cat_sort)
fun mk_func F A B = mk_var(F,func_sort A B)

val _ = EqSorts := "func" :: (!EqSorts)

val _ = new_pred "Holds" [("R",rel_sort (mk_set "A") (mk_set "B")),
                         ("a",mem_sort (mk_set "A")),
                         ("b",mem_sort (mk_set "B"))]
