
val listof_sorts = Binarymap.listItems (!sorts)

val ground_sorts = 
    List.filter on_ground (List.map fst listof_sorts)

val sort_infixes0: (string,string)Binarymap.dict = 
Binarymap.mkDict String.compare

val sort_infixes = ref sort_infixes0

fun new_sort_infix st symbol = 
    sort_infixes := Binarymap.insert(!sort_infixes,symbol,st)

fun sortname_of_infix syb =
    case Binarymap.peek(!sort_infixes,syb) of 
        SOME sn => sn
      | _ => raise TER ("sortname_of_infix.no sort with infix symbol: " ^ syb,[],[])


val _ = new_sort "ob" [] 
val _ = new_sort "ar" [("A",mk_sort "ob" []),("B",mk_sort "ob" [])]

val _ = new_sort "set" [] 

val _ = new_fun "o" (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])],[("f",mk_sort "ar" [mk_var("B",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])]),("g",mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("B",mk_sort "ob" [])])])


val _ = new_fun "id" 
       (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("A",mk_sort "ob" [])],
        [("A",mk_sort "ob" [])])

val _ = new_sort_infix "ar" "->"

fun of_sort_ns sn = (of_sort sn) o mk_var

fun select_vars sn (vl,l0) =  ((List.filter (not o (of_sort_ns sn)) vl),(List.filter (of_sort_ns sn) vl) :: l0)

fun partition_sorts vl = 
    snd $ List.foldr (uncurry select_vars) (vl,[]) (List.map fst (listof_sorts (!SortDB)))

rastt
parse_ast $ lex "a: set"
val tl = lex "f:ar(A,A)"
parse_ast $ lex "f:ar(A,A)";

val tl' = List.tl rest
parse_ast_atom tl'

parse_ast_fix 0 (a0,rest)

val (a0,rest) = (parse_ast_atom $ lex "f:ar(A,A)")



val _ = new_sort "ob" [];
val _ = new_sort "ar" [("A",mk_sort "ob" []),("B",mk_sort "ob" [])];

val _ = new_sort "set" [];

val _ = new_fun "o" (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])],[("f",mk_sort "ar" [mk_var("B",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])]),("g",mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("B",mk_sort "ob" [])])]);


val _ = new_fun "id" 
       (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("A",mk_sort "ob" [])],
        [("A",mk_sort "ob" [])]);

val _ = new_sort_infix "ar" "->";



rapf "!B A f:B ->A. id (A) o f = f";
rapf "!A B f: A -> B. f o id(A) = f";
rapf "!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f";

val ob_sort = mk_sort "ob" [];
fun ar_sort A B = mk_sort "ar" [A,B];

val _ = new_fun "1" (mk_sort "ob" [],[]);
val ONE = mk_fun "1" [];
val _ = new_fun "To1" (mk_sort "ar" [mk_var ("A",ob_sort),ONE],[("A",ob_sort)]);
val _ = new_fun "0" (mk_sort "ob" [],[]);
val ZERO = mk_fun "0" [];
val _ = new_fun "From0" (mk_sort "ar" [ZERO,mk_var ("A",ob_sort)],[("A",ob_sort)]);

rapf "!X f:X->1. f = To1(X)";
rapf "!X f:0->X. f = From0(X)";

val _ = new_fun "*" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun Po A B = mk_fun "*" [A,B];
fun mk_ob name = mk_var (name,ob_sort);
fun mk_ar name dom cod = mk_var (name,ar_sort dom cod);
val _ = new_fun "Pa" (ar_sort (mk_ob "X") (Po (mk_ob "A") (mk_ob "B")),
 [("f",ar_sort (mk_ob "X") (mk_ob "A")),("g",ar_sort (mk_ob "X") (mk_ob "B"))]);

val qreadf = rapf o q2str;
qreadf
val _ = new_fun "π₁" ("")
lex "!X A f:X->A B g:X-> B. ?!fg:X-> A * B. T"

rapf "T"
val (pf,env) = read_ast_pf "?!f. T"

mk_uex "f" (mk_sort "ob" []) (mk_fvar "a")

mk_exists "f" (mk_sort "ob" []) (mk_fvar "a")


form_from_pf env pf


parse_ast (lex "?!f. T")


val _ = new_sort "ob" []
“?!f:ob. T”
rapf "!X A f:X->A B g:X->B."
"!A.!B.!AB.!p1:AB->A.!p2:AB->B.ispr(p1,p2)<=>!X.!f:X->A.!g:X->B.?fg:X->AB.!fg':X->AB.p1 o fg' = f & p2 o fg' = g <=> fg' = fg"

val _ =  new_pred "P" [("A",mk_sort "ob" [])]

val ob_sort = mk_sort "ob" []
fun ar_sort A B = mk_sort "ar" [A,B]

val ground_sorts = Binarymap.listItems sorts

rapf "ob" "P(a)"

(*reasonable sort infixes can be -> => ≃> --> ~> ~~> etc

so how can user define ≃*)

(*so should it be sort * string or string * sort dict?*)

val sort_infixes0: (string,string)Binarymap.dict = 
Binarymap.mkDict String.compare

val sort_infixes = ref sort_infixes0

fun new_sort_infix srt symbol = 
    sort_infixes := Binarymap.insert(!sort_infixes,symbol,srt)

fun sortname_of_infix syb =
    case Binarymap.peek(!sort_infixes,syb) of 
        SOME sn => sn
      | _ => raise simple_fail ("sortname_of_infix.no sort with infix symbol: " ^ syb)



Want we can write f:ar(A,B), but if the user write ar has infix ->, then parser can read f:A ->B.


