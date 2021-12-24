
fun binop_t s t1 t2 = mk_fun s [t1,t2]

fun unop_t s t = mk_fun s [t]

val And = binop_t "And"

val Or = binop_t "Or"

val Imp = binop_t "Imp"

val Iff = binop_t "Iff"

val id = unop_t "id"

val ALL = unop_t "ALL";

fun dest_ar s = 
    case view_sort s of
       vSrt("ar",[d,c]) => (d,c) 
     | _ => raise simple_fail "not an arr"

val dom = fst o dest_ar 
val cod = snd o dest_ar 

fun term2IL v t =
    if t = v then id (cod $ sort_of t)
    else
        case view_term t of 
            vVar(n,s) => binop_t "o" t (unop_t "To1" (cod $ sort_of v))
          | vFun(f,s,tl) => 
            mk_fun f (*(ar_sort (cod $ sort_of v) (cod s))*)
                   (List.map (term2IL v) tl)
          (*  Fun(f,ar_sort (cod $ sort_of v) (cod s),List.map (term2IL v) tl)*)
          | _ => raise simple_fail "bound variables should not be here"; 


term2IL (rastt "c:1->N") (rastt "Add(a:1->N,b)") 

 
val truth = mk_fun "TRUE" []

fun Pal l = 
    case l of 
       [] => raise ERR ("Pal.empty input",[],[],[])
      |h :: t => 
       (case t of 
           [] => raise ERR ("Pal.sing input",[],[],[])
         | h1 :: t1 => 
           (case t1 of 
               [] => Pa h h1
             | h2 :: t2 => 
               Pa h (Pal t)))

val ts = List.map rastt ["a:1->A","b:1->A","c:1->C","d:1->B","e:1->A"]

fun mk_pred_ap pt args = (mk_o pt (Pal args))



val psym2IL = Binarymap.insert(Binarymap.mkDict String.compare, "Le",rastt "Char(LE)")


fun form2IL v f = 
    case view_form f of 
        vConn("&",[f1,f2]) => 
        And (form2IL v f1) (form2IL v f2)
      | vConn("|",[f1,f2]) => 
        Or (form2IL v f1) (form2IL v f2)
      | vConn("==>",[f1,f2]) => 
        Imp (form2IL v f1) (form2IL v f2)
      | vPred("=",[t1,t2]) =>
        mk_pred_ap (mk_fun "Eq" [cod (sort_of t2)])
         [term2IL v t1,term2IL v t2]
      | vPred(P,tl) => 
        (case Binarymap.peek(psym2IL,P) of
            SOME p => mk_pred_ap p (List.map (term2IL v) tl)
          | _ => raise simple_fail ("form2IL.pred: " ^ P ^ " not found"))
      | vQ ("!",n,s,b) => ALL (form2IL v b)

val ((n,s),b) = dest_forall “!c:1->N. a = c”

val v = rastt "a:1->N"

form2IL (rastt "a:1->N") “Add(a:1->N,b) = c”

form2IL (rastt "a:1->N") “!c:1->N.a = c”

form2IL (rastt "a:1->N") “Le(a:1->N,b)”

form2IL (rastt "a:1->N") “Le(Add(a:1->N,c),b)”

form2IL (rastt "a:1->N") “!b.Le(Add(a:1->N,c),b)”


