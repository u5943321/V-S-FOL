


(*need to order the variables in the order of quantification, 
!a. P(a) ==> !b. Q(a,b,n)
a pred on n, the order of b is before a, b is the first component because it is the first one of being transposed. 

*)
fun binop_t s t1 t2 = mk_fun s [t1,t2]

fun unop_t s t = mk_fun s [t]

val And = binop_t "And"

val Or = binop_t "Or"

val Imp = binop_t "Imp"

val Iff = binop_t "Iff"

val id = unop_t "id"

val ALL = unop_t "ALL";

val EX = unop_t "EX";

val UE = unop_t "UE";

fun dest_ar s = 
    case view_sort s of
       vSrt("ar",[d,c]) => (d,c) 
     | _ => raise simple_fail "not an arr"

val dom = fst o dest_ar 
val cod = snd o dest_ar 

fun bounds f = 
    case view_form f of 
        vQ(q,n,s,b) => (n,s) :: bounds b
      | vConn(_,[f]) => bounds f
      | vConn(_,[f1,f2]) => (bounds f1) @ (bounds f2)
      | vPred _ => []
      | vConn(_,l) => raise simple_fail "bounds.wrong input"

fun Pol l = 
    case l of 
       [] => raise ERR ("Pol.empty input",[],[],[])
      |h :: t => 
       (case t of 
           [] => raise ERR ("Pol.sing input",[],[],[])
         | h1 :: t1 => 
           (case t1 of 
               [] => Po h h1
             | h2 :: t2 => 
               Po h (Pol t)))

(*
val ts = List.map rastt ["A","A","C","B","A"]

Pol ts


val ts = List.map rastt ["a:1->A","b:1->A","c:1->C","d:1->B","e:1->A"]
*)

fun mk_pj n1 n2 =
    mk_fun ("p" ^ (Int.toString n1) ^ (Int.toString n2))

(*only bound variables have corresponing components, free ones are composition with To1

val f = “!n:1->N. !a:1->N. P(Add(a,n)) ==> !b:1->N c:1->N. Q(b,c,n)”
    !n. !a. P(a,n) ==> !b c. Q(b,c,n)

in the outmost layer cannot use ALL, because only N remains, unless always compose with a N * 1. 

once have constant, always choose the projection to the last component since it is safe that it will never


like the HOL terms formla has type bool, it should produce a term of bool as well, which is an arrow 1->2. 

order of bounded vars [(n,1->N),(a:1->N),(b:1->N),(c:1->N)]

rev, get [c:1->N,b:1->N.a:1->N,n:1->N]

means the c is outmost, n is the last to be transposed 

before constructing each connective, need to makes sure that each pair of the connective comes from a common domain.

ALL(ALL(Imp(,ALL(ALL(Q o Pa(p41,p42,))))))

rastt "ALL(Imp(P o Pa(p1(N,N),p2(N,N)),ALL(ALL(Q o Pa3(p41(N,N,N,N),p42(N,N,N,N),p44(N,N,N,N))))))"

rastt "ALL(Imp(P o Pa(p43(N,N,N,N),p44(N,N,N,N)),ALL(ALL(Q o Pa3(p41(N,N,N,N),p42(N,N,N,N),p44(N,N,N,N))))))"


rastt "ALL(ALL(Q o Pa3(p41(N,N,N,N),p42(N,N,N,N),p44(N,N,N,N))))"
 *)

(*

fun compn (l:((string * sort) list)) t = 
    let val doms = Pol (List.map (dom o snd) l)
    in
    if not $ mem t l then mk_pj (length l) (length l) doms


*)

fun pos n l = 
    case l of 
        [] => raise simple_fail "pos.not a list member"
      | h :: t => if h = n then 1 else (pos n t) + 1


val f = “!n:1->N. !a:1->N. P(Add(a,n)) ==> !b:1->N c:1->N. Q(b,c,n)”


(* better have somme normalising procedure to pull all the quantifiers out???*)
val bvs = rev $ bounds f
val t = rastt "c:1->N"

fun term2IL bvs t =
    let val doms = List.map (cod o snd) bvs
        val tn = length doms
        val vdom = el tn doms
    in
        case view_term t of 
            vVar(n,s) => 
            if not $ mem (n,s) bvs then 
               binop_t "o" t (unop_t "To1" (Pol doms))
            else mk_pj tn (pos (n,s) bvs) doms
          | vFun(f,s,tl) => 
            mk_fun f (List.map (term2IL bvs) tl)
          | _ => raise simple_fail "bound variables should not be here"
    end; 



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

val p21_ex = prove_store("p21_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A,B)’ >> rw[])
(form_goal
 “!A B. ?p. p1(A,B) = p”));


val p21_def = p21_ex |> spec_all |> ex2fsym0 "p21" ["A","B"]
                     |> gen_all


val p22_ex = prove_store("p22_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(A,B)’ >> rw[])
(form_goal
 “!A B. ?p. p2(A,B) = p”));


val p22_def = p22_ex |> spec_all |> ex2fsym0 "p22" ["A","B"]
                     |> gen_all


val psym2IL = Binarymap.insert(Binarymap.mkDict String.compare, "Le",rastt "Char(LE)")

val f = “!n a.
     Le(Add(a, n),n0) & !b c:1->N. Le(Add(b,c),n)”

val bvs = rev $ bounds f 

form2IL bvs “Le(Add(b:1->N,c),n)”



val f0 = “!b c:1->N.Le(Add(b,c),n)”
val bvs = rev $ bounds f0
form2IL [dest_var $ rastt "n:1->N"] “!b c:1->N.Le(Add(b,c),n)”
form2IL [dest_var $ rastt "n:1->N"] 
“!a:1->N.
     Le(Add(a, n),n0) & !b c:1->N. Le(Add(b,c),n)”


val f0 = “!a:1->N. Le(a,n)”


 
fun form2IL bvs f = 
    case view_form f of 
        vConn("&",[f1,f2]) => 
        And (form2IL bvs f1) (form2IL bvs f2)
      | vConn("|",[f1,f2]) => 
        Or (form2IL bvs f1) (form2IL bvs f2)
      | vConn("==>",[f1,f2]) => 
        Imp (form2IL bvs f1) (form2IL bvs f2)
      | vPred("=",true,[t1,t2]) =>
        mk_pred_ap (mk_fun "Eq" [cod (sort_of t2)])
         [term2IL bvs t1,term2IL bvs t2]
      | vPred(P,_,tl) => 
        (case Binarymap.peek(psym2IL,P) of
            SOME p => mk_pred_ap p (List.map (term2IL bvs) tl)
          | _ => raise simple_fail ("form2IL.pred: " ^ P ^ " not found"))
      | vQ ("!",n,s,b) => ALL (form2IL ((n,s) :: bvs) b)
      | vQ ("?",n,s,b) => EX (form2IL ((n,s) :: bvs) b)
      | vQ ("?!",n,s,b) => UE (form2IL ((n,s) :: bvs) b)
      | _ => raise ERR ("form2IL.ill-formed formula",[],[],[f])


fun form2IL bvs f = 
    case view_form f of 
        vConn("&",[f1,f2]) => 
        And (form2IL bvs f1) (form2IL bvs f2)
      | vConn("|",[f1,f2]) => 
        Or (form2IL bvs f1) (form2IL bvs f2)
      | vConn("==>",[f1,f2]) => 
        Imp (form2IL bvs f1) (form2IL bvs f2)
      | vPred("=",true,[t1,t2]) =>
        mk_pred_ap (mk_fun "Eq" [cod (sort_of t2)])
         [term2IL bvs t1,term2IL bvs t2]
      | vPred(P,_,tl) => 
        (case Binarymap.peek(psym2IL,P) of
            SOME p => mk_pred_ap p (List.map (term2IL bvs) tl)
          | _ => raise simple_fail ("form2IL.pred: " ^ P ^ " not found"))
      | vQ ("!",n,s,b) => ALL (form2IL bvs b)
      | vQ ("?",n,s,b) => EX (form2IL bvs b)
      | vQ ("?!",n,s,b) => UE (form2IL bvs b)
      | _ => raise ERR ("form2IL.ill-formed formula",[],[],[f])



fun form2IL bvs f = 
    case view_form f of 
        vConn("&",[f1,f2]) => 
        And (form2IL bvs f1) (form2IL bvs f2)
      | vConn("|",[f1,f2]) => 
        Or (form2IL bvs f1) (form2IL bvs f2)
      | vConn("==>",[f1,f2]) => 
        Imp (form2IL bvs f1) (form2IL bvs f2)
      | vPred("=",true,[t1,t2]) =>
        mk_pred_ap (mk_fun "Eq" [cod (sort_of t2)])
         [term2IL bvs t1,term2IL bvs t2]
      | vPred(P,_,tl) => 
        (case Binarymap.peek(psym2IL,P) of
            SOME p => mk_pred_ap p (List.map (term2IL bvs) tl)
          | _ => raise simple_fail ("form2IL.pred: " ^ P ^ " not found"))
      | vQ ("!",n,s,b) => ALL (form2IL bvs b)
      | vQ ("?",n,s,b) => EX (form2IL bvs b)
      | vQ ("?!",n,s,b) => UE (form2IL bvs b)
      | _ => raise ERR ("form2IL.ill-formed formula",[],[],[f])





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

(*
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
*)

 
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


