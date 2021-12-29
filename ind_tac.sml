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

fun mk_pj n1 n2 =
    mk_fun ("p" ^ (Int.toString n1) ^ (Int.toString n2))


fun pos n l = 
    case l of 
        [] => raise simple_fail "pos.not a list member"
      | h :: t => if h = n then 1 else (pos n t) + 1


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

fun inserts d l = List.foldr (fn ((a,b),d) => Binarymap.insert(d,a,b)) d l


val psym2IL = inserts (Binarymap.mkDict String.compare)
[("Le",rastt "Char(LE)"),("Lt",rastt "Char(LT)"),
 ("HasCard",rastt "hasCard(X)")]



 
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


val _ = new_pred "HasCard" [("xs",ar_sort ONE (rastt "Exp(X,1+1)")),
                            ("n",ar_sort ONE N)]

val HasCard_def = store_ax("HasCard_def",
 “!X xs n. HasCard(xs,n) <=> hasCard(X) o Pa(xs,n) = TRUE”)

hasCard(X) o Pa(xs,n) = TRUE

hasCard(X) o Pa(xs,n) = TRUE & !x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0)

form2IL [dest_var $ rastt "n:1->N",dest_var $ rastt "n1:1->N"]
“n = TRUE” 


“P o n:1->N = TRUE & Q o n1:1->N = TRUE”
