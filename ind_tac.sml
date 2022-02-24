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
           [] => (*raise ERR ("Pol.sing input",[],[],[])*) h
         | h1 :: t1 => 
           (case t1 of 
               [] => Po h h1
             | h2 :: t2 => 
               Po h (Pol t)))

fun mk_pj n1 n2 =
    mk_fun ("p" ^ (Int.toString n1) ^ (Int.toString n2))

fun mk_pj n1 n2 =
    if n1 = 1 andalso n2 = 1 then mk_fun "id" 
    else if n1 = 2 andalso n2 = 1 then mk_fun "p1" 
    else if n1 = 2 andalso n2 = 2 then mk_fun "p2"
    else
    mk_fun ("p" ^ (Int.toString n1) ^ (Int.toString n2))


fun pos n l = 
    case l of 
        [] => raise simple_fail "pos.not a list member"
      | h :: t => if h = n then 1 else (pos n t) + 1


(*
p11(A) = id(A)

form2IL [dest_var $ rastt "n:1->N"]
“P o n:1->N = TRUE” 
 
want EQ(1+1) o Pa(P,TRUE o To1(N)) o n

when bvs are a b. output is a term FM such that 
!a b. FM o Pa(a,b) = TRUE <=> P(a,b) 

val f = “P o n:1->N = TRUE” 

val bvs = [dest_var $ rastt "n:1->N"]

val (_,[t1,t2]) = dest_pred f

t1

val (f,s,tl) = dest_fun t1

term2IL bvs (rastt "TRUE") (rastt "P:N->1+1")(hd tl)

*)

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

(*So in current version, the term2IL vFun only for function symbols which corresponds to function application to generalised elements. maybe handle exception by Ev?

so P o n corres EV(Tp1(P),n), this is a function app to gen el. 

P:N -> 1+1. Tp1(N):1-> Exp(N,1+1),n:1->N

still P is not a generalised element so the construction of Tp1(P) still problem.
*)




val truth = mk_fun "TRUE" []

fun Pal l = 
    case l of 
       [] => raise ERR ("Pal.empty input",[],[],[])
      |h :: t => 
       (case t of 
           [] => (*raise ERR ("Pal.sing input",[],[],[])*) h
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


val psym2IL0 = inserts (Binarymap.mkDict String.compare)
[("Le",(rastt "Char(LE)",[])),
 ("Lt",(rastt "Char(LT)",[])),(*
 ("HasCard",(rastt "hasCard(X)",
             [("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)")),
              ("n",ar_sort (mk_ob "A") N)])),*)
 ("Even",(rastt "EVEN",[])),
 ("IN",(rastt "Mem(X)",
        [("x",ar_sort (mk_ob "A") (mk_ob "X")),
         ("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)"))])),
 ("Sim",(rastt "relJ",[]))]

val psym2IL = ref psym2IL0

fun new_psym2IL (pred,(predfun,inputs)) = 
psym2IL := Binarymap.insert(!psym2IL,pred,(predfun,inputs))

(*
form2IL [dest_var $ rastt "xs:1->Exp(X,1+1)",dest_var $ rastt "n:1->N"]
“!x:1->K.HasCard(xs:1->Exp(X,1+1),n:1->N)” 
keep this example

*)


(*
val f = “!x:1->K.HasCard(xs:1->Exp(X,1+1),n:1->N)” 

val bvs = [dest_var $ rastt "xs:1->Exp(X,1+1)",dest_var $ rastt "n:1->N"]

val ((n,s),b) = dest_forall f

val bvs' = (n,s) :: bvs

(form2IL ((n,s) :: bvs) b)

val bvs = [dest_var (rastt "x:1->K"),dest_var $ rastt "xs:1->Exp(X,1+1)",dest_var $ rastt "n:1->N"]

term2IL bvs (rastt "n:1->N") 



form2IL [dest_var $ rastt "n:1->N"]
“P o n:1->N = TRUE” 
 
want EQ(1+1) o Pa(P o n,TRUE)

val f = “P o n:1->N = TRUE” 

val bvs = [dest_var $ rastt "n:1->N"]

val (_,[t1,t2]) = dest_pred f

t1
*)

(*if see application P o n, just modify the n to the desired projection
e.g. m |-> !n. P o n & Q o m 

n m|-> P o n & Q o m

that is a pred such that P0 o Pa(n,m) = TRUE <=> P o n & Q o m
And (P o n)


Note that actual function composition such like ADD are also fobidden, because it is not ADD o Pa(m,n) function symbol application which corrsponds to variables, since ADD is not a variable.

 *)

val p11_ex = prove_store("p11_ex",
e0
(strip_tac >> qexists_tac ‘id(A)’ >> rw[])
(form_goal
 “!A.?p. id(A) = p”));

val p11_def = p11_ex |> spec_all |> ex2fsym0 "p11" ["A"] |> gen_all

(*
form2IL [dest_var $ rastt "n:1->N"]
“Even(Suc(n:1->N))” 
*)

fun form2IL bvs f = 
    case view_form f of 
        vConn("&",[f1,f2]) => 
        And (form2IL bvs f1) (form2IL bvs f2)
      | vConn("|",[f1,f2]) => 
        Or (form2IL bvs f1) (form2IL bvs f2)
      | vConn("==>",[f1,f2]) => 
        Imp (form2IL bvs f1) (form2IL bvs f2)
      | vConn("<=>",[f1,f2]) => 
        Iff (form2IL bvs f1) (form2IL bvs f2)
      | vPred("=",true,[t1,t2]) =>
        mk_pred_ap (mk_fun "Eq" [cod (sort_of t2)])
         [term2IL bvs t1,term2IL bvs t2]
      | vPred(P,_,tl) => 
        (case Binarymap.peek(!psym2IL,P) of
            SOME (p,l) => 
            if l = []  then
                mk_pred_ap p (List.map (term2IL bvs) tl)
            else let val env = match_tl essps (List.map mk_var l) 
                                        (List.map (term2IL bvs) tl) emptyvd
                     in mk_pred_ap (inst_term env p) (List.map (term2IL bvs) tl)
                 end
          | _ => raise simple_fail ("form2IL.pred: " ^ P ^ " not found"))
      | vQ ("!",n,s,b) => ALL (form2IL ((n,s) :: bvs) b)
      | vQ ("?",n,s,b) => EX (form2IL ((n,s) :: bvs) b)
      | vQ ("?!",n,s,b) => UE (form2IL ((n,s) :: bvs) b)
      | _ => raise ERR ("form2IL.ill-formed formula",[],[],[f])



(*
val _ = new_pred "HasCard" [("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)")),
                            ("n",ar_sort (mk_ob "A") N)]

val HasCard_def = store_ax("HasCard_def",
 “!X A xs n. HasCard(xs,n) <=> hasCard(X) o Pa(xs,n) = True(A)”)

val _ = new_pred "Even" [("n",ar_sort (mk_ob "A") N)]

val _ = new_fun "EVEN" (ar_sort N (rastt "1+1"),[])

val HasCard_def = store_ax("HasCard_def",
 “!X A xs n. HasCard(xs,n) <=> hasCard(X) o Pa(xs,n) = True(A)”)

hasCard(X) o Pa(xs,n) = TRUE

hasCard(X) o Pa(xs,n) = TRUE & !x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0)

form2IL [dest_var $ rastt "n:1->N"]
“P o n:1->N = TRUE” 

val bvs = [dest_var (rastt "x:1->K"),dest_var $ rastt "xs:1->Exp(X,1+1)",dest_var $ rastt "n:1->N"]

term2IL bvs (rastt "n:1->N") 

“P o n:1->N = TRUE & Q o n1:1->N = TRUE”
*)





(*

Take R: A * A -> 2. R is equivalence relation. 
Goal: 
1.form quotient object Q ~ A * A / R
2.once we have map A * X -> B.
  turn it into a map Q * X -> B
 A * X ------> B
  |            |
  |            |
 Q * X ------> B
 

 q: A ->> Q 


 avoid AC: not to use the section of q. and not to use ex2fsym.

 to go  from Q to A 

 can use section of mono. 

 Q is a subset of 2^A. really want is:


 A * X ------> B
  |            |
  |            |
 2^A * X ----> B

 \a x.b
 \as x. ?a. f a x = b

define quotient to be 

  Q -----> 1
  |        |
  |        |
  As- ---> 2

a subset of 2^A such that obtained 

is a pullback 

 maps f:A * X ->B
 to 


val  _ = new_fun "2" (ob_sort,[])
 


new_abbr ("2",[]) ("+",[ONE,ONE]) 


new_abbr ("Exp",[mk_ob "A",rastt "2"])
*)

fun sep_ex_tac (ct,asl,w) = 
    let val f = 
