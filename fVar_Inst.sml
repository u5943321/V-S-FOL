

(*does not consider same fvar with different sorts of input lists
maybe add this as a wf condiiton? *)




fun fVar_Inst1 (pair as (P,(argl:(string * sort) list,Q))) f = 
    case view_form f of
        vPred(P0,false,args0) =>
(*ListPair.map ListPair.foldl*)
(*mk_inst (zip argl args0)ListPair. [] *)
        if P0 = P then
            let val venv = match_tl essps (List.map mk_var argl) args0 emptyvd 
            in inst_form (mk_menv venv emptyfvd) Q
            end
(*if the number of arguments is wrong, or the sorts is wrong, then handle the matching exn by returning f *)
        else f
      | vConn(co,fl) => mk_conn co (List.map (fVar_Inst1 pair) fl)
      | vQ(q,n,s,b) => mk_quant q n s (fVar_Inst1 pair b)
      | vPred (_,true,_) => f




fun fVar_Inst1 (pair as (P,(argl:(string * sort) list,Q))) f = 
    case view_form f of
        vPred(P0,false,args0) =>
(*ListPair.map ListPair.foldl*)
(*mk_inst (zip argl args0)ListPair. [] *)
        if P0 = P then
            let val venv = match_tl essps (List.map mk_var argl) args0 emptyvd 
            in inst_form (mk_menv venv emptyfvd) Q
            end
(*if the number of arguments is wrong, or the sorts is wrong, then handle the matching exn by returning f *)
        else f
      | vConn(co,fl) => mk_conn co (List.map (fVar_Inst1 pair) fl)
      | vQ(q,n,s,b) => mk_quant q n s (fVar_Inst1 pair b)
      | vPred (_,true,_) => f



(*in last meeting discussed that :
P(a:mem(A),b:mem(B))

Q(c:mem(C),d:mem(D))

should not be allowed since the sort is incorrect, but if use rw, then can just use fVar to inst form. 
*)

(*ex2fsym should check that the input thm does not contain fvars*)

fun fVar_Instl l f = 
    case l of [] => f
            | pair :: t => fVar_Inst1 pair (fVar_Instl t f)

fun fVar_Inst0 l th = 
    let val (ct,asl,w) = dest_thm th
        val asl' = List.map (fVar_Instl l) asl
        val w' = fVar_Instl l w
        val vs = bigunion (pair_compare String.compare sort_compare)
                          (List.map fvf (w' :: asl'))
        val newct = HOLset.union(ct,vs)
    in mk_thm (newct,asl',w')
    end



(*

when a formula with fVar is to be insted, we first look at the free variables in the formula to be insted, and identify if there are variables which should be free after inst, but will be captured by quantifiers. if there are, rename the bound variables, so they will not be matched to the ones that should be free. 

for instance, when inst !a. P(a) with 

P: λf. isInj(f) & a in im(f).

the a 
*)






(*a bit worry for the case !n. P(n#) & n = a
when view_form, it will give
"n'" and P(n') & n = a
instead of n.

val f = “!f:A->B. isFun(f) & f = a ”

val n' = "g"

val ((n,s),b) = dest_forall f

val f0 = “(!f:A->B. f = a) <=> (!g. g = a)”
val th0 = mk_thm(fvf f0,[],f0)

val f1 = “(!f:A->B. f = a) & a = b”

basic_fconv 

*)


(*
fun rename_forall_fconv f n' = 
    case view_form f of
        vQ("!",n,s,b) => 
        let val b' = mk_forall n' s (substf ((n,s),mk_var(n',s)) b)
            val l2r = 

*)



fun newname names n = 
    if not $ HOLset.member(names,n) then n
    else newname names (n^"'") 

fun bound_names f = 
    case view_form f of
        vPred _ => HOLset.empty String.compare
      | vConn(_,fl) => bigunion String.compare (List.map bound_names fl)
      | vQ(_,n,s,b) => HOLset.add(bound_names b,n)


(*not sure if should n0 is a free variable name of f*)
fun avoid_clash f n0 names = 
    if not $ HOLset.member(names,n0) then (f,[])
    else 
        let val n' = newname names n0
            val fv0 = fvf f 
            val (name,st) = 
                case HOLset.find(fn (n1,s1) => n1 = n0) fv0 of 
                    SOME (name0,st0) => (name0,st0)
                  | _ => raise ERR
                               ("avoid_clash.no free variable with name: " ^ n0,
                                [],[],[f])
            val new = mk_var(n',st)
        in (substf ((name,st),new) f,[((n',st),mk_var(name,st))])
        end

(*there will not be two free vars with same name, so name clash only happens between bound and free, do not need to add new forbidden names *)

fun avoid_clashes f nl names l = 
    case nl of 
        [] => (f,l)
      | h :: t => 
        let val (f0,l0) = avoid_clashes f t names l
            val (f1,l1) = avoid_clash f0 h names
        in (f1,l1 @ l0)
        end


fun avoid_clashes f nl names l = 
    case nl of 
        [] => (f,[])
      | h :: t => 
        let val (f0,l0) = avoid_clashes f t names l
            val (f1,l1) = if mem h l then (f0,[]) else
                          avoid_clash f0 h names
        in (f1,l1 @ l0)
        end


(*
fun recover f l = 
    case l of [] => f
            | h :: t => substf h (recover f t)
*)


(*
fun inst_form env f = 
    case f of
        Pred(P,true,tl) => Pred(P,true,List.map (inst_term' env) tl)
      | Conn(co,fl) => Conn(co,List.map (inst_form env) fl)
      | Quant(q,n,s,b) => 
        let 
            val s' = inst_sort' env s
            val b' = inst_form env b
            val n' = rename_once_need n env 
        in 
            Quant(q,n',s',b')
        end
      | Pred(f,false,tl) => 
        (case lookup_f' env f of
             SOME f' => inst_form env f'
           | NONE => Pred(f,false,List.map (inst_term' env) tl))
*)

(*reason of not use inst_form is that if so, then 

“a' = a' & !a. P(a)” [(("a'",set_sort),mk_set "a")]
{
the bound a will be renamed to be a'.
*)

(*assume that there are no free variables in f which has different sorts but same name*)



(*

is the power of 

P(A,B) <=> A = Pow(B)

?l. length l = n & !n. n < LENGTH l ==> P(El(n),El(n+1))



*)

fun fVar_Inst' (P:string,(ssl:(string * sort) list,f)) th = 
    let val bns = bigunion String.compare
                           (List.map bound_names ((concl th) :: ant th ))
        val (f0,l) = avoid_clashes f (List.map fst (HOLset.listItems (fvf f))) bns (List.map fst ssl)
        val th0 = fVar_Inst0 [(P,(ssl,f0))] th 
    in inst_thm (mk_inst l []) th0
    end

(*the thing that fVar_Inst' does for avoid clash is that 
 once discover that there is a free variable introduced due to inst, rename the free variable so it has a name which is not possible to be captured by a bounded variable, and record the renaming in the list. after the inst, rename the free variable back to the orginal name that it should have.


fVar_Inst' ("P",([("y",mem_sort N)],“y = n:mem(N)”))
(mk_thm(essps,[],“!n:mem(N).P(n)”))


fVar_Inst_f ("P",([("y",mem_sort N)],“y = n:mem(N)”))
“!n:mem(N).P(n)”

fVar_Inst1 ("P",([("y",mem_sort N)],“y = n:mem(N)”))
“!n:mem(N).P(n)”
(mk_thm(essps,[],“!n:mem(N).P(n)”))


fVar_Inst1 ("P",([("n",mem_sort N)],“y = n:mem(N)”))
“!n:mem(N).P(n)”

val P = "P"
val ssl = [("y",mem_sort N)];
val f = “y = n:mem(N)”
val th= mk_thm(essps,[],“!n:mem(N).P(n)”)


val f = “P(n) <=> y = n”
val th = mk_thm(fvf f, [], f)
*)



fun fVar_Inst l th = 
    case l of 
        [] => th
      | h :: t => fVar_Inst t (fVar_Inst' h th)

(*N_ind_P |> rewr_rule [th]*)


(*


“a' = a' & !a. P(a)” [(("a'",set_sort),mk_set "a")]

recover f' l'
  
val(f',l') = 
avoid_clashes “b = a & !a. P(a)” ["a","b"]
(HOLset.add(HOLset.add(HOLset.empty String.compare,"a"),"b"))
[] 

val n0 = "a"

val names = 
 (HOLset.add(HOLset.empty String.compare,"a"))


*)(*

val f = “P(n) <=> y = n”
val th = mk_thm(fvf f, [], f)

(thenfc(rewr_fconv th,rewr_fconv th)) 
rewr_fconv th “P(m)”

rewr_fconv th “y = m”

top_depth_fconv no_conv (rewr_fconv th) “P(m)”

basic_fconv no_conv (rewr_fconv th) “P(m) & n = y”

rewr_fconv th “P(m)”




val f0 = concl N_ind_P

top_depth_fconv no_conv (rewr_fconv (spec_all th)) f0

top_depth_fconv no_conv (rewr_fconv (spec_all th)) f1

top_depth_fconv no_conv (rewr_fconv (spec_all th)) f2

top_depth_fconv no_conv (rewr_fconv (spec_all th)) f3 

top_depth_fconv no_conv (rewr_fconv (spec_all th)) f4


conj_fconv (rewr_fconv (spec_all th)) “P(a:mem(N)) & P(Suc(a))”

sub_fconv no_conv (rewr_fconv (spec_all th)) “P(a:mem(N)) & P(Suc(a))”


top_depth_fconv no_conv 

repeatfc

fun fVarsl fl = bigunion String.compare (List.map fVars fl)
fun part_fmatch partfn th f = 
    let 
        val fvd = match_form (fvfl (ant th)) (fVarsl (ant th)) (partfn th) f mempty
    in 
        inst_thm fvd th
    end

fun rewr_fconv th = part_fmatch (fst o dest_dimp o concl) th



val f = “!n.P(n) <=> Eval(u1:N->X,n) = Eval(u2,n)”
val th = mk_thm(fvf f,[],f)


basic_fconv no_conv (rewr_fconv (add_assum “!n:mem(N). P(n) <=> P(n)” (spec_all th)))
“P(a:mem(N)) & P(Suc(a))”


 “P(a:mem(N))”

“P(a:mem(N)) & P(Suc(a))”


wrong 


f4 = P(n) ==> P(Eval(SUC, n)): form

# val it =
   {(X : set), (n : mem(N)), (u1 : rel(N, X)), (u2 : rel(N, X))}, 
   |- P(n) <=> Eval(u1, n) = Eval(u2, n): thm




 N_ind_P |> rewr_rule[spec_all th]

rewr_fconv (spec_all th) “P(O)”

*)



(*


val f = “?R:A->B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)”

val f0 = “P(a,b:mem(B)) <=> ~(a:mem(A) = a)”
val th = (add_assum “!n:mem(N). P(n) <=> P(n)” (mk_thm(fvf f0,[],f0)))

*)



(*
val f0 = “P(n) <=> Sub(Suc(m),Suc(n)) = Sub(m,n)”
val th = (add_assum “!n:mem(N). P(n) <=> P(n)” (mk_thm(fvf f0,[],f0)))

uex_fconv (rewr_fconv th) “?!n. P(n:mem(N))”

 fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
“Holds(R1:A->B,a,b)”))] 
(AX1 |> qspecl [‘A’,‘B’]) |> uex_expand

val f0 = “P(a,b) <=> Holds(R1:A->B,a,b)”

val th = add_assum “!a:mem(A) b:mem(B). P(a,b) <=> P(a,b)”
 (mk_thm (fvf f0,[],f0))



val f1 = “P(a:mem(A),b:mem(B)) <=> (!a0 b0. Holds(R:C->D,a0,b0) ==> Q(a,b))”

val f = concl (AX1 |> qspecl [‘A’,‘B’])


val f0 = “!a b.P(a,b) <=> Holds(R1:A->B,a,b)”
val localax = mk_thm(fvf f0,[],f0)
val th1 = assume f0
(AX1 |> qspecl [‘A’,‘B’] |> rewr_rule[th1]) |> prove_hyp localax

(AX1 |> qspecl [‘A’,‘B’]) |> rewr_rule[th]

top_depth_fconv no_conv (rewr_fconv th) 
“!a b. Holds(R:A->B,a,b) <=> P(a,b)”

top_depth_fconv no_conv (rewr_fconv th) 
“?R. !a b. Holds(R:A->B,a,b) <=> P(a,b)”

top_depth_fconv no_conv (rewr_fconv th) 
“?!R. !a b. Holds(R:A->B,a,b) <=> P(a,b)”


basic_fconv no_conv (rewr_fconv th) 
“!B.?!R. !a b. Holds(R:A->B,a,b) <=> P(a,b)”

sub_fconv no_conv (top_depth_fconv no_conv (rewr_fconv th)) 
“!B.?!R. !a b. Holds(R:A->B,a,b) <=> P(a,b)”



forall_iff ("B",set_sort) $

(top_depth_fconv no_conv (rewr_fconv th)) 
“?!R. !a b. Holds(R:A->B,a,b) <=> P(a,b)”


forall_fconv (top_depth_fconv no_conv (rewr_fconv th)) 
“!B.?!R. !a b. Holds(R:A->B,a,b) <=> P(a,b)”


no_conv (top_depth_fconv no_conv (rewr_fconv th)) 
“!B.?!R. !a b. Holds(R:A->B,a,b) <=> P(a,b)”

val 

fun spec_fVar pdeff th = 
    let val localax = mk_thm(fvf pdeff,[],pdeff) 
        val th0 = rewr_rule[localax] th
    in th0
    end

val f0 = “!a b.P(a,b) <=> Holds(R1:A->B,a,b)”

val pdeff = f0; val th = AX1 |> qspecl [‘A’,‘B’]

AX1 |> rewr_rule[th]

val f0 = “P <=> Q”

val th = assume f0
val th = mk_thm(essps,[],f0)


rewr_fconv th “R”

val (G,fl,f) = cg $
e0
(dimp_tac >> rpt strip_tac 
>-- (first_x_assum irule >> arw[]) >>
first_x_assum irule >> arw[]

 (qby_tac ‘A & B’ >> arw[]) first_x_assum drule >> arw[])
(form_goal
“(A & B ==> C) <=> (A ==> B ==> C)”)
first_x_assum mapfilter



*)

(*
val f = concl N_ind_P
val f0 = “P(n) <=> Sub(Suc(m),Suc(n)) = Sub(m,n)”
val th = (add_assum “!n:mem(N). P(n) <=> P(n)” (mk_thm(fvf f0,[],f0)))

basic_fconv no_conv (rewr_fconv (spec_all th)) f

“P(a,b) <=> ~(a = a)”

N_ind_P |> rewr_rule[th] 

val th = mk_thm(essps,[],“(?!a.P(a)) <=> ?a. P(a) & (!b. P(b) ==> b = a)”)

val f0 = “?!a.Q(a)”


val th = mk_thm(essps,[],“P <=> Q(a)”)

val f0 = “R(a)”

rewr_fconv (th) f0


basic_fconv no_conv (rewr_fconv (add_assum “!n:mem(N). P(n) <=> P(n)” (spec_all th)))

*)

(*
val (ct,asl,w) = cg $
e0
(assume_tac l0 >> strip_tac >>
 first_x_assum (qspecl_then [‘A’] assume_tac) >>
 first_assum (fn th => assume_tac (uex_def $ concl th)) >> fs[])
(form_goal
“!A. ?!R:1->A.!a:mem(A). Holds(R,dot,a) <=> P(a)”)

w |> rewr_fconv (uth)

*)



(*
fVar_Inst_f ("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "A"))],“~(a:mem(A) = a)”)) (concl (AX1 |> qspecl [‘A’,‘A’]))


fVar_Inst_f ("P",([("y",mem_sort (mk_set "A")),("z",mem_sort (mk_set "A"))],“y = a0:mem(A) & z = a0”)) (concl (AX1 |> qspecl [‘A’,‘A’]))
*)
