val AX4 = new_ax
“?N0 O0:mem(N0) S0:N0->N0. isFun(S0) & (!n:mem(N0). ~(Eval(S0,n) = O0)) & 
 !n m. Eval(S0,n) = Eval(S0,m) <=> n = m”

(*is it fair to add the constriction that no formula variable can occur in the input of define_pred, if not, we can write:
!n. inN(n) <=>
    P(n0) &
    (!n0. P(n0) ==> P(Eval(S0,n0))) ==>
    P(n)

!n.
    P(n0) &
    (!n0. P(n0) ==> P(Eval(S0,n0))) ==>
    P(n) <=> inN(n)

wrong because the "invisiable" quantifier of P is always on the outmost.

think a problem is that if we allow the definition to include fvars,
then we can make something like:

|- !n. inN(n) <=> P(n) as a thm

and inst the P(n) to be ~inN(n)

this is !n. F. but not equivalent to F. it just says there should be no member such that inN, maybe not problematic, just weird.

*)

fun ind_with th (ct,asl,w) = 
    let 
        val th1 = undisch th
        val (bvs,conc) = dest_forall (concl th1)
        val (ante,con) = dest_imp conc
                         handle _ => (TRUE,conc)
        val (P,args) = dest_fvar con
        val (b,qvs) = strip_forall w
        val (gante,gcon) = dest_imp b
                           handle _ => (TRUE,b)
        val th2 = fVar_Inst_th (P,(qvs,gcon)) th
    in match_mp_tac th2 (ct,asl,w)
    end

fun spec_fVar pdef th = 
    let val (l,r) = dest_dimp pdef 
        val (P,vars0) = dest_fvar l
        val vars = List.map dest_var vars0
    in fVar_Inst_th (P,(vars,r)) th
    end

val inN_def = define_pred
“!n:mem(N0). inN(n) <=>
(!P.IN(O0,P) &
 (!n0. IN(n0,P) ==> IN(Eval(S0,n0),P)) ==> 
 IN(n,P))”


val inN_ind0 = 
    inN_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “inN(n)”
            |> gen_all
            |> disch_all 
            |> gen_all

local 
val l = allE (rastt "N0") IN_def_P_expand
in
val inN_ind = prove_store("inN_ind",
e0
(strip_tac >> rw[inN_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !n:mem(N0). IN(n,P0) <=> P(n)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “(P(O0) &
   (!n0. P(n0) ==> P(Eval(S0,n0))) ==>
  !n.inN(n) ==> P(n))”))
end

val inN_rules = prove_store("inN_rules",
e0
(strip_tac >-- (rw[inN_def] >> rpt strip_tac) >>
 rw[inN_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “inN(O0) & 
  (!n. inN(n) ==> inN(Eval(S0,n)))”));

val inN_rules_step = inN_rules |> conjE2


(*inN_cases there is a case that rw does not work and do not know why*)
val inN_cases = prove_store("inN_cases",
e0
(strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!n0. inN(n0) ==> (n0 = O0 |
  (?a. n0 = Eval(S0,a) & inN(a)))’
 >-- (strip_tac >> arw[]) >>
 ind_with inN_ind >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexists_tac ‘O0’ >> rw[inN_rules]) >>
 disj2_tac >> qexists_tac ‘n0'’ >> rw[] >>
 arw[] >> match_mp_tac inN_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[inN_rules] >>
 arw[] >> match_mp_tac inN_rules_step >> arw[])
(form_goal
 “!n0. inN(n0) <=> (n0 = O0 |
  (?a. n0 = Eval(S0,a) & inN(a)))”));



val FI_def = define_pred 
“!X xs:mem(Pow(X)). FI(xs) <=> 
 !P. (IN(Empty(X),P) &
      (!xs. IN(xs,P)==> !x.IN(Ins(x,xs),P))) ==>
     IN(xs,P)”



val FI_ind0 = 
    FI_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “FI(xs:mem(Pow(X)))”
            |> gen_all
            |> disch_all 
            |> gen_all

local 
val l = allE (rastt "Pow(X)") IN_def_P_expand
in
val FI_ind = prove_store("FI_ind",
e0
(strip_tac >> strip_tac >> rw[FI_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !xs:mem(Pow(X)). IN(xs,P0) <=> P(xs)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “!X.(P(Empty(X)) &
   (!xs. P(xs) ==> !x:mem(X).P(Ins(x,xs)))) ==>
  !xs:mem(Pow(X)).FI(xs) ==> P(xs)”))
end

val FI_rules = prove_store("FI_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[FI_def] >> rpt strip_tac) >>
 rw[FI_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “!X. FI(Empty(X))& 
     (!xs:mem(Pow(X)). FI(xs) ==> !x. FI(Ins(x,xs)))”));

val FI_rules_step = FI_rules |> spec_all |> conjE2


val FI_cases = prove_store("FI_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!xs. FI(xs) ==> (xs = Empty(X) |
  (?xs0 x0. xs = Ins(x0,xs0) & FI(xs0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (FI_ind |> allE (rastt "X")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘Empty(X)’,‘x’] >> 
     rw[FI_rules]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘xs'’,‘x’] >> rw[] >> arw[] >>
 match_mp_tac FI_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[FI_rules] >>
 arw[] >> match_mp_tac FI_rules_step >> arw[])
(form_goal
 “!X xs. FI(xs) <=> (xs = Empty(X) |
  (?xs0 x0. xs = Ins(x0,xs0) & FI(xs0)))”));



(*necessary to take a term in product rather then a pair? so Cd has only one argument?*)
(*
val Cd_def = define_pred
“!X xsn:mem(Pow(X) * N). Cd(xsn) <=>
(!P.IN(Pair(Empty(X),O),P) &
   (!xsn0 x. IN(xsn0,P) & ~IN(x,Fst(xsn0)) ==> 
    IN(Pair(Ins(x,Fst(xsn0)),Suc(Snd(xsn0))),P)) ==> 
 IN(xsn,P))”

if use this, then the cases will be:

Cd(xsn) <=> ?... long. 

*)

val Cd_def = define_pred
“!X xs:mem(Pow(X)) n. Cd(xs,n) <=>
(!P.IN(Pair(Empty(X),O),P) &
   (!xs0 n0 x. IN(Pair(xs0,n0),P) & ~IN(x,xs0) ==>
   IN(Pair(Ins(x,xs0),Suc(n0)),P)) ==> 
 IN(Pair(xs,n),P))”


val Cd_ind0 = 
    Cd_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “Cd(xs:mem(Pow(X)),n)”
            |> qgen ‘n’ |> qgen ‘xs’
            |> disch_all 
            |> gen_all 

val Fst_of_Pair = prove_store("Fst_of_Pair",
e0
(rw[GSYM Fst_def,Eval_p1_Pair])
(form_goal
 “!A B a:mem(A) b:mem(B). Fst(Pair(a,b)) = a”));


val Snd_of_Pair = prove_store("Snd_of_Pair",
e0
(rw[GSYM Snd_def,Eval_p2_Pair])
(form_goal
 “!A B a:mem(A) b:mem(B). Snd(Pair(a,b)) = b”));


local 
val l = allE (rastt "Pow(X) * N") IN_def_P_expand |>
spec_fVar “P(xsn) <=> P(Fst(xsn),Snd(xsn))”
in
val Cd_ind = prove_store("Cd_ind",
e0
(strip_tac >> rw[Cd_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !xs:mem(Pow(X)) n. IN(Pair(xs,n),P0) <=> P(xs,n)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> (* simply arw[] works for previous cases but not for this, since the pattern is different *)
 qby_tac ‘!xs n. P(xs,n) <=> IN(Pair(xs,n),s)’ 
 >-- (rpt strip_tac >> 
      first_x_assum (qspecl_then [‘Pair(xs',n')’] assume_tac) >>
      fs[Fst_of_Pair,Snd_of_Pair]) >>
 arw[])
(form_goal 
 “!X.(P(Empty(X),O) &
     (!xs n x:mem(X). 
      P(xs,n) & (~IN(x,xs)) ==> 
      P(Ins(x,xs),Suc(n)))) ==>
  !xs:mem(Pow(X)) n.Cd(xs,n) ==> P(xs,n)”))
end

val Cd_rules = prove_store("Cd_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[Cd_def] >> rpt strip_tac) >>
 rw[Cd_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> arw[] (*to eliminate the ~IN(x,xs) in the goal, previously did not have it*) >> 
 first_x_assum match_mp_tac >> arw[])
(form_goal
 “!X. Cd(Empty(X),O)& 
     (!xs:mem(Pow(X)) n x. Cd(xs,n) & ~(IN(x,xs)) ==> 
     Cd(Ins(x,xs),Suc(n)))”));

val Cd_rules_step = Cd_rules |> spec_all |> conjE2


val Cd_cases = prove_store("Cd_cases",
e0
(strip_tac >> strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!xs n. Cd(xs,n) ==> ((xs = Empty(X) & n = O) |
  (?xs0 n0 x0. ~(IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) &
  Cd(xs0,n0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (Cd_ind |> allE (rastt "X")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘Empty(X)’,‘O’,‘x’] >> 
     rw[Cd_rules] >> (*previously the rw [..._rules] solve the goal, but here require the condition not in empty*) 
     rw[Empty_property]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘xs'’,‘n'’,‘x’] >> rw[] >> arw[] >>
 match_mp_tac Cd_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[Cd_rules] >>
 arw[] >> match_mp_tac Cd_rules_step >> arw[])
(form_goal
 “!X xs:mem(Pow(X)) n. Cd(xs,n) <=> ((xs = Empty(X) & n = O) |
  (?xs0 n0 x0. ~(IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) &
   Cd(xs0,n0)))”));




val isL_def = define_pred 
“!A nas:mem(Pow(N * A)). isL(nas) <=>
(!P.IN(Empty(N * A),P) &
   (!nas0. IN(nas0,P) ==>
    !a.IN(Ins(Pair(CARD(nas0),a),nas0),P)) ==> 
 IN(nas,P))”

val isL_ind0 = 
    isL_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “isL(nas:mem(Pow(N * A)))”
            |> gen_all  
            |> disch_all 
            |> gen_all 


local 
val l = allE (rastt "Pow(N * A)") IN_def_P_expand
in
val isL_ind = prove_store("isL_ind",
e0
(strip_tac >> rw[isL_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !nas:mem(Pow(N * A)). IN(nas,P0) <=> P(nas)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “!A.(P(Empty(N * A)) &
   (!nas. P(nas) ==> !a:mem(A).P(Ins(Pair(CARD(nas),a),nas)))) ==>
  !nas:mem(Pow(N * A)).isL(nas) ==> P(nas)”))
end


val isL_rules = prove_store("isL_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[isL_def] >> rpt strip_tac) >>
 rw[isL_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “!A. isL(Empty(N * A))& 
     (!nas:mem(Pow(N * A)). isL(nas) ==> 
              !a. isL(Ins(Pair(CARD(nas),a),nas)))”));

val isL_rules_step = isL_rules |> spec_all |> conjE2



val isL_cases = prove_store("isL_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!nas. isL(nas) ==> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (isL_ind |> allE (rastt "A")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] (*figure out why the arw work here*)>> 
      qexistsl_tac [‘Empty(N * A)’,‘a’] >> 
      rw[isL_rules]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘nas'’,‘a’] >> rw[] >> arw[] >>
 match_mp_tac isL_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[isL_rules] >>
 arw[] >> match_mp_tac isL_rules_step >> arw[])
(form_goal
 “!A nas. isL(nas) <=> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))”));




val _ = new_sort "fun" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "fun" "~>"

fun fun_sort A B = mk_sort "fun" [A,B]
fun mk_func f A B = mk_var(f,fun_sort A B)
val _ = EqSorts := "fun" :: (!EqSorts)


val _ = new_fun "App" (mem_sort (mk_set "B"),
                       [("f",fun_sort (mk_set "A") (mk_set "B")),
                       ("a",mem_sort (mk_set "A"))]);

val rel2fun = store_ax("rel2fun",
“!A B R:A->B. isFun(R) ==> ?!f:A~>B. !a b. App(f,a) = b <=> Holds(R,a,b)”)


val Nf_def = define_pred 
“!X x0:mem(X) t:X~>X n x. Nf(x0,t,n,x) <=>
(!P.IN(Pair(O,x0),P) &
   (!n x. IN(Pair(n,x),P) ==>
          IN(Pair(Suc(n),App(t,x)),P)) ==> 
 IN(Pair(n,x),P))”


val Nf_ind0 = 
    Nf_def |> spec_all |> dimpl2r |> undisch
           |> strip_all_and_imp 
           |> disch “Nf(x0:mem(X), t:X~>X, n:mem(N), x:mem(X))”
           |> gen_all  
           |> disch_all 
           |> qgen ‘P’ |> qgen ‘t’ |> qgen ‘x0’ |> qgen ‘X’

local 
val l = allE (rastt "N * X") IN_def_P_expand
             |> spec_fVar “P(a:mem(N * X)) <=> P(Fst(a),Snd(a))”
in
val Nf_ind = prove_store("Nf_ind",
e0
(strip_tac >> strip_tac >> strip_tac >> rw[Nf_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !n:mem(N) x:mem(X). IN(Pair(n,x),P0) <=> P(n,x)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> strip_tac >> strip_tac >>
 first_x_assum (qsspecl_then [‘Pair(n',x')’] assume_tac) >>
 (*need spec, different from all above.*)
 fs[Fst_of_Pair,Snd_of_Pair])
(form_goal 
 “!X x0:mem(X) t:X~>X.
   (P(O,x0) &
   (!n:mem(N) x:mem(X). P(n,x) ==> 
    P(Suc(n),App(t,x)))) ==>
  !n:mem(N) x:mem(X).Nf(x0,t,n,x) ==> P(n,x)”))
end

val Nf_rules = prove_store("Nf_rules",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac 
 >-- (rw[Nf_def] >> rpt strip_tac) >>
 rw[Nf_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “!X x0:mem(X) t:X~>X. Nf(x0,t,O,x0) & 
     (!n x. Nf(x0,t,n,x) ==> Nf(x0,t,Suc(n),App(t,x)))”));


val Nf_rules_step = Nf_rules |> spec_all |> conjE2


val Nf_cases = prove_store("Nf_cases",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!n x. Nf(x0,t,n,x) ==> ((n = O & x = x0) |
  (?pn px. n = Suc(pn) & x = App(t,px) & Nf(x0,t,pn,px)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (Nf_ind |> qspecl [‘X’,‘x0:mem(X)’,‘t:X~>X’]) >> 
 strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘O’,‘x0’] >> 
     rw[Nf_rules]) >>
 disj2_tac >> 
 qexistsl_tac [‘n'’,‘x'’] >> rw[] >> arw[] >>
 match_mp_tac Nf_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[Nf_rules] >>
 arw[] >> match_mp_tac Nf_rules_step >> arw[])
(form_goal
 “!X x0:mem(X) t:X~>X n x. Nf(x0,t,n,x) <=> 
  ((n = O & x = x0) |
   (?pn px. n = Suc(pn) & x = App(t,px) & Nf(x0,t,pn,px)))”));



val Lf_def = define_pred 
“!A X x0:mem(X) t:A * X~>X l:mem(List(A)) x:mem(X). Lf(x0,t,l,x) <=>
(!P.IN(Pair(Nil(A),x0),P) &
   (!l x. IN(Pair(l,x),P) ==>
          !a:mem(A). IN(Pair(CONS(a,l),App(t,Pair(a,x))),P)) ==> 
 IN(Pair(l,x),P))”


val Lf_ind0 = 
    Lf_def |> spec_all |> dimpl2r |> undisch
           |> strip_all_and_imp 
           |> disch “Lf(x0:mem(X), t: A * X~>X, 
                        l:mem(List(A)), x:mem(X))”
           |> gen_all  
           |> disch_all 
           |> qgen ‘P’ |> qgen ‘t’ |> qgen ‘x0’ |> qgen ‘X’
           |> qgen ‘A’

local 
val l = allE (rastt "List(A) * X") IN_def_P_expand
             |> spec_fVar “P(a:mem(List(A) * X)) <=> P(Fst(a),Snd(a))”
in
val Lf_ind = prove_store("Lf_ind",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac 
 >> rw[Lf_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !l:mem(List(A)) x:mem(X). IN(Pair(l,x),P0) <=> P(l,x)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> strip_tac >> strip_tac >>
 first_x_assum (qsspecl_then [‘Pair(l',x')’] assume_tac) >>
 (*need spec, different from all above.*)
 fs[Fst_of_Pair,Snd_of_Pair])
(form_goal 
 “!A X x0:mem(X) t:A * X~>X.
   (P(Nil(A),x0) &
    (!l x. P(l,x) ==> 
     !a:mem(A).P(CONS(a,l),App(t,Pair(a,x))))) ==>
  !l:mem(List(A)) x:mem(X).Lf(x0,t,l,x) ==> P(l,x)”))
end

val Lf_rules = prove_store("Lf_rules",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac
 >-- (rw[Lf_def] >> rpt strip_tac) >>
 rw[Lf_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “!A X x0:mem(X) t:A * X~>X. Lf(x0,t,Nil(A),x0) & 
  (!l x. Lf(x0,t,l,x) ==> !a.Lf(x0,t,CONS(a,l),App(t,Pair(a,x))))”));


val Lf_rules_step = Lf_rules |> spec_all |> conjE2


val Lf_cases = prove_store("Lf_cases",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!l x. Lf(x0,t,l,x) ==> ((l = Nil(A) & x = x0) |
  (?a pl px. l = CONS(a,pl) & x = App(t,Pair(a,px)) & 
             Lf(x0,t,pl,px)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (Lf_ind |> qspecl [‘A’,‘X’,‘x0:mem(X)’,‘t:A * X~>X’]) >> 
 strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘a’,‘Nil(A)’,‘x0’] >> 
     rw[Lf_rules]) >>
 disj2_tac >> 
 qexistsl_tac [‘a'’,‘l'’,‘x'’] >> rw[] >> arw[] >>
 match_mp_tac Lf_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[Lf_rules] >>
 arw[] >> match_mp_tac Lf_rules_step >> arw[])
(form_goal
 “!A X x0:mem(X) t:A * X~>X l:mem(List(A)) x. Lf(x0,t,l,x) <=> 
  ((l = Nil(A) & x = x0) |
   (?a pl px. l = CONS(a,pl) & x = App(t,Pair(a,px)) &
              Lf(x0,t,pl,px)))”));













val FI_rules_step = FI_rules |> spec_all |> conjE2




val Nf_def = define_pred 
“!X x0:mem(X) t:X->X . Nf(x0,t,n,x) <=>
 isFun(t) & 
(!P.IN(Pair(O,x0),P) &
   (!n x. IN(Pair(n,x),P) ==>
    !a.IN(Pair(Suc(n)),nas0),P)) ==> 
 IN(nas,P))”


val isL_ind0 = 
    isL_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “isL(nas:mem(Pow(N * A)))”
            |> gen_all  
            |> disch_all 
            |> gen_all 









val FI_cases = prove_store("FI_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!nas. isL(nas) ==> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (isL_ind |> allE (rastt "A")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] rw[(assume “nas' = Empty(N * A)”)]
     fconv_tac (top_depth_fconv 
(rewr_conv (assume “nas' = Empty(N * A)”))
no_fconv) >>

 fconv_tac (basic_fconv 
(rewr_conv (assume “nas' = Empty(N * A)”))
no_fconv) 

(*top_depth_fconv cannot, basic can do it.*)

“Ins(Pair(CARD(nas':mem(Pow(N * A))), a:mem(A)), nas')”

      


arw[])))
(form_goal
 “!A nas. isL(nas) <=> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))”));



(*
top_depth_fconv 
(first_conv 
(List.map rewr_conv
[assume “xs = xs':mem(Pow(X))”,
 assume “n = n0:mem(N)”]))
no_fconv
“Cd(xs:mem(Pow(X)),n:mem(N))”

top_depth_fconv 
(first_conv 
(List.map rewr_conv
[assume “xs = xs':mem(Pow(X))”(*,
 assume “n = n0:mem(N)” *)]))
no_fconv
“Cd(xs:mem(Pow(X)),n:mem(N))”


top_depth_fconv 
(rewr_conv (assume “nas' = Empty(N * A)”))
no_fconv
“Ins(Pair(CARD(nas':mem(Pow(N * A))), a:mem(A)), nas')”

basic_fconv 
(rewr_conv (assume “nas' = Empty(N * A)”))
no_fconv
“Ins(Pair(CARD(nas':mem(Pow(N * A))), a:mem(A)), nas')”

because nas' is wrapped in some function which has one input...


bugbugbug

*)



val FI_cases = val (ct,asl,w) = cg $
e0
(strip_tac >> strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!xs n. Cd(xs,n) ==> ((xs = Empty(X) & n = O) |
  (?xs0 n0 x0. ~(IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) &
  Cd(xs0,n0)))’
 >-- (strip_tac >> arw[])))
(form_goal
 “!X xs:mem(Pow(X)) n. Cd(xs,n) <=> ((xs = Empty(X) & n = O) |
  (?xs0 n0 x0. ~(IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) &
   Cd(xs0,n0)))”)




(*
alt of Cd_ind
(form_goal 
 “!X.(P(Pair(Empty(X),O)) &
     (!xs n x:mem(X). 
      P(Pair(xs,n)) & (~IN(x,xs)) ==> 
      P(Pair(Ins(x,xs),Suc(n))))) ==>
  !xs:mem(Pow(X)) n.Cd(xs,n) ==> P(xs,n)”))


maybe use the idea that a subset of A * B is a subset of A and a subset of B, hence may turn the IN(Pair...) into IN(...,A) & IN(...,B)

!(P : mem(Pow(Pow(X) * N))).
               IN(Pair(Empty(X), O), P#) &
               (!(xs0 : mem(Pow(X)))  (n0 : mem(N))  (x : mem(X)).
                   IN(Pair(xs0#, n0#), P#) & ~IN(x#, xs0#) ==>
                   IN(Pair(Ins(x#, xs0#), Suc(n0#)), P#)) ==>
               IN(Pair(xs, n), P#)

*)



val f= “xs' = Ins(x0:mem(X), xs0)”
val th = mk_thm(fvf f,[],f)

basic_fconv (rewr_conv (assume “xs' = Ins(x0:mem(X), xs0)”))
no_fconv
“?xs0:mem(Pow(X)). Ins(x:mem(X),xs':mem(Pow(X)))”

top_depth_fconv (rewr_conv (assume “xs' = Ins(x0:mem(X), xs0)”))
no_fconv
“?xs0:mem(Pow(X)). Ins(x:mem(X),xs':mem(Pow(X)))”



top_depth_fconv (rewr_conv (assume “xs' = Ins(x0:mem(X), xs0)”))
no_fconv
“?xs0:mem(Pow(X)). Ins(x:mem(X),xs':mem(Pow(X))) = a”

top_depth_conv (rewr_conv (assume “xs' = Ins(x0:mem(X), xs0)”))
(rastt "Ins(x:mem(X),xs':mem(Pow(X)))")


redepth_fconv (rewr_conv (assume “xs' = Ins(x0:mem(X), xs0)”))
no_fconv
“Ins(x:mem(X),xs':mem(Pow(X))) = a”


arg_conv (rewr_conv (assume “xs' = Ins(x0:mem(X), xs0)”))
(rastt "Ins(x:mem(X),xs':mem(Pow(X)))")

arg_conv (try_conv (rewr_conv (assume “xs' = Ins(x0:mem(X), xs0)”)))
(rastt "Ins(x:mem(X),xs':mem(Pow(X)))")


The one in top_depth_conv does not have try_conv.Should I add it?



(*

val f= “xs' = Ins(x0:mem(X), xs0)”
val th = mk_thm(fvf f,[],f)

top_depth_fconv (rewr_conv th)
no_fconv
“Ins(x:mem(X),xs':mem(Pow(X))) = a”
*)



top_depth_fconv (rewr_conv th)
no_fconv
“?xs0:mem(Pow(X)). Ins(x:mem(X),xs':mem(Pow(X))) = a”



basic_fconv (rewr_conv th)
no_fconv
“?xs0:mem(Pow(X)). Ins(x:mem(X),xs':mem(Pow(X)))”




(*parser bug 
“?xs0. Ins(x,xs')”

parsed as 

  (?(xs0 : set). Ins(x, xs')) 

*)

val inN_cases = prove_store("inN_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!xs. FI(xs) ==> (xs = Empty(X) |
  (?xs0 x0. xs = Ins(x0,xs0) & FI(xs0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (FI_ind |> allE (rastt "X")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘Empty(X)’,‘x’] >> 
     rw[FI_rules]) >>
 disj2_tac >> arw[]


qexists_tac ‘n0'’ >> rw[] >>
 arw[] >> match_mp_tac inN_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[inN_rules] >>
 arw[] >> match_mp_tac inN_rules_step >> arw[])
(form_goal
 “!X xs. FI(xs) <=> (xs = Empty(X) |
  (?xs0 x0. xs = Ins(x0,xs0) & FI(xs0)))”));







(*
local 
val l = allE (rastt "N0") IN_def_P_expand
val inN_def_alt = prove_store("inN_def_alt",
e0
(strip_tac >> rw[inN_def] >> dimp_tac >> strip_tac >--
 (qsuff_tac
 ‘?P0. !n:mem(N0). IN(n,P0) <=> P(n)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[]) >>
 
 strip_tac >>
 pop_assum (assume_tac o (spec_fVar “P(a) <=> IN(a,P)”))
 strip_tac >> 
qsuff_tac
 ‘?P0. !n:mem(N0). IN(n,P0) <=> P(n)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[] )
(form_goal 
     “!n. inN(n) <=> 
    (P(O0) &
     (!n0. P(n0) ==> P(Eval(S0,n0))) ==>
     P(n))”))
*)
