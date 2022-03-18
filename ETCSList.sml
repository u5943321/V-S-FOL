(*
collect the set of all sets of of sets of (n,a) pairs such that 
{} in the set 
if l is in in the set, then for every a\in A, l ∪ (CARD l,a) is in the set

*)



val Lists_cond_ex = prove_store("Lists_cond_ex",
e0
(rpt strip_tac >> 
 qby_tac
 ‘?P0. !ls. P0 o ls = TRUE <=> IN(Empty(N * A),ls)’ >--
 (qexists_tac ‘Mem(Exp(N * A, 1 + 1)) o 
             Pa(Empty(N * A) o To1(Exp(Exp(N * A, 1 + 1), 1 + 1)),id(Exp(Exp(N * A, 1 + 1), 1 + 1)))’
 >> rw[o_assoc,Pa_distr,IN_def] >>
 once_rw[one_to_one_id] >> rw[idL,idR,True1TRUE]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘?P1. !ls. P1 o ls = TRUE <=> 
 (!l:1-> Exp(N * A,1+1). IN(l,ls) ==>
 !a. IN(Ins(Pa(CARD(l),a),l), ls))’ >-- 
 (strip_tac >>
 qexists_tac ‘And(P0,P1)’ >>
 once_rw[GSYM And_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> 
 once_rw[CONJ_def] >> arw[]) >>
 pop_assum (K all_tac) >>
 qsuff_tac
 ‘?P2. !l ls. P2 o Pa(l,ls) = TRUE <=> 
  (IN(l,ls) ==>
   !a:1->A. IN(Ins(Pa(CARD(l),a),l), ls))’ >--
 (strip_tac >> qexists_tac ‘ALL(P2)’ >>
  once_rw[GSYM ALL_def] >> once_rw[o_assoc] >>
  once_rw[All_def] >> arw[]) >>
 qby_tac
 ‘?P3. !l:1-> Exp(N * A,1+1) ls. P3 o Pa(l,ls) = TRUE <=> 
  IN(l,ls)’
 >-- (qexists_tac ‘Mem(Exp(N * A,1+1))’ >>
      rw[IN_def,True1TRUE]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘?P4. !a l:1-> Exp(N * A,1+1) ls.
 P4 o Pa(a,Pa(l,ls)) = TRUE <=> 
 IN(Ins(Pa(CARD(l),a),l), ls)’ 
 >-- (strip_tac >> 
      qexists_tac ‘Imp(P3,ALL(P4))’ >>
      once_rw[GSYM Imp_def] >> once_rw[o_assoc] >>
      once_rw[Pa_distr] >> once_rw[IMP_def] >>
      rw[ALL_property] >> arw[]) >>
 pop_assum (K all_tac) >>
 rw[IN_def,True1TRUE] >>
 qexists_tac ‘ Mem(Exp(N * A, 1 + 1)) o Pa(Ins(
 Pa
 (CARD(p32(A,Exp(N * A,1+1),Exp(Exp(N * A, 1 + 1), 1 + 1)))
 ,
 p31(A,Exp(N * A,1+1),Exp(Exp(N * A, 1 + 1), 1 + 1))
  )
  ,
 p32(A,Exp(N * A,1+1),Exp(Exp(N * A, 1 + 1), 1 + 1)))
 ,
 p33(A,Exp(N * A,1+1),Exp(Exp(N * A, 1 + 1), 1 + 1))
)
’ >>
 rw[Pa3_def,GSYM Ins_def] >> rw[Pa_distr,o_assoc] >>
 rw[p31_of_Pa3,p32_of_Pa3,p33_of_Pa3] >>
 once_rw[GSYM CARD_def] >> rw[o_assoc,Pa_distr] >>
 once_rw[p32_of_Pa3] >> rw[])
(form_goal “!A.?P. !ls.P o ls = TRUE <=>
IN(Empty(N * A),ls) &
 !l. IN(l,ls) ==>
 !a. IN(Ins(Pa(CARD(l),a),l), ls)”));

(*sets contain the set of lists as a subset*)
val cLists_def = Lists_cond_ex |>  spec_all
                               |> ex2fsym0 "cLists" ["A"]
                               |> gen_all
                               |> store_as "cLists_def";

val Lists_ex = prove_store("Lists_ex",
e0
(strip_tac >> qexists_tac ‘BIGINTER(Exp(N * A,1+1)) o 
           Tp1(cLists(A))’ >> rw[])
(form_goal
 “!A. ?la. BIGINTER(Exp(N * A,1+1)) o 
           Tp1(cLists(A)) = la”));

val Lists_def = Lists_ex |> spec_all |> ex2fsym0 "Lists" ["A"]
                           |> gen_all
                           |> store_as "Lists_def";

val isList_ex = prove_store("isList_ex",
e0
(strip_tac >> qexists_tac ‘Tp0(Lists(A))’ >> rw[])
(form_goal “!A. ?isl. Tp0(Lists(A)) = isl”));


val isList_def = isList_ex |> spec_all |> ex2fsym0 "isList" ["A"]
                           |> gen_all
                           |> store_as "isList_def";

val isList_property = prove_store("isList_property",
e0
(rpt strip_tac >>(*
 rw[GSYM isList_def,GSYM Lists_def,GSYM Tp0_def,o_assoc,Pa_distr,
    idL,one_to_one_id,idR,BIGINTER_property,GSYM Tp1_def,
    Ev_of_Tp_el',p12_of_Pa,Ev_of_el,cLists_def,IN_o]
*)
 once_rw[GSYM isList_def] >>
 once_rw[GSYM Lists_def] >> 
 once_rw[GSYM Tp0_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> rw[o_assoc,idL] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 rw[BIGINTER_property] >> 
 rw[GSYM Tp1_def] >> rw[Ev_of_Tp_el',p12_of_Pa,o_assoc] >>
 rw[Ev_of_el] >> 
 once_rw[cLists_def] >> rw[IN_o] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum (qspecl_then [‘Tp1(P)’] assume_tac) >>
     fs[Tp0_Tp1_inv] >> rfs[]) >>
 last_x_assum (qsspecl_then [‘Tp0(s0)’] assume_tac) >> rfs[]
)
(form_goal
 “!A l. isList(A) o l = TRUE <=> 
  (!P.( P o Empty(N * A) = TRUE &
      (!l0. P o l0 = TRUE ==>
        !a. P o Ins(Pa(CARD(l0),a),l0) = TRUE)) ==> 
      P o l = TRUE)”));

val List_def = pred_subset_ex' 
                 |> sspecl [rastt "isList(A)"]
                 |> ex2fsym0 "List" ["A"]
                 |> ex2fsym0 "LI" ["A"]
                 |> gen_all
                 |> store_as "List_def";

val List_def1= List_def |> spec_all |> conjE2
                        |> allE ONE
                        |> rewr_rule[True1TRUE]
                        |> gen_all
                        |> store_as "List_def1";

val isList_Empty = prove_store("isList_Empty",
e0
(rw[isList_property] >> rpt strip_tac >> arw[])
(form_goal
 “!A. isList(A) o Empty(N * A) = TRUE”));

val isList_cons = prove_store("isList_cons",
e0
(rw[isList_property] >> rpt strip_tac >>
 first_x_assum (qspecl_then [‘P’] assume_tac) >> rfs[] >>
 first_x_assum irule >> arw[])
(form_goal
 “!A l. isList(A) o l = TRUE ==> 
  !a. isList(A) o Ins(Pa(CARD(l),a),l) = TRUE”));

val Nil_ex = prove_store("Nil_ex",
e0
(rw[GSYM List_def,isList_Empty,True1TRUE])
(form_goal
 “!A.?nil:1->List(A). Empty(N * A) = LI(A) o nil”));

val Nil_def = Nil_ex |> spec_all |> ex2fsym0 "Nil" ["A"]
                     |> gen_all
                     |> GSYM
                     |> store_as "Nil_def";

val Cons_rel_ex = prove_store("Cons_ex",
e0
(strip_tac >> qexists_tac 
 ‘Eq(Exp(N * A,1+1)) o Pa(
  Ins(
      Pa(
         CARD(LI(A) o p2(A,List(A)) o p1(A * List(A),List(A)))
         , 
         p1(A,List(A)) o p1(A * List(A),List(A)))
      , 
      LI(A) o p2(A,List(A)) o p1(A * List(A),List(A)))
  ,
  LI(A) o p2(A * List(A),List(A)))’ >>
 rw[o_assoc] >> rw[Pa_distr] >> rw[Eq_property_TRUE] >>
 rw[o_assoc] >> rw[p12_of_Pa] >>
 rw[GSYM Ins_def,o_assoc,p12_of_Pa,Pa_distr] >>
 rw[GSYM CARD_def,o_assoc,p12_of_Pa,Pa_distr])
(form_goal
 “!A. ?R: (A * List(A)) * List(A) -> 1+1.
 !a0 l0 l. R o Pa(Pa(a0,l0),l) = TRUE <=> 
 Ins(Pa(CARD(LI(A) o l0),a0),LI(A) o l0) = LI(A) o l ”));

val Crel_def = Cons_rel_ex |> spec_all |> ex2fsym0 "Crel" ["A"]
                           |> gen_all 
                           |> store_as "Crel_def";

val Cons_ex = prove_store("Cons_ex",
e0
(strip_tac >>
 assume_tac Rel2Ar' >>
 first_x_assum (qsspecl_then [‘Crel(A)’] assume_tac) >>
 qby_tac
 ‘!al:1-> A * List(A). ?!l. Crel(A) o Pa(al,l) = TRUE’
 >-- (strip_tac >> uex_tac >> 
      qsspecl_then [‘al’] (x_choosel_then ["a0","l0"] assume_tac)
      has_components >>
      fs[] >> rw[Crel_def] >>
      qby_tac ‘isList(A) o (LI(A) o l0) = TRUE’
      >-- (rw[List_def1] >> qexists_tac ‘l0’ >> rw[]) >>
      drule isList_cons  >>
      first_x_assum (qspecl_then [‘a0’] assume_tac) >>
      drule $ iffLR List_def1 >>
      pop_assum (x_choosel_then ["l"] assume_tac) >>
      qexists_tac ‘l’ >> arw[] >>
      rpt strip_tac >> irule $ iffLR Mono_def >>
      qexistsl_tac [‘Exp(N * A,1+1)’,‘LI(A)’] >> arw[List_def]) >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["cons"] assume_tac) >>
 qexists_tac ‘cons’ >> arw[] >> 
 rw[Crel_def])
(form_goal
 “!A. ?cons:A * List(A) ->List(A). 
  !a0:1->A l0 l:1->List(A). cons o Pa(a0,l0) = l <=> 
  Ins(Pa(CARD(LI(A) o l0),a0),LI(A) o l0) = LI(A) o l”));

val Cons_def = Cons_ex |> spec_all |> ex2fsym0 "Cons" ["A"]
                       |> gen_all
                       |> store_as "Cons_def";


val CONS_ex = prove_store("CONS_ex",
e0
(rpt strip_tac >> qexists_tac ‘Cons(A) o Pa(a0,l0)’ >> rw[])
(form_goal
 “!X a0:X->A l0. ?l. Cons(A) o Pa(a0,l0) = l”));

val CONS_def = CONS_ex |> spec_all |> ex2fsym0 "CONS" ["a0","l0"]
                       |> gen_all |> store_as "CONS_def";


val cRf_ex = prove_store("Rf_ex",
e0
(rpt strip_tac >>
 qby_tac
 ‘?P0. !ss. P0 o ss = TRUE <=> IN(Pa(Nil(A), x), ss)’
 >-- (qexists_tac 
     ‘Mem(List(A) * X) o Pa(Pa(Nil(A), x) o To1(Exp(List(A) * X,1+1)),
      id(Exp(List(A) * X,1+1)))’
      >> rw[IN_def1] >> rw[o_assoc,Pa_distr,idL] >>
      once_rw[one_to_one_id] >> rw[idR]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘?P1. !ss. P1 o ss = TRUE <=> 
  !l x. IN(Pa(l, x), ss) ==>
  !a. IN(Pa(Cons(A) o Pa(a, l), t o Pa(a, x)), ss)’ 
 (*here if forgot strip the P0, so P0 is not in context, still be able to qexists on CONJ o Pa(P0,P1), check this*)
 >-- (strip_tac >> qexists_tac ‘CONJ o Pa(P0,P1)’ >> 
      arw[o_assoc,Pa_distr,CONJ_def]) >>
 qsuff_tac
 ‘?P2. !x:1->X l ss. 
  P2 o Pa(x,Pa(l,ss)) = TRUE <=>
   IN(Pa(l, x), ss) ==>
  !a:1->A. IN(Pa(Cons(A) o Pa(a, l), t o Pa(a, x)), ss)’
 >-- (strip_tac >>
      qexists_tac ‘ALL(ALL(P2))’ >>
      rw[ALL_property] >> arw[]) >>
 qby_tac
 ‘?P3. !x:1->X l:1->List(A) ss.
  P3 o Pa(x,Pa(l,ss)) = TRUE <=> IN(Pa(l,x),ss)’
 >-- (qexists_tac 
     ‘Mem(List(A) * X) o 
      Pa(Pa(p32(X,List(A),Exp(List(A) * X,1+1)),
            p31(X,List(A),Exp(List(A) * X,1+1))), p33(X,List(A),Exp(List(A) * X,1+1)))’ >>
     rw[Pa3_def,o_assoc,Pa_distr,
       p31_of_Pa3,p32_of_Pa3,p33_of_Pa3] >> rw[GSYM IN_def1]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘?P4. !a:1->A x:1->X l:1->List(A) ss. 
  P4 o Pa4(a,x,l,ss) = TRUE <=>
  IN(Pa(Cons(A) o Pa(a, l), t o Pa(a, x)), ss)’
 >-- (strip_tac >> qexists_tac ‘Imp(P3,ALL(P4))’ >>
      rw[GSYM Imp_def,o_assoc,Pa_distr,IMP_def] >>
      arw[] >>
      arw[ALL_property,Pa4_def]) >>
 qexists_tac ‘
 Mem(List(A) * X) o Pa(
Pa (CONS(p41(A,X,List(A),Exp(List(A) * X,1+1)),
    p43(A,X,List(A),Exp(List(A) * X,1+1)))
    ,
    t o Pa(p41(A,X,List(A),Exp(List(A) * X,1+1)),
           p42(A,X,List(A),Exp(List(A) * X,1+1))))
,
 p44(A,X,List(A),Exp(List(A) * X,1+1))
)’ >>
 rw[GSYM CONS_def,o_assoc,Pa_distr,
    p41_of_Pa4,p42_of_Pa4,p43_of_Pa4,p44_of_Pa4] >>
 rw[GSYM IN_def1])
(form_goal
 “!X x:1->X A t:A * X ->X.
  ?P:Exp(List(A) * X,1+1) -> 1 + 1.
  !ss. P o ss = TRUE <=> 
       IN(Pa(Nil(A), x),ss) & 
       (!l:1-> List(A) x:1->X. IN(Pa(l,x),ss) ==> 
             !a. IN(Pa(Cons(A) o Pa(a,l), t o Pa(a,x)),ss) )”));

val cRf_def = cRf_ex |> spec_all |> ex2fsym0 "cRf" ["x","t"]
                     |> qgen ‘t’ |> qgen ‘A’
                     |> gen_all 
                     |> store_as "cRf_def";

val Rf_ex = prove_store("Rf_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Tp0(BIGINTER(List(A) * X) o Tp1(cRf(x,t)))’ >> rw[])
(form_goal
 “!X x:1->X A t:A * X ->X.
  ?R.Tp0(BIGINTER(List(A) * X) o Tp1(cRf(x,t))) = R”));

val Rf_def = Rf_ex |> spec_all |> ex2fsym0 "Rf" ["x","t"]
                   |> qgen ‘t’ |> qgen ‘A’
                   |> gen_all 
                   |> store_as "Rf_def";


val isList_ind =
    isList_property |> iffLR
                    |> strip_all_and_imp
                    |> disch “isList(A) o l = TRUE”
                    |> gen_all
                    |> disch_all |> gen_all
                    |> store_as "isList_ind";

val LI_Mono = List_def |> spec_all |> conjE1
                       |> gen_all
                       |> store_as "LI_Mono";


val List_ind = prove_store("List_ind",
e0
(assume_tac isList_ind >> rpt strip_tac >>
 qby_tac
 ‘?P0:Exp(N * A,1+1) -> 1+1.
  !ss. P0 o ss = TRUE <=>
  ?l:1->List(A). ss = LI(A) o l & P o l = TRUE’
 >-- (qexists_tac 
      ‘EX(And(Eq(Exp(N * A,1+1)) o 
              Pa(p2(List(A), Exp(N * A,1+1)),
                 LI(A) o p1(List(A), Exp(N * A,1+1))) ,
              P o p1(List(A), Exp(N * A,1+1))))’ >>
      rw[EX_property] >>
      rw[GSYM And_def,o_assoc,Pa_distr,p12_of_Pa] >>
      rw[CONJ_def,Eq_property_TRUE]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac 
 ‘P0 o LI(A) o l = TRUE’ 
 >-- (arw[] >> rpt strip_tac >>
      qsuff_tac ‘l = l'’ >-- (strip_tac >> arw[]) >>
      qspecl_then [‘A’] assume_tac LI_Mono >>
      drule $ iffLR Mono_def >> first_x_assum drule >>
      arw[]) >>
 first_assum irule >> rw[List_def1] >> strip_tac (* 2 *)
 >-- (qexists_tac ‘l’ >> rw[]) >>
 arw[] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘Nil(A)’ >> arw[Nil_def]) >>
 qexists_tac ‘CONS(a,l')’ >> first_assum drule >> arw[] >>
 rw[GSYM Cons_def] >> rw[GSYM CONS_def]
 )
(form_goal
 “!A P. P o Nil(A) = TRUE & 
        (!l. P o l = TRUE ==> !a. P o CONS(a,l) = TRUE) ==>
        !l. P o l = TRUE”));


val Rf_property = prove_store("Rf_property",
e0
(once_rw[GSYM Rf_def] >> 
 once_rw[GSYM Tp0_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[o_assoc] >>
 once_rw[idL] >> once_rw[one_to_one_id] >>
 once_rw[idR] >> once_rw[BIGINTER_property] >>
 once_rw[GSYM Tp1_def] >>
 once_rw[Ev_of_Tp_el'] >> once_rw[o_assoc] >>
 once_rw[p1_of_Pa] >> once_rw[Mem_def] >> once_rw[GSYM IN_def1] >>
 once_rw[cRf_def] >> once_rw[CONS_def] >> rpt strip_tac >>
 first_assum irule >> first_assum irule >> arw[])
(form_goal
 “!X x:1->X A t:A * X ->X. Rf(x,t) o Pa(Nil(A),x) = TRUE & 
   !l x0. Rf(x,t) o Pa(l,x0) = TRUE ==> 
   !a. Rf(x,t) o Pa(CONS(a,l), t o Pa(a,x0)) = TRUE
  ”));





val Rf_min = prove_store("Rf_min",
e0
(once_rw[GSYM Rf_def] >> 
 once_rw[GSYM Tp0_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[o_assoc] >>
 once_rw[idL] >> once_rw[one_to_one_id] >>
 once_rw[idR] >> once_rw[BIGINTER_property] >>
 once_rw[GSYM Tp1_def] >>
 once_rw[Ev_of_Tp_el'] >> once_rw[o_assoc] >>
 once_rw[p1_of_Pa] >> once_rw[Mem_def] >> once_rw[GSYM IN_def1] >>
 once_rw[cRf_def]  >> rpt strip_tac >>
 first_x_assum (qsspecl_then [‘Tp1(P)’] assume_tac) >>
 fs[IN_o,Tp0_Tp1_inv] >>
 first_assum irule >> arw[CONS_def])
(form_goal
 “!X x:1->X A t:A * X ->X P. P o Pa(Nil(A),x) = TRUE & 
   (!l x0. P o Pa(l,x0) = TRUE ==> 
          !a. P o Pa(CONS(a,l), t o Pa(a,x0)) = TRUE) ==> 
   !l x0. Rf(x,t) o Pa(l,x0) = TRUE ==> P o Pa(l,x0) = TRUE
  ”));

val CONS_NOTNIL = prove_store("CONS_NOTNIL",
e0
(rpt strip_tac >> ccontra_tac >>
 fs[GSYM CONS_def,Cons_def,Nil_def] >> 
 fs[Ins_NONEMPTY])
(form_goal
 “!A a l. ~(CONS(a,l) = Nil(A))”));

val Rf_Nil_unique = prove_store("Rf_Nil_unique",
e0
(rpt strip_tac >> ccontra_tac >> 
 qsuff_tac ‘?P. P o Pa(Nil(A),x) = TRUE & 
   (!l x0. P o Pa(l,x0) = TRUE ==> 
    !a. P o Pa(CONS(a,l), t o Pa(a,x0)) = TRUE) & 
    ~(P o Pa(Nil(A),x0) = TRUE)’ >--
 (strip_tac >>
  qsspecl_then [‘x’,‘t’,‘P’] assume_tac Rf_min>>
  qby_tac ‘P o Pa(Nil(A), x0) = TRUE’
  >-- (first_x_assum irule>> arw[]) >>
  fs[]) >>
 qsuff_tac
 ‘?P. !l1 x1. P o Pa(l1,x1) = TRUE <=> 
  Rf(x,t) o Pa(l1,x1) = TRUE & ~(l1 = Nil(A) & x1 = x0)’
 >-- (strip_tac >> qexists_tac ‘P’ >>
      arw[] >> strip_tac (* 2 *)
      >-- (rw[Rf_property] >> dflip_tac >> arw[]) >>
      (*should not need the thing between the rpt strip ans fs. should be done by arw*)
      rpt strip_tac >> fs[] >>
      first_assum (qsspecl_then [‘l’,‘x0'’] assume_tac) >> 
      fs[] >>
      qsspecl_then [‘x’,‘t’] strip_assume_tac Rf_property >>
      last_x_assum (K all_tac) >>
      first_x_assum rev_drule >> arw[] >>
      rw[CONS_NOTNIL]) >>
 qexists_tac
 ‘And(Rf(x,t),
      Not
      (And(Eq(List(A)) o 
           Pa(p1(List(A),X),Nil(A) o To1(List(A) * X)),
           Eq(X) o 
           Pa(p2(List(A),X), x0 o To1(List(A) * X)) )))’ >>
 rw[GSYM And_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[GSYM Not_def] >> once_rw[o_assoc] >>
 once_rw[NEG_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> rw[TRUE_xor_FALSE] >> once_rw[CONJ_def] >>
 rw[o_assoc,Pa_distr] >> once_rw[one_to_one_id] >>
 rw[idR,p12_of_Pa] >> rw[Eq_property_TRUE])
(form_goal
 “!X x:1->X A t:A * X ->X x0. Rf(x,t) o Pa(Nil(A),x0) = TRUE ==> x0 = x”));


val Rf_CONS = Rf_property |> spec_all |> conjE2
                          |> gen_all
                          |> store_as "Rf_CONS";


val Ins_eq_eq = prove_store("Ins_eq_eq",
e0
(rpt strip_tac >-- (ccontra_tac >>
 qsuff_tac ‘~(IN(a2,Ins(a2,s2)))’
 >-- rw[IN_Ins] >>
 qsuff_tac ‘~(IN(a2,Ins(a1,s1)))’
 >-- arw[] >>
 rw[IN_Ins] >> arw[] >> dflip_tac >> first_x_assum accept_tac) >>
 rw[IN_EXT] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘IN(x,Ins(a1,s1))’ >-- arw[IN_Ins] >> rfs[] >>
      fs[IN_Ins] >> pop_assum (assume_tac o GSYM) >> fs[]) >>
 qpick_x_assum ‘Ins(a1, s1) = Ins(a2, s2)’ (assume_tac o GSYM) >>
 qby_tac ‘IN(x,Ins(a2,s2))’ >-- arw[IN_Ins] >>
 rfs[] >> fs[IN_Ins] >> pop_assum (assume_tac o GSYM) >> fs[]
 )
(form_goal
 “!A a1:1->A s1 a2 s2. ~(IN(a1,s1)) & ~(IN(a2,s2)) & ~(IN(a1,s2)) & ~(IN(a2,s1)) & 
 Ins(a1,s1) = Ins(a2,s2) ==> a1 = a2 & s1 = s2”));

val FINITE_Empty = isFinite_Empty|> rewr_rule[GSYM FINITE_def] 
                                 |> store_as "FINITE_Empty";

val FINITE_Ins = isFinite_Insert |> rewr_rule[GSYM FINITE_def]
                                 |> store_as "FINITE_Ins";

val Del_Empty = prove_store("Del_Empty",
e0
(rw[IN_EXT,IN_Del,NOT_IN_Empty,IN_def1])
(form_goal
 “!X x:1->X. Del(x,Empty(X)) = Empty(X)”));

val isFinite_Del0 = prove_store("isFinite_Del0",
e0
(strip_tac >>
 qby_tac
 ‘?P. !xs. (isFinite(X) o xs = TRUE & !x. isFinite(X) o Del(x,xs) = TRUE) <=> P o xs = TRUE’ 
 >-- (qexists_tac ‘And(isFinite(X),ALL(isFinite(X) o Del(p1(X,Exp(X,1+1)),p2(X,Exp(X,1+1)))))’ >> rw[GSYM And_def,o_assoc,Pa_distr,CONJ_def,p12_of_Pa,ALL_property,GSYM Del_def]) >>
 pop_assum strip_assume_tac >>
 arw[] >> match_mp_tac Finite_ind >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Del_Empty,isFinite_Empty] >> strip_tac >>
 strip_tac >> drule isFinite_Insert >> arw[] >> rpt strip_tac >>
 cases_on “x = x':1->X” >-- 
 (arw[] >> cases_on “IN(x':1->X,xs)”
 >-- (drule $iffLR Ins_absorb >> arw[]) >>
 drule Del_Ins >> arw[]) >>
 drule Del_Ins_SWAP >> arw[] >> 
 last_x_assum (qspecl_then [‘x'’] assume_tac) >>
 drule isFinite_Insert>> arw[])
(form_goal
 “!X xs. isFinite(X) o xs = TRUE ==> isFinite(X) o xs = TRUE & 
   !x. isFinite(X) o Del(x,xs) = TRUE”));

val FINITE_Del = prove_store("FINITE_Del",
e0
(rw[FINITE_def] >> rpt strip_tac >> drule isFinite_Del0 >>
 arw[])  
(form_goal
 “!X xs:1->Exp(X,1+1). FINITE(xs) ==> !x. FINITE(Del(x,xs))”));

val Card_FINITE = Card_def |> spec_all |> conjE1 |> gen_all
                           |> store_as "Card_FINITE";

val Card_INFINITE = Card_def |> spec_all |> conjE2 |> gen_all
                           |> store_as "Card_INFINITE";

val CARD_Empty = prove_store("CARD_Empty",
e0
(rw[GSYM CARD_def] >> assume_tac FINITE_Empty >> strip_tac >>
 first_x_assum $ qspecl_then [‘X’] assume_tac >>
 drule Card_FINITE >> arw[] >> rw[hasCard_Empty])
(form_goal
 “!X. CARD(Empty(X)) = O”));

val CARD_Ins = prove_store("CARD_Ins",
e0
(rw[GSYM CARD_def] >> rpt strip_tac >> drule Card_FINITE >> 
 first_x_assum (qspecl_then [‘Card(X) o xs’] assume_tac) >> fs[] >>
 drule hasCard_Ins >> first_x_assum drule >>
 drule FINITE_Ins >> 
 first_x_assum $ qspecl_then [‘x’] assume_tac >> drule Card_FINITE >>
 arw[])
(form_goal
 “!X xs. FINITE(xs) ==> 
         !x:1->X. ~(IN(x,xs)) ==> CARD(Ins(x,xs)) = Suc(CARD(xs))”));

val CARD_Del = prove_store("CARD_Del",
e0
(rpt strip_tac >> rw[GSYM CARD_def] >>
 drule FINITE_Del >> drule Card_FINITE >> 
 first_x_assum (qspecl_then [‘x’] assume_tac) >> 
 drule Card_FINITE >> arw[] >> 
 last_x_assum (qspecl_then [‘Card(X) o xs’] assume_tac) >> fs[] >>
 drule hasCard_Del >> fs[] >> first_x_assum drule >> arw[])
(form_goal “!X xs:1->Exp(X,1+1). FINITE(xs) ==> 
 !x. IN(x,xs) ==> CARD(Del(x,xs)) = Pre(CARD(xs))”));

val isList_Finite = prove_store("isList_Finite",
e0
(rw[FINITE_def] >> strip_tac >> match_mp_tac isList_ind >> 
 rw[isFinite_Empty] >> rpt strip_tac >> drule isFinite_Insert >> arw[])
(form_goal “!A l. isList(A) o l = TRUE ==> FINITE(l)”));

val List_LI_Finite = prove_store("List_LI_Finite",
e0
(assume_tac isList_Finite >> rpt strip_tac >> first_x_assum irule >>
 rw[List_def1] >> qexists_tac ‘l’ >> rw[])
(form_goal “!A l:1-> List(A). FINITE(LI(A) o l)”));


val isList_CARD_NOTIN0 = prove_store("isList_CARD_NOTIN0",
e0
(strip_tac >> 
 qby_tac ‘?P. !l. P o l = TRUE <=>  
          (isList(A) o l = TRUE & !n:1->N a:1->A. IN(Pa(n,a),l) ==> Lt(n,CARD(l)))’  >-- (qexists_tac 
     ‘And
     (isList(A),
      ALL (ALL (Imp (Mem(N * A) o Pa(Pa(p32(A,N,Exp(N * A,1+1)),p31(A,N,Exp(N * A,1+1))), p33(A,N,Exp(N * A,1+1))),Char(LT) o Pa(p32(A,N,Exp(N * A,1+1)),CARD(p33(A,N, Exp(N * A,1+1))))) )))’
      >> rw[GSYM And_def,GSYM CARD_def,GSYM Imp_def,o_assoc,CONJ_def,
            GSYM p31_def,GSYM p32_def,GSYM p33_def,p12_of_Pa,Pa_distr,
            ALL_property,IMP_def] >>
         rw[IN_def1,Lt_def1]) >>
 pop_assum (strip_assume_tac o GSYM) >> arw[] >>
 match_mp_tac isList_ind >>
 pop_assum (assume_tac o GSYM) >> arw[NOTIN_Empty] >> rpt strip_tac (* 3 *)>--
 rw[isList_Empty] >-- (drule isList_cons >> arw[]) >>
 fs[IN_Ins] (* 2 *)
 >-- (fs[Pa_eq_eq] >>
     qby_tac ‘~(IN(Pa(CARD(l0), a),l0))’ >-- 
     (ccontra_tac >> first_x_assum drule >> fs[Lt_def]) >>
     drule isList_Finite >> drule CARD_Ins >> first_x_assum drule >> 
     arw[] >> rw[Lt_Suc]) >>
 first_x_assum drule >> drule isList_Finite >> drule CARD_Ins >>
 cases_on “IN(Pa(CARD(l0), a:1->A), l0)”
 >-- (drule $ iffLR Ins_absorb >> arw[]) >>
 drule CARD_Ins >> first_x_assum drule >> arw[] >>
 irule Lt_trans >>
 qexists_tac ‘CARD(l0)’ >> arw[Lt_Suc])
(form_goal
 “!A l. isList(A) o l = TRUE ==> isList(A) o l = TRUE & 
        !n a. IN(Pa(n,a),l) ==> Lt(n,CARD(l))”));




val isList_CARD_NOTIN = prove_store("isList_CARD_NOTIN",
e0
(rpt strip_tac >> drule isList_CARD_NOTIN0 >> pop_assum strip_assume_tac >>
 first_x_assum drule >> arw[])
(form_goal
 “!A l. isList(A) o l = TRUE ==> 
        !n a. IN(Pa(n,a),l) ==> Lt(n,CARD(l))”));

val Cons_Mono = prove_store("Cons_Mono",
e0
(rw[Mono_def] >> rpt strip_tac >> irule FUN_EXT >> strip_tac >>
 qby_tac ‘Cons(A) o g o a = Cons(A) o h o a’ 
 >-- arw[GSYM o_assoc] >>
 qsspecl_then [‘g o a’] (x_choosel_then ["a1","l1"] assume_tac) has_components>>
 qsspecl_then [‘h o a’] (x_choosel_then ["a2","l2"] assume_tac) has_components>>
 fs[Cons_def] >>
 assume_tac Cons_def >>
 first_x_assum $ qsspecl_then [‘a2’,‘l2’,‘Cons(A) o Pa(a2,l2)’] assume_tac >>
 fs[] >>
 qby_tac ‘Ins(Pa(CARD(LI(A) o l1), a1), LI(A) o l1) = 
          Ins(Pa(CARD(LI(A) o l2), a2), LI(A) o l2)’
 >-- arw[] >>
 qsuff_tac
 ‘Pa(CARD(LI(A) o l1), a1) = Pa(CARD(LI(A) o l2), a2) & 
  LI(A) o l1 = LI(A) o l2’
 >-- (rw[Pa_eq_eq] >> strip_tac >> arw[] >>
     irule $ iffLR Mono_def >> qexistsl_tac [‘Exp(N * A,1+1)’,‘LI(A)’] >>
     arw[LI_Mono]) >>
 irule Ins_eq_eq >> arw[] >> 
 qby_tac ‘isList(A) o LI(A) o l1 = TRUE’
 >-- (rw[List_def1] >> qexists_tac ‘l1’ >> rw[]) >> 
 qby_tac ‘~IN(Pa(CARD(LI(A) o l1), a1), LI(A) o l1)’ >-- 
 (ccontra_tac >> drule isList_CARD_NOTIN >> first_x_assum drule >>
  fs[Lt_def]) >>
 qby_tac ‘isList(A) o LI(A) o l2 = TRUE’
 >-- (rw[List_def1] >> qexists_tac ‘l2’ >> rw[]) >> 
 qby_tac ‘~IN(Pa(CARD(LI(A) o l2), a2), LI(A) o l2)’ >-- 
 (ccontra_tac >> drule isList_CARD_NOTIN >> first_x_assum drule >>
  fs[Lt_def]) >> 
 arw[] >> 
 qby_tac ‘CARD(LI(A) o l2) = CARD(LI(A) o l1)’
 >-- (drule Del_Ins >> rev_drule Del_Ins >>
     qby_tac ‘FINITE(Ins(Pa(CARD(LI(A) o l2), a2), LI(A) o l2))’ >--
     (irule FINITE_Ins >> rw[List_LI_Finite])  >>
     drule CARD_Del >>
     first_x_assum (qspecl_then [‘Pa(CARD(LI(A) o l2), a2)’] assume_tac) >>
     fs[IN_Ins] >> rfs[] >>
     qby_tac ‘FINITE(Ins(Pa(CARD(LI(A) o l1), a1), LI(A) o l1))’ >-- 
     (irule FINITE_Ins >> rw[List_LI_Finite]) >>
     drule CARD_Del >>
     first_x_assum (qspecl_then [‘Pa(CARD(LI(A) o l1), a1)’] assume_tac) >>
     fs[IN_Ins] >> rfs[]) >>
 strip_tac (* 2 *)
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >> 
      ccontra_tac >> drule isList_CARD_NOTIN >> first_x_assum drule >>
      fs[Lt_def]) >>
 arw[] >> ccontra_tac >> rev_drule isList_CARD_NOTIN >> first_x_assum drule >>
 fs[Lt_def])
(form_goal
 “!A.Mono(Cons(A))”));

val CONS_eq_eq = prove_store("CONS_eq_eq",
e0
(strip_tac >> 
 qspecl_then [‘A’] assume_tac Cons_Mono >>
 fs[Mono_def,GSYM CONS_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 first_x_assum drule >> fs[Pa_eq_eq])
(form_goal
 “!A a1:1->A l1:1->List(A) a2 l2.
  CONS(a1,l1) = CONS(a2,l2) <=> (a1 = a2 & l1 = l2) ”));


val CONS_or_Nil = prove_store("CONS_or_Nil",
e0
(strip_tac >>
 qby_tac ‘?P. !l. P o l = TRUE <=> (l = Nil(A) | ?a0 l0. l = CONS(a0,l0))’
 >-- (qexists_tac
      ‘Or(Eq(List(A)) o Pa(id(List(A)),Nil(A) o To1(List(A))),
          EX(EX(Eq(List(A)) o Pa(p33(List(A),A,List(A)), CONS(p32(List(A),A,List(A)),p31(List(A),A,List(A))) ) )))’ >>
      rw[GSYM Or_def, o_assoc,Pa_distr,DISJ_def] >>
      rw[EX_property] >> rw[GSYM p31_def,GSYM p32_def,GSYM p33_def] >>
      rw[Pa_distr,o_assoc,p12_of_Pa,Eq_property_TRUE] >>
      rw[GSYM CONS_def,p12_of_Pa,o_assoc,Pa_distr] >> once_rw[one_to_one_id] >>
      rw[idR,idL]) >>
 pop_assum (assume_tac o GSYM) >> pop_assum strip_assume_tac >>
 arw[] >> irule List_ind >> pop_assum (assume_tac o GSYM) >>
 arw[] >> rpt strip_tac (* 2 *)
 >-- (disj2_tac >> qexistsl_tac [‘a’,‘l’] >> rw[]) >>
 disj2_tac >> qexistsl_tac [‘a’,‘l’] >> rw[])
(form_goal
 “!A l:1-> List(A). l = Nil(A) | ?a0 l0. l = CONS(a0,l0)”));

val Rf_Cons_back = prove_store("Rf_Cons_back",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 qby_tac
 ‘?P. !l0:1->List(A) x0:1->X. P o Pa(l0,x0) = TRUE <=>
  (Rf(x,t) o Pa(l0,x0) = TRUE & 
  !a:1->A l1. l0 = CONS(a,l1) ==> 
  ?x1:1->X. Rf(x,t) o Pa(l1,x1) = TRUE & x0 = t o Pa(a,x1))’ >-- (
 qsuff_tac
 ‘?P1. !l0:1->List(A) x0:1->X. P1 o Pa(l0,x0) = TRUE <=>
  (!a:1->A l1. l0 = CONS(a,l1) ==> 
  ?x1:1->X. Rf(x,t) o Pa(l1,x1) = TRUE & x0 = t o Pa(a,x1))’
 >-- (strip_tac >> qexists_tac ‘And(Rf(x,t),P1)’ >> arw[GSYM And_def,CONJ_def,o_assoc,Pa_distr]) >>
 qexists_tac 
 ‘ALL(ALL(Imp(Eq(List(A)) o Pa(p43(List(A),A,List(A),X),CONS(p42(List(A),A,List(A),X),p41(List(A),A,List(A),X))), 
              EX(And(Rf(x,t) o 
                     Pa(p52(X,List(A),A,List(A),X), p51(X,List(A),A,List(A),X)), 
                     Eq(X) o 
                     Pa(p55(X,List(A),A,List(A),X), t o Pa(p53(X,List(A),A,List(A),X),p51(X,List(A),A,List(A),X)))))
              )
         )
      )’ >>
 once_rw[GSYM p54_def] >> once_rw[GSYM p53_def] >> once_rw[GSYM p51_def] >>
 once_rw[GSYM p52_def] >>
 once_rw[GSYM p55_def] >> once_rw[GSYM p43_def] >> once_rw[GSYM p42_def] >>
 once_rw[GSYM p41_def] >>
 once_rw[ALL_property] >>  once_rw[ALL_property] >>
 once_rw[GSYM Imp_def] >> once_rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[IMP_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[Eq_property_TRUE] >>
 once_rw[EX_property] >>
 once_rw[GSYM And_def] >> once_rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[CONJ_def] >> once_rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[Eq_property_TRUE] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[GSYM CONS_def] >> 
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[p12_of_Pa] >> rw[])>>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘!l0 x0.Rf(x, t) o Pa(l0, x0) = TRUE ==> P o Pa(l0,x0) = TRUE’
 >-- (rpt strip_tac >> first_x_assum drule >> rfs[] >>
      first_x_assum drule >> arw[]) >>
 match_mp_tac Rf_min >> arw[] >> 
 rw[GSYM CONS_NOTNIL] >> rpt strip_tac (* 3 *)
 >-- rw[Rf_property] 
 >-- (drule Rf_CONS >> arw[]) >>
 (*cases_on
 “?a2:1->A l2. l = CONS(a2,l2)” *)
 qsspecl_then [‘l’] strip_assume_tac CONS_or_Nil >-- (* 2 *)
 (fs[CONS_eq_eq] >> qexists_tac ‘x0’ >> arw[]) >>
 fs[CONS_eq_eq] >> qexists_tac ‘x0’ >> arw[])
(form_goal
 “!X x:1->X A t:A * X ->X l0 x0. Rf(x,t) o Pa(l0,x0) = TRUE ==>
  Rf(x,t) o Pa(l0,x0) = TRUE & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Rf(x,t) o Pa(l1,x1) = TRUE & x0 = t o Pa(a,x1)”));

val Rf_unique = prove_store("Rf_unique",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 qby_tac
 ‘?P. !l0 x0. P o Pa(l0,x0) = TRUE <=>
 (!x'. Rf(x,t) o Pa(l0,x') = TRUE ==> x' = x0)’
 >-- (qexists_tac ‘ALL(Imp(Rf(x,t) o Pa(p32(X,List(A),X),p31(X,List(A),X)),Eq(X) o Pa(p31(X,List(A),X),p33(X,List(A),X))))’ >>
      rw[ALL_property] >> rw[GSYM Imp_def,o_assoc,Pa_distr,IMP_def] >>
      rw[Pa3_def,p31_of_Pa3,p32_of_Pa3,p33_of_Pa3] >> rw[Eq_property_TRUE])>> pop_assum strip_assume_tac >>
 qsuff_tac 
 ‘!l0 x0. Rf(x,t) o Pa(l0,x0) = TRUE ==> P o Pa(l0,x0) = TRUE’ 
 >-- arw[] >>
 match_mp_tac Rf_min >> arw[] >> 
 strip_tac (* 2 *)
 >-- rw[Rf_Nil_unique] >> rpt strip_tac >>
 drule Rf_Cons_back >> 
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘a’,‘l’] assume_tac) >> fs[] >>
 first_x_assum drule >> arw[])
(form_goal
 “!X x:1->X A t:A * X ->X l0 x0. 
  Rf(x,t) o Pa(l0,x0) = TRUE ==>
  !x'. Rf(x,t) o Pa(l0,x') = TRUE ==> x' = x0”));

val Rf_uex = prove_store("Rf_uex",
e0
(rpt strip_tac >>
 qby_tac ‘?P. !l0. (?!x0. Rf(x,t) o Pa(l0,x0) = TRUE) <=> P o l0 = TRUE’
 >-- (qexists_tac ‘UE(Rf(x,t) o Swap(X,List(A)))’ >>
      rw[GSYM UE_def,E1_def,o_assoc] >> rw[Swap_Pa] >> 
     rpt strip_tac >> dimp_tac >> rpt strip_tac 
    >-- (pop_assum (strip_assume_tac o uex_expand) >> 
         qexists_tac ‘x0’ >> arw[]) >>
    uex_tac >> qexists_tac ‘x'’ >> arw[]) >> pop_assum strip_assume_tac >> arw[] >>
 irule List_ind >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rpt strip_tac (* 2 *) >--
 (pop_assum (strip_assume_tac o uex_expand) >>
 drule Rf_CONS >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 uex_tac >> qexists_tac ‘t o Pa(a,x0)’ >> arw[] >> drule Rf_unique >> arw[]) >>
 uex_tac >> qexists_tac ‘x’ >> rw[Rf_property] >>
 rw[Rf_Nil_unique])
(form_goal
 “!X x:1->X A t:A * X ->X l0.?!x0. Rf(x,t) o Pa(l0,x0) = TRUE”));

val from_List_eq = prove_store("from_List_eq",
e0
(rpt strip_tac >> irule FUN_EXT >> 
 qby_tac ‘?P. !l. f1 o l = f2 o l <=> P o l = TRUE’
 >-- (qexists_tac ‘Eq(X) o Pa(f1,f2)’ >> rw[o_assoc,Pa_distr,Eq_property_TRUE])
 >> pop_assum strip_assume_tac >> arw[] >>
 irule List_ind >> pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A X f1:List(A) ->X f2. (f1 o Nil(A) = f2 o Nil(A) &
 (!l:1-> List(A). f1 o l = f2 o l ==> !a. f1 o CONS(a,l) = f2 o CONS(a,l))) ==> f1 = f2”));

val List_rec = prove_store("List_rec",
e0
(rpt strip_tac >>
 assume_tac Rel2Ar' >> assume_tac Rf_uex >>
first_x_assum (qsspecl_then [‘Rf(x,t)’] assume_tac) >> 
 last_x_assum mp_tac >> strip_tac >>
 pop_assum (qspecl_then [‘X’,‘x’,‘A’,‘t’] assume_tac) >> 
 first_x_assum drule >> pop_assum strip_assume_tac >>
 uex_tac >> qexists_tac ‘f’ >>  arw[] >> rw[Rf_property] >> 
 qby_tac
 ‘f o Cons(A) = t o Pa(p1(A, List(A)), f o p2(A, List(A)))’
 >-- (irule FUN_EXT >> rw[o_assoc] >> strip_tac >>
 qsspecl_then [‘a’] (x_choosel_then ["a0","l0"] assume_tac) has_components >>
 arw[] >>
 first_x_assum (qspecl_then [‘l0’,‘f o l0’] assume_tac) >> fs[] >>
 drule Rf_CONS >> rw[Pa_distr,p12_of_Pa,CONS_def,o_assoc] >> arw[]) >>
 arw[] >> rpt strip_tac >> irule from_List_eq >> arw[] >>
 rpt strip_tac
 >-- (arw[GSYM CONS_def,GSYM o_assoc] >> 
      rw[o_assoc,Pa_distr,p12_of_Pa] >> arw[]) >>
 flip_tac >> arw[] >> rw[Rf_property]
 )
(form_goal
 “!X x:1->X A t:A * X ->X. 
  ?!f:List(A) -> X. f o Nil(A) = x &
      f o Cons(A) = t o Pa(p1(A,List(A)), f o p2(A,List(A)))”));


val Length_ex = prove_store("Length_ex",
e0
(rpt strip_tac >> qexists_tac ‘Card(N * A) o LI(A)’ >> rw[])
(form_goal “!A. ?lg.Card(N * A) o LI(A) = lg”));

val Length_def =Length_ex |> spec_all |> ex2fsym0 "Length" ["A"]
|> gen_all |> store_as "Length_def";


val LENGTH_ex = prove_store("LENGTH_ex",
e0
(rpt strip_tac >> qexists_tac ‘Length(A) o l’ >> rw[])
(form_goal
 “!X A l:X->List(A).?n. Length(A) o l = n”));


val LENGTH_def = LENGTH_ex |> spec_all |> ex2fsym0 "LENGTH" ["l"]
                           |> qgen ‘l’ |> qgen ‘A’ |> gen_all
                           |> store_as "LENGTH_def";


val LENGTH_def1 = LENGTH_def |> allE (rastt "1")

val LENGTH_Nil = prove_store("LENGTH_Nil",
e0
(strip_tac >> rw[GSYM LENGTH_def] >> rw[GSYM Length_def] >>
 rw[o_assoc,Nil_def] >> rw[CARD_def,CARD_Empty])
(form_goal “!A. LENGTH(Nil(A)) = O”));

val List_CARD_NOTIN = prove_store("List_CARD_NOTIN",
e0
(rpt strip_tac >>
 ccontra_tac >> 
 assume_tac isList_CARD_NOTIN >>
 first_x_assum (qsspecl_then [‘LI(A) o l’] assume_tac) >>
 fs[List_def1] >>
 qby_tac ‘?x0:1->List(A). LI(A) o l = LI(A) o x0’ >--
 (qexists_tac ‘l’ >> rw[]) >>
 first_x_assum drule >>
 first_x_assum drule >> fs[Lt_def])
(form_goal “!A a:1->A l. ~IN(Pa(CARD(LI(A) o l), a), LI(A) o l)”));

val LENGTH_CONS = prove_store("LENGTH_CONS",
e0
(rpt strip_tac >> rw[GSYM LENGTH_def,GSYM Length_def,o_assoc] >> 
 assume_tac Cons_def >>
 first_x_assum (qsspecl_then [‘a’,‘l’,‘CONS(a,l)’] assume_tac) >>
 fs[CONS_def] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[CARD_def] >> irule CARD_Ins >>
 rw[List_LI_Finite] >> ccontra_tac >>
 fs[List_CARD_NOTIN])
(form_goal
 “!A a:1->A l. LENGTH(CONS(a,l)) = Suc(LENGTH(l))”));

val Map_ex = prove_store("Map_ex",
e0
(rpt strip_tac >>
 assume_tac List_rec >>
 first_x_assum (qsspecl_then [‘Nil(B)’,‘Cons(B) o Pa(f o p1(A,List(B)),p2(A,List(B)))’] assume_tac) >> 
 pop_assum (strip_assume_tac o uex_expand) >>
 pop_assum (K all_tac) >> qexists_tac ‘f'’ >> arw[] >>
 rpt strip_tac >> rw[GSYM CONS_def] >>
 arw[GSYM o_assoc] >>
 rw[o_assoc,p12_of_Pa,Pa_distr] )
(form_goal
 “!A B f:A->B. ?map:List(A) ->List(B).
 map o Nil(A)  = Nil(B) & 
 !a:1->A l. map o CONS(a,l) = CONS(f o a,map o l)”));

val Map_def = Map_ex |> spec_all |> ex2fsym0 "Map" ["f"]
                     |> gen_all |> store_as "Map_def";

val Arb_ex = prove_store("Arb_ex",
e0
(rw[])
(form_goal
 “!A. (?a:1->A.T) ==> (?a:1->A.a = a) ”));

val Arb_def = Arb_ex |> spec_all |> undisch
                     |> ex2fsym0 "Arb" ["A"]
                     |> disch_all
                     |> gen_all
                     |> store_as "Arb_def";

val LENGTH_eqn = prove_store("LENGTH_eqn",
e0
(rw[GSYM LENGTH_def,GSYM Length_def,GSYM CARD_def,o_assoc])
(form_goal
 “!A l:1->List(A). LENGTH(l) = CARD(LI(A) o l)”));

val NOT_Lt_O = rewr_rule[GSYM Lt_def1] NOT_LT_O
                        |> store_as "NOT_Lt_O";




val Le_cases_iff = prove_store("Le_cases_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (drule Le_cases >> arw[]) 
 >-- fs[Lt_def] >>
 arw[Le_refl])
(form_goal
 “!n0 n:1->N. Le(n0,n) <=> 
  (Lt(n0,n) | n0 = n)”));


val CONS_eqn = prove_store("CONS_eqn",
e0
(rpt strip_tac >>
 assume_tac Cons_def >>
 first_x_assum
 (qsspecl_then [‘a0’,‘l0’,‘Cons(A) o Pa(a0,l0)’] assume_tac) >>
 fs[CONS_def])
(form_goal
 “!A a0 l0:1->List(A). Ins(Pa(CARD(LI(A) o l0),a0), LI(A) o l0) = 
            LI(A) o CONS(a0,l0)”));

val El_lemma = prove_store("El_lemma",
e0
(strip_tac >> 
 qby_tac
 ‘?P.!l. (!n. Lt(n,LENGTH(l)) ==> ?!a. IN(Pa(n,a),LI(A) o l)) <=> 
          P o l = TRUE’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 arw[] >> match_mp_tac List_ind >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[LENGTH_Nil,NOT_Lt_O] >> rpt strip_tac >>
 fs[LENGTH_CONS] >> fs[Lt_Suc_Le] >> fs[Le_cases_iff] 
 >-- (first_x_assum drule >> uex_tac >>
     pop_assum (strip_assume_tac o uex_expand) >>
     qexists_tac ‘a'’ >>
     arw[GSYM CONS_eqn,IN_Ins] >> rw[Pa_eq_eq] >> rpt strip_tac (* 2 *)
     >-- 
     fs[GSYM LENGTH_def,GSYM Length_def,Lt_def,o_assoc,GSYM CARD_def]>>
     first_x_assum irule >> arw[]) >>
uex_tac >> qexists_tac ‘a’ >> rw[GSYM CONS_eqn,IN_Ins] >>
arw[LENGTH_eqn] >> rw[Pa_eq_eq] >> rpt strip_tac >>
fs[List_CARD_NOTIN])
(form_goal
 “!A l:1->List(A) n. Lt(n,LENGTH(l)) ==> ?!a. IN(Pa(n,a),LI(A) o l)”));



val LESS_ADD_NONZERO = prove_store("LESS_ADD_NONZERO",
e0
(strip_tac >> 
 qby_tac ‘?P. !n.(~(n = O) ==> Lt(m,Add(m,n))) <=> P o n = TRUE’
 >-- cheat >>
 pop_assum strip_assume_tac >> arw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
rw[Suc_def] >> 
rpt strip_tac >> cases_on “n = O” 
 >-- arw[Add_Suc,Add_O,Lt_Suc] >>
 first_x_assum drule >>
 rw[Add_Suc] >> irule Lt_trans >>
 qexists_tac ‘Add(m,n)’ >> arw[Lt_Suc])
(form_goal
 “!m:1->N n. ~(n = O) ==> Lt(m,Add(m,n))”));

val Add_Sub = rewr_rule[Add_def,Sub_def] ADD_SUB
                       |> store_as "Add_Sub";

val SUB_LESS = prove_store("SUB_LESS",
e0
(rpt strip_tac >>
 drule Le_Add_ex >> pop_assum (strip_assume_tac o GSYM)>>
 arw[] >>
 rw[Add_Sub] >> 
 irule LESS_ADD_NONZERO >> fs[Lt_def] >> dflip_tac >> arw[]
 )
(form_goal
 “!m n. Lt(O,n) & Le(n,m) ==> Lt(Sub(m,n),m)”));

val LESS_O = rewr_rule[GSYM Lt_def1,Suc_def] LESS_0
                      |> store_as "LESS_O";

val El_ex = prove_store("El_ex",
e0
(rpt strip_tac >>
 assume_tac Rel2Ar' >>
 qby_tac
 ‘?R. !n:1->N l:1->List(A) a:1->A.
  R o Pa(Pa(n,l),a) = TRUE <=>
  (Le(n, LENGTH(l)) & 
   IN(Pa(Sub(LENGTH(l),n),a),LI(A) o l)) | 
  (n = O & a = Arb(A)) |
  (Lt(LENGTH(l),n) & a = Arb(A))’ 
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘!nl:1-> N * List(A). ?!a. R o Pa(nl,a) = TRUE’ 
 >-- (strip_tac >>
     qsspecl_then [‘nl’] (x_choosel_then ["n","l"] assume_tac) 
     has_components>> cases_on “n = O” (* 2 *)
     >-- (uex_tac >> qexists_tac ‘Arb(A)’ >> arw[] >>
         rw[Sub_O,LENGTH_eqn,List_CARD_NOTIN,NOT_Lt_O]) >>
     cases_on “Lt(LENGTH(l:1-> List(A)),n)”
     >-- (uex_tac >> qexists_tac ‘Arb(A)’ >> arw[] >>
         rw[LENGTH_eqn] >> rpt strip_tac >>
         fs[LENGTH_eqn] >> fs[Lt_def] >>
         qsuff_tac ‘CARD(LI(A) o l) = n’ >-- arw[] >>
         irule Le_asym >> arw[]) >>
     qspecl_then [‘A’] assume_tac El_lemma >>
     uex_tac >> arw[] >>
     fs[NOT_LESS] >> 
     qsuff_tac
       ‘?!b. IN(Pa(Sub(LENGTH(l), n), b),LI(A) o  l)’
     >-- (strip_tac >> pop_assum (assume_tac o uex_expand) >>arw[]) >>
     first_x_assum irule >> irule SUB_LESS >> arw[] >>
     fs[O_xor_Suc] >> rw[LESS_O]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >> 
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘Pa(n,l)’,‘f o Pa(n,l)’] assume_tac)>>
 fs[] >> rfs[]) 
(form_goal
 “!A. ?el:N * List(A) -> A.
  !n l. ~(n = O) & ~(Lt(LENGTH(l),n)) ==>
  IN(Pa(Sub(LENGTH(l),n),el o Pa(n,l) ),LI(A) o l)”));
