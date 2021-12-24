
                    

val Insert_ex = prove_store("Insert_ex",
e0
(strip_tac >> qexists_tac
 ‘Tp(DISJ o 
    Pa(Eq(X) o Pa(p31(X,X,Exp(X,1+1)),p32(X,X,Exp(X,1+1))),
       Ev(X,1+1) o Pa(p31(X,X,Exp(X,1+1)),p33(X,X,Exp(X,1+1)))))’
 >> rw[])
(form_goal
 “!X.?Ins: X * Exp(X,1+1) -> Exp(X,1+1). 
 Tp(DISJ o 
    Pa(Eq(X) o Pa(p31(X,X,Exp(X,1+1)),p32(X,X,Exp(X,1+1))),
       Ev(X,1+1) o Pa(p31(X,X,Exp(X,1+1)),p33(X,X,Exp(X,1+1))))) = Ins ”));


val Delete_ex = prove_store("Delete_ex",
e0
(strip_tac >> qexists_tac
 ‘Tp(CONJ o 
    Pa(NEG o Eq(X) o Pa(p31(X,X,Exp(X,1+1)),p32(X,X,Exp(X,1+1))),
       Ev(X,1+1) o Pa(p31(X,X,Exp(X,1+1)),p33(X,X,Exp(X,1+1)))))’
 >> rw[])
(form_goal
 “!X.?Del: X * Exp(X,1+1) -> Exp(X,1+1). 
 Tp(CONJ o 
    Pa(NEG o Eq(X) o Pa(p31(X,X,Exp(X,1+1)),p32(X,X,Exp(X,1+1))),
       Ev(X,1+1) o Pa(p31(X,X,Exp(X,1+1)),p33(X,X,Exp(X,1+1))))) = Del ”));


val Insert_def = 
    Insert_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Insert" ["X"]
              |> C mp (trueI []) |> gen_all



val Delete_def = 
    Delete_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Delete" ["X"]
              |> C mp (trueI []) |> gen_all


val Ins_ex = prove_store("Ins_ex",
e0
(rpt strip_tac >> qexists_tac ‘Insert(X) o Pa(x,s0)’ >> rw[])
(form_goal
“!A X x:A->X s0:A->Exp(X,1+1).?f. Insert(X) o Pa(x,s0) = f”));


val Del_ex = prove_store("Del_ex",
e0
(rpt strip_tac >> qexists_tac ‘Delete(X) o Pa(x,s0)’ >> rw[])
(form_goal
“!A X x:A->X s0:A->Exp(X,1+1).?f. Delete(X) o Pa(x,s0) = f”));



val Ins_def = 
    Ins_ex |> spec_all |> eqT_intro
           |> iffRL |> ex2fsym "Ins" ["x","s0"]
           |> C mp (trueI []) |> gen_all


val Del_def = 
    Del_ex |> spec_all |> eqT_intro
           |> iffRL |> ex2fsym "Del" ["x","s0"]
           |> C mp (trueI []) |> gen_all




val Ins_property = prove_store("Ins_property",
e0
(rpt strip_tac >> rw[GSYM Ins_def,GSYM Insert_def,Ev_of_Tp] >> 
 rw[Ev_of_Tp_el,Pa_distr,o_assoc,DISJ_def,p31_def] >> rw[p31_of_Pa,p32_of_Pa] >> 
(qspecl_then [‘X’,‘1’,‘x’,‘x0’] mp_tac) $ GSYM Eq_property >> once_rw[True1TRUE] >> 
 strip_tac >> arw[] >> rw[p33_of_Pa]
)
(form_goal
 “!X x0:1->X s0:1->Exp(X,1+1).
  !x:1->X. Ev(X,1+1) o Pa(x,Ins(x0,s0)) = TRUE <=> 
  (x = x0 | Ev(X,1+1) o Pa(x,s0) = TRUE)”));



val Del_property = prove_store("Del_property",
e0
(rpt strip_tac >> rw[GSYM Del_def,GSYM Delete_def,Ev_of_Tp] >> 
 rw[Ev_of_Tp_el,Pa_distr,o_assoc,CONJ_def,p31_def,NEG_def] >> rw[p31_of_Pa,p32_of_Pa,p33_of_Pa,TRUE_xor_FALSE,Eq_property_TRUE] >> 
 dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X x0:1->X s0:1->Exp(X,1+1).
  !x:1->X. Ev(X,1+1) o Pa(x,Del(x0,s0)) = TRUE <=> 
  (Ev(X,1+1) o Pa(x,s0) = TRUE & ~(x = x0))”));





val Empty_ex = prove_store("Empty_ex",
e0
(strip_tac >> qexists_tac ‘Tp(False(X) o p1(X,1))’ >> rw[])
(form_goal
“!X.?ept:1->Exp(X,1+1). Tp(False(X) o p1(X,1))= ept”));


val Empty_def = 
    Empty_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Empty" ["X"]
             |> C mp (trueI []) |> gen_all



val contain_empty = 
mk_o (rastt "Mem(Exp(X,1+1))") $
Pa
(rastt "Empty(X) o To1(Exp(Exp(X,1+1),1+1))")
(rastt "id(Exp(Exp(X,1+1),1+1))")


val longpred_ant = rastt "Ev(Exp(X,1+1),1+1)"

val longpred_conc = 
rastt $ q2str
‘All(X) o Tp(Ev(Exp(X,1+1),1+1) o 
             Pa(Ins(p31(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1)),
                    p32(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1))),
                p33(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1))))’



val longpred0 = 
mk_o (rastt "All(Exp(X,1+1))") $ Tp (mk_o IMP (Pa longpred_ant longpred_conc))

val longpred = 
mk_o CONJ (Pa contain_empty longpred0)

val bigset = Tp1 longpred





val BIGINTER_ex = prove_store("BIGINTER_ex",
e0
(*?(biX : Exp(Exp(X#, 2), 2) -> Exp(X#, 2))*)
(strip_tac >> qexists_tac ‘Tp (All(Exp(X,1+1)) o Tp(IMP o Pa
 (Ev(Exp(X,1+1),1+1) o 
  Pa(p31(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1)),
     p33(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1))),
  Ev(X,1+1) o 
  Pa(p32(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1)),
     p31(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1))))  ))’ >> rw[])
(form_goal
“!X.?biX.
 Tp (All(Exp(X,1+1)) o Tp(IMP o Pa
 (Ev(Exp(X,1+1),1+1) o 
  Pa(p31(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1)),
     p33(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1))),
  Ev(X,1+1) o 
  Pa(p32(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1)),
     p31(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1))))  )) = biX ”));


val BIGINTER_def = 
BIGINTER_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "BIGINTER" ["X"] 
            |> C mp (trueI []) |> gen_all

val BIGINTER_property = prove_store("BIGINTER_property",
e0
(rpt strip_tac >> rw[GSYM BIGINTER_def] >>
 rw[Ev_of_Tp_el] >> rw[o_assoc,All_def] >> 
 rw[Pa_distr,IMP_def] >>
 rw[o_assoc,Pa_distr,p33_of_Pa,p31_of_Pa,p32_of_Pa])
(form_goal
 “!X ss:1->Exp(Exp(X,1+1),1+1) x:1->X.
  Ev(X,1+1) o Pa(x,BIGINTER(X) o ss) = TRUE <=> 
  !s0:1-> Exp(X,1+1). Ev(Exp(X,1+1),1+1) o Pa(s0,ss) = TRUE ==>
   Ev(X,1+1) o Pa(x,s0) = TRUE”));



val finites = 
mk_o (rastt "BIGINTER(Exp(X,1+1))") bigset

val isFinite_subset = 
mk_o (mk_o (rastt "Ev(Exp(X,1+1),1+1)") 
(Pa (rastt "p1(Exp(X,1+1),1)") (mk_o finites (rastt "p2(Exp(X,1+1),1)")))) (rastt "Pa(id(Exp(X,1+1)),To1(Exp(X,1+1)))")




val isFinite_ex = prove_store("isFinite_ex",
e0
(strip_tac >> 
 exists_tac isFinite_subset >> rw[])
(form_goal $
mk_forall "X" ob_sort
 (mk_exists "f" (ar_sort (Exp (mk_ob "X") two) two)
  (mk_eq isFinite_subset (rastt "f:Exp(X,1+1) -> 1+1")))
));

val isFinite_def = 
isFinite_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "isFinite" ["X"] 
            |> C mp (trueI []) |> gen_all;


val isFinite_property = prove_store("isFinite_property",
e0
(rpt strip_tac >> rw[GSYM isFinite_def] >>
rw[o_assoc,Pa_distr,idL,p1_of_Pa] >>
rw[BIGINTER_property] >> 
rw[p2_of_Pa] >> rw[GSYM Tp1_def] >>
rw[Ev_of_Tp_el] >> rw[o_assoc,CONJ_def,Pa_distr] >>
rw[p1_of_Pa,idL] >> rw[All_def] >>
rw[o_assoc,Pa_distr] >> rw[IMP_def] >>
rw[All_def] >> rw[o_assoc,Pa_distr] >>
rw[Pa3_def] >> rw[p32_of_Pa3,p33_of_Pa3] >>
rw[GSYM Ins_def] >> rw[Pa_distr,o_assoc] >>
rw[p31_of_Pa3,p32_of_Pa3] >>
rw[GSYM Mem_def] >> once_rw[one_to_one_id] >> rw[idR]
)
(form_goal
“!X a:1->Exp(X,1+1). isFinite(X) o a = TRUE <=>
!P: 1-> Exp(Exp(X,1+1),1+1). 
 Ev(Exp(X,1+1),1+1) o Pa(Empty(X),P) = TRUE &
 (!s0:1-> Exp(X,1+1). Ev(Exp(X,1+1),1+1) o Pa(s0,P) = TRUE ==>
   !e:1->X.Ev(Exp(X,1+1),1+1) o Pa(Ins(e,s0),P) = TRUE) ==>
 Ev(Exp(X,1+1),1+1) o Pa(a,P) = TRUE
 ”));




val isFinite_property1 =prove_store("isFinite_property1",
e0
(rw[isFinite_property] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (first_x_assum (qspecl_then [‘Tp1(P)’] assume_tac) >>
  fs[GSYM Tp1_def,Ev_of_Tp_el',o_assoc,p1_of_Pa] >>
  first_x_assum irule >> arw[]) >>
 rw[Ev_of_el] >> first_x_assum irule >>
 fs[Ev_of_el]
 )
(form_goal 
 “!X a:1->Exp(X,1+1). isFinite(X) o a = TRUE <=> !P:Exp(X,1+1) ->1+1.
 P o Empty(X) = TRUE &
 (!s0:1-> Exp(X,1+1). 
  P o s0 = TRUE ==> !e:1->X.P o Ins(e,s0) = TRUE) ==>
 P o a = TRUE
 ”));



val FINITE_def = new_ax 
“!X. FINITE(X) <=> isFinite(X) o Tp1(True(X)) =TRUE”


val isFinite_Empty = prove_store("isFinite_Empty",
e0
(strip_tac >> rw[isFinite_property1] >> rpt strip_tac)
(form_goal
 “!X. isFinite(X) o Empty(X) = TRUE”));


val isFinite_Insert = prove_store("isFinite_Insert",
e0
(rw[isFinite_property1] >> rpt strip_tac >>
 qsuff_tac 
 ‘All(X) o Tp(P o Insert(X)) o a = TRUE’ >--
 (rw[All_def,o_assoc,Ins_def] >> strip_tac >> arw[]) >>
 rw[GSYM o_assoc] >> first_x_assum irule >>
 strip_tac >-- 
 (rw[All_def,o_assoc,Ins_def] >> strip_tac >> strip_tac >>
  strip_tac >> first_x_assum irule >> arw[]) >>
 rw[All_def,o_assoc,Ins_def] >> first_x_assum irule >> arw[]
 )
(form_goal
 “!X a:1-> Exp(X,1+1). isFinite(X) o a = TRUE ==>
  !x:1->X. isFinite(X) o Ins(x,a) = TRUE”));



(*
val p41_ex = prove_store("p41_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A, B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p41. p1(A,B * C * D) = p41”));

val p41_def = p41_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p41" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val p42_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac ‘p1(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p42. p1(B, C * D) o p2(A,B * C * D) = p42”)


val p42_def = p42_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p42" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p43_ex = prove_store("p43_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p43. p1(C,D) o p2(B, C * D) o p2(A,B * C * D) = p43”));


val p43_def = p43_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p43" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p44_ex = prove_store("p44_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p44. p2(C,D) o p2(B, C * D) o p2(A,B * C * D) = p44”));


val p44_def = p44_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p44" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

*)


(*
val p42_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac ‘p1(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p42. p1(B, C * D) o p2(A,B * C * D) = p42”)


val p42_def = p42_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p42" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p43_ex = prove_store("p43_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p43. p1(C,D) o p2(B, C * D) o p2(A,B * C * D) = p43”));


val p43_def = p43_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p43" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p42_of_Pa4 = prove_store("p42_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p42_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p42(A,B,C,D) o Pa4(f,g,h,k) = g”));


val p43_of_Pa4 = prove_store("p43_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p43_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p43(A,B,C,D) o Pa4(f,g,h,k) = h”));
*)



val ABSORPTION_RWT = prove_store("ABSORPTION_RWT",
e0
(rpt strip_tac >> rw[GSYM Mem_def] >>
 once_rw[GSYM Tp0_INJ] >> dimp_tac >> strip_tac (* 2 *) >-- 
 (irule FUN_EXT >> strip_tac >> 
 rw[GSYM Tp0_def,o_assoc,Pa_distr,idL] >> 
 once_rw[one_to_one_id] >> rw[idR] >>
 once_rw[GSYM pred_ext] >> rw[Ins_property] >>
 dimp_tac >> strip_tac (* 2 *) 
 >-- fs[] >> arw[]) >>
 pop_assum mp_tac >>  
 rw[GSYM Tp0_def,o_assoc,Pa_distr,idL] >> 
 once_rw[GSYM FUN_EXT_iff] >> once_rw[one_to_one_id] >>
 rw[idR] >> once_rw[GSYM pred_ext] >> rw[] >>
 rw[Pa_distr,o_assoc] >> once_rw[one_to_one_id] >>
 rw[idL,idR] >> rw[Ins_property] >> rpt strip_tac >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 fs[])
(form_goal
“!X x:1->X s0:1->Exp(X,1+1). (Mem(X) o Pa(x,s0) = TRUE) <=>
 Ins(x,s0) = s0”));


val NOT_IN_Empty = prove_store("NOT_IN_Empty",
e0
(rpt strip_tac >> rw[GSYM Mem_def,GSYM Empty_def,Ev_of_Tp_el',o_assoc] >> once_rw[one_to_one_id] >> rw[idR,False2FALSE]>>
 rw[TRUE2FALSE])
(form_goal
“!X x:1->X. ~(Mem(X) o Pa(x,Empty(X)) = TRUE)”));


val NOTIN_Empty = prove_store("NOTIN_Empty",
e0
(assume_tac NOT_IN_Empty >> fs[GSYM IN_def1])
(form_goal “!X x. ~IN(x,Empty(X))”));

val IN_Ins = prove_store("IN_Ins",
e0
(assume_tac Ins_property >> fs[GSYM IN_def1,Mem_def] )
(form_goal “!X x:1->X x0 xs0. IN(x,Ins(x0,xs0)) <=> x = x0 | IN(x,xs0)”));


val IN_Del = prove_store("IN_Ins",
e0
(assume_tac Del_property >> fs[GSYM IN_def1,Mem_def] )
(form_goal “!X x:1->X x0 xs0. IN(x,Del(x0,xs0)) <=> IN(x,xs0) & ~(x = x0)”));

val Ins_absorb = prove_store("Ins_absorb",
e0
(assume_tac ABSORPTION_RWT  >> fs[IN_def,True1TRUE])
(form_goal “!X x:1->X s0.IN(x,s0) <=> Ins(x,s0) = s0”));
 
val Del_Ins = prove_store("Del_Ins",
e0
(rpt strip_tac >> rw[IN_EXT,IN_Del,IN_Ins] >>
 strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 ccontra_tac >> fs[])
(form_goal “!X x0:1->X xs0. (~IN(x0,xs0)) ==> Del(x0,Ins(x0,xs0)) =xs0”));


val Ins_NONEMPTY = prove_store("Ins_NONEMPTY",
e0
(rw[IN_EXT,IN_Ins,NOTIN_Empty] >> rpt strip_tac >> 
ccontra_tac >>
 first_x_assum (qspecl_then [‘x0’] assume_tac) >> fs[])
(form_goal
 “!X x0:1->X xs.~(Ins(x0,xs) = Empty(X))”));

val IN_Ins_SND = prove_store("IN_Ins_SND",
e0
(rw[IN_Ins] >> rpt strip_tac)
(form_goal “!X x0:1->X xs0 x. IN(x, Ins(x0, xs0)) & (~(x = x0)) ==> IN(x,xs0)”)); 

val Del_Ins_SWAP = prove_store("Del_Ins_SWAP",
e0
(rpt strip_tac >> rw[IN_EXT,IN_Ins,IN_Del] >> 
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X x0 x:1->X.(~(x0 = x)) ==> !xs.Del(x,Ins(x0, xs)) = Ins(x0,Del(x,xs))”));




val contain_empty_O = 
mk_o (rastt "Mem(Exp(X,1+1) * N)") $
Pa
(rastt "Pa(Empty(X),O) o To1(Exp(Exp(X,1+1) * N,1+1))")
(rastt "id(Exp(Exp(X,1+1) * N,1+1))")

val longp_ant = rastt "Ev(Exp(X,1+1) * N,1+1)";


val notin_pred = 
rastt $ q2str 
‘NEG o Mem(X) o 
       Pa(p31(X,
              Exp(X,1+1) * N,
              Exp(Exp(X,1+1) * N,1+1)),
          p1(Exp(X,1+1), N) o 
          p32(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1)))’

val notin_conc_pred = 
rastt $ q2str
‘Mem(Exp(X,1+1) * N) o 
      Pa(Pa(Ins(p31(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1)),
             p1(Exp(X,1+1), N) o
             p32(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1))),
            SUC o 
            p2(Exp(X,1+1), N) o
            p32(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1))),
         p33(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1)))’

val imp_pred = mk_o IMP (Pa notin_pred notin_conc_pred)

val longp_conc = mk_o (rastt "All(X)") (Tp imp_pred)

val longp0 = 
mk_o (rastt "All(Exp(X,1+1) * N)") $ Tp (mk_o IMP (Pa longp_ant longp_conc))

val longp = 
mk_o CONJ (Pa contain_empty_O longp0)

val sets_contain_pair = Tp1 longp

val hasCard = mk_o (rastt "BIGINTER(Exp(X,1+1) * N)") sets_contain_pair



val hasCard_ar = Tp0 hasCard

val hasCard_ex = prove_store("hasCard_ex",
e0
(strip_tac >> 
 exists_tac hasCard_ar >> rw[])
(form_goal $
mk_forall "X" ob_sort
 (mk_exists "f" (ar_sort (Po (Exp (mk_ob "X") two) N) two)
  (mk_eq hasCard_ar (rastt "f:Exp(X,1+1) * N -> 1+1")))
));

val hasCard_def = 
hasCard_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "hasCard" ["X"] 
            |> C mp (trueI []) |> gen_all;




val hasCard_property = prove_store("hasCard_property",
e0
(rpt strip_tac >> rw[GSYM hasCard_def] >>
 rw[GSYM Tp0_def] >>
 rw[o_assoc,Pa_distr,idL,p1_of_Pa] >>
 once_rw[one_to_one_id] >> rw[idR,idL] >>
 once_rw[GSYM p31_def] >> 
once_rw [GSYM p32_def] >> 
 once_rw[GSYM p33_def] >>
 rw[o_assoc,Pa_distr,p12_of_Pa] >>
 rw[GSYM p31_def,GSYM p32_def,GSYM p33_def] >>
 once_rw[BIGINTER_property] >> once_rw[GSYM Tp1_def] >>
 once_rw[Ev_of_Tp_el'] >> 
 rw[o_assoc] >> rw[p12_of_Pa] >>
 once_rw[Pa_distr] >> once_rw[CONJ_def]>>
 rw[Pa_distr,o_assoc] >> rw[idL,idR] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 once_rw[All_def] >> rw[o_assoc,Pa_distr] >>
 once_rw[IMP_def] >> once_rw[All_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >>  once_rw[IMP_def] >> once_rw[o_assoc] >> once_rw[p12_of_Pa] >>
 once_rw[NEG_def] >>
 once_rw[TRUE_xor_FALSE] >>
 once_rw[Pa_distr] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >>
 once_rw[GSYM Ins_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >> 
  once_rw[p12_of_Pa] >>  once_rw[p12_of_Pa] >> 
once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum irule >> once_rw[GSYM Mem_def] >>
     once_arw[] >> rw[] >> strip_tac >>
     qby_tac ‘?s n. x = Pa(s,n)’ >-- 
     (qexistsl_tac [‘p1(Exp(X,1+1),N) o x’,
                    ‘p2(Exp(X,1+1),N) o x’] >>
     rw[GSYM to_P_component]) >>
     pop_assum strip_assume_tac >>
     once_arw[] >> rw[p12_of_Pa,o_assoc,Pa_distr] >>
     rpt strip_tac >> first_x_assum drule >>
     first_x_assum irule >> 
     rw[IN_def,GSYM Mem_def,True1TRUE] >>
     first_x_assum accept_tac) >>
 last_x_assum (qspecl_then [‘s0’] assume_tac) >> 
 first_x_assum irule >> fs[GSYM Mem_def] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘Pa(s0',n0)’] assume_tac) >>
 pop_assum mp_tac >> rw[p12_of_Pa,o_assoc,Pa_distr] >> 
 rpt strip_tac >> first_x_assum irule >> arw[] >>
 fs[IN_def,GSYM Mem_def,True1TRUE]
)
(form_goal
 “!X xs:1->Exp(X,1+1) n. hasCard(X) o Pa(xs,n) = TRUE <=>
 !P:1 -> Exp(Exp(X,1+1) * N,1+1).
  Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(Empty(X),O),P) = TRUE & 
  (!s0:1-> Exp(X,1+1) n0:1-> N. Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(s0,n0),P) = TRUE ==>
  !e:1->X.~(IN(e,s0)) ==>
    Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(Ins(e,s0),SUC o n0),P) = TRUE) ==> 
  Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(xs,n),P) = TRUE”));






(*
val hasCard_property = prove_store("hasCard_property",
e0
(rpt strip_tac >> rw[GSYM hasCard_def] >>
 rw[GSYM Tp0_def] >>
 rw[o_assoc,Pa_distr,idL,p1_of_Pa] >>
 once_rw[one_to_one_id] >> rw[idR,idL] >>
 once_rw[GSYM p31_def] >> 
once_rw [GSYM p32_def] >> 
 once_rw[GSYM p33_def] >>
 rw[o_assoc,Pa_distr,p12_of_Pa] >>
 rw[GSYM p31_def,GSYM p32_def,GSYM p33_def] >>
 once_rw[BIGINTER_property] >> once_rw[GSYM Tp1_def] >>
 once_rw[Ev_of_Tp_el'] >> 
 rw[o_assoc] >> rw[p12_of_Pa] >>
 once_rw[Pa_distr] >> once_rw[CONJ_def]>>
 rw[Pa_distr,o_assoc] >> rw[idL,idR] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 once_rw[All_def] >> rw[o_assoc,Pa_distr] >>
 once_rw[IMP_def] >> once_rw[All_def] >>
 rw[o_assoc,Pa_distr] >>
 once_rw[IMP_def] >>
 rw[o_assoc] >> rw[p12_of_Pa] >>
 once_rw[NEG_def] >>
 once_rw[TRUE_xor_FALSE] >>
 once_rw[Pa_distr] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >>
 once_rw[GSYM Ins_def] >> 
 rw[o_assoc] >> rw[Pa_distr] >> rw[p12_of_Pa] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum irule >> once_rw[GSYM Mem_def] >>
     once_arw[] >> rw[] >> strip_tac >>
     qby_tac ‘?s n. x = Pa(s,n)’ >-- 
     (qexistsl_tac [‘p1(Exp(X,1+1),N) o x’,
                    ‘p2(Exp(X,1+1),N) o x’] >>
     rw[GSYM to_P_component]) >>
     pop_assum strip_assume_tac >>
     once_arw[] >> rw[p12_of_Pa,o_assoc,Pa_distr] >>
     rpt strip_tac >> first_x_assum drule >>
     first_x_assum irule >> 
     rw[IN_def,GSYM Mem_def,True1TRUE] >>
     first_x_assum accept_tac) >>
 last_x_assum (qspecl_then [‘s0’] assume_tac) >> 
 first_x_assum irule >> fs[GSYM Mem_def] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘Pa(s0',n0)’] assume_tac) >>
 pop_assum mp_tac >> rw[p12_of_Pa,o_assoc,Pa_distr] >> 
 rpt strip_tac >> first_x_assum irule >> arw[] >>
 fs[IN_def,GSYM Mem_def,True1TRUE]
)
(form_goal
 “!X xs:1->Exp(X,1+1) n. hasCard(X) o Pa(xs,n) = TRUE <=>
 !P:1 -> Exp(Exp(X,1+1) * N,1+1).
  Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(Empty(X),O),P) = TRUE & 
  (!s0:1-> Exp(X,1+1) n0:1-> N. Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(s0,n0),P) = TRUE ==>
  !e:1->X.~(IN(e,s0)) ==>
    Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(Ins(e,s0),SUC o n0),P) = TRUE) ==> 
  Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(xs,n),P) = TRUE”));
*)



val IN_o = prove_store("IN_o",
e0
(rw[IN_def,GSYM Mem_def,GSYM Tp0_def,o_assoc,Pa_distr,True1TRUE,idL] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal
 “!X P x:1->X. IN(x,P) <=> Tp0(P) o x = TRUE”));

val Finite_ind = prove_store("Finite_ind",
e0
(rw[isFinite_property1] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal
 “!X P. P o Empty(X)= TRUE &
        (!xs. P o xs = TRUE ==> 
         !x. P o Ins(x, xs) = TRUE) ==>
   !xs. isFinite(X) o xs = TRUE ==> P o xs = TRUE”));

val hasCard_property1 = hasCard_property |> rewr_rule[Mem_def,GSYM IN_def1] |> store_as "hasCard_property1";

val hasCard_ind = prove_store("hasCard_ind",
e0
(rw[hasCard_property1] >> once_rw[Suc_def] >>
 rpt strip_tac >> 
 qsspecl_then [‘P’] assume_tac $ GSYM Tp0_Tp1_inv >>
 once_arw[] >>  rw[GSYM IN_o] >> first_x_assum irule >>
 rw[IN_o] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rpt strip_tac >> first_x_assum irule >>
 once_arw[] >> rw[] >> fs[GSYM IN_o])
(form_goal
 “!X P. P o Pa(Empty(X),O)= TRUE &
        (!xs n. P o Pa(xs,n) = TRUE ==> 
         !x. (~(IN(x,xs))) ==> P o Pa(Ins(x, xs),Suc(n)) = TRUE) ==>
   !xs n. hasCard(X) o Pa(xs,n) = TRUE ==> P o Pa(xs,n) = TRUE”));

val hasCard_Empty = prove_store("hasCard_Empty",
e0
(rw[hasCard_property1] >> rpt strip_tac >> arw[])
(form_goal “!X.hasCard(X) o Pa(Empty(X),O) = TRUE ”));

 

val hasCard_Ins = prove_store("hasCard_Ins",
e0
(rw[hasCard_property1] >> once_rw[Suc_def] >> rpt strip_tac
 >> first_assum irule >> arw[] >> first_assum irule >>
 arw[])
(form_goal 
 “!X xs n.hasCard(X) o Pa(xs,n) = TRUE ==>
          !x. (~IN(x,xs)) ==> hasCard(X) o Pa(Ins(x,xs),Suc(n)) = TRUE”));





val hasCard_Ins_Suc = prove_store("hasCard_Ins_Suc",
e0
(strip_tac >> assume_tac hasCard_ind >>
 qby_tac ‘?P. 
 !xs n. P o Pa(xs,n) = TRUE <=>
  hasCard(X) o Pa(xs,n) = TRUE & !x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0)’ >--
 (qby_tac ‘?P1.!xs:1->Exp(X,1+1) n:1->N. P1 o Pa(xs,n) = TRUE <=>
  (!x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0))’ >--
(qby_tac 
 ‘?P2. !x0:1->X xs:1->Exp(X,1+1) n. P2 o Pa(x0,Pa(xs,n)) = TRUE <=>
  !xs0. xs = Ins(x0,xs0) ==> ?n0:1->N. n = Suc(n0)’ >-- 
 (qby_tac ‘?P3. !xs0 x0 xs:1->Exp(X,1+1) n. P3 o Pa(xs0,Pa(x0,Pa(xs,n))) = TRUE <=> xs = Ins(x0,xs0) ==> ?n0:1->N. n = Suc(n0)’ >-- 
  (qby_tac ‘?P4. !n0:1->N xs0:1->Exp(X,1+1) x0:1->X xs:1->Exp(X,1+1) n.
   P4 o Pa(n0,Pa(xs0,Pa(x0,Pa(xs,n)))) = TRUE <=>
   n = Suc(n0)’ >-- 
   (qexists_tac ‘EQ(p55(N,Exp(X,1+1),X,Exp(X,1+1), N),
                    SUC o p51(N,Exp(X,1+1),X,Exp(X,1+1), N))’    >> rw[GSYM EQ_def] >> once_rw[o_assoc] >>
    once_rw[Pa_distr] >> rw[Eq_property_TRUE] >> 
    rw[Pa5_def]  >> 
    rw[p51_of_Pa5,p55_of_Pa5,o_assoc,Suc_def]) >> 
  pop_assum strip_assume_tac >>
  qby_tac ‘?P5. !xs0:1->Exp(X,1+1) x0:1->X xs:1->Exp(X,1+1) n:1->N.
   P5 o Pa(xs0,Pa(x0,Pa(xs,n))) = TRUE <=>
   xs = Ins(x0,xs0)’ >-- 
  (qexists_tac 
   ‘EQ(p43(Exp(X, 1 + 1),X,Exp(X,1 + 1), N),
       Insert(X) o 
       Pa(p42(Exp(X, 1 + 1),X,Exp(X,1 + 1), N),
          p41(Exp(X, 1 + 1),X,Exp(X,1 + 1), N)))’ >>
   rw[Pa4_def] >> rw[GSYM EQ_def,o_assoc,Pa_distr] >>
   rw[p41_of_Pa4,p42_of_Pa4,p43_of_Pa4] >>
   rw[Ins_def,Eq_property_TRUE]) >> 
  pop_assum strip_assume_tac >>
  qexists_tac ‘IMP o Pa(P5,Ex(N) o Tp(P4))’ >>
  rw[o_assoc,Pa_distr,IMP_def] >> rw[Ex_def] >>
  arw[]) >> pop_assum strip_assume_tac >>
 qexists_tac ‘All(Exp(X,1+1)) o Tp(P3)’ >> 
 once_rw[o_assoc] >> once_rw[All_def] >> once_arw[] >> rw[])
 >> pop_assum strip_assume_tac >>
 qexists_tac ‘All(X) o Tp(P2)’ >>
 once_rw[o_assoc] >> once_rw[All_def] >>
 once_arw[] >> rw[])>>
  pop_assum strip_assume_tac >>
  qexists_tac ‘CONJ o Pa(hasCard(X),P1)’ >>
  once_rw[o_assoc] >> once_rw[Pa_distr] >>
  once_rw[CONJ_def]>> once_arw[] >> rw[]) >>
 pop_assum strip_assume_tac >>
 first_x_assum (qsspecl_then [‘P’] assume_tac) >>
 pop_assum mp_tac >> once_arw[] >>
 strip_tac >> strip_tac >> strip_tac >>
 first_x_assum match_mp_tac >> once_rw[hasCard_Empty] >>
 rw[] >> once_rw[GSYM Ins_NONEMPTY]>> rw[] >>
 rpt strip_tac >--
 (drule hasCard_Ins >> first_x_assum drule >>
 first_x_assum accept_tac) >>
 qexists_tac ‘n'’ >> rw[])
(form_goal
 “!X xs n. hasCard(X) o Pa(xs,n) = TRUE ==> hasCard(X) o Pa(xs,n) = TRUE & !x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0)”));


(*

val hasCard_Ins_Suc = prove_store("hasCard_Ins_Suc",
e0
(strip_tac >> assume_tac hasCard_ind >>
 qby_tac ‘?P. 
 !xs n. P o Pa(xs,n) = TRUE <=>
  hasCard(X) o Pa(xs,n) = TRUE & !x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0)’ >--
 (qby_tac ‘?P1.!xs:1->Exp(X,1+1) n:1->N. P1 o Pa(xs,n) = TRUE <=>
  (!x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0))’ >--
(qby_tac 
 ‘?P2. !x0:1->X xs:1->Exp(X,1+1) n. P2 o Pa(x0,Pa(xs,n)) = TRUE <=>
  !xs0. xs = Ins(x0,xs0) ==> ?n0:1->N. n = Suc(n0)’ >-- 
 (qby_tac ‘?P3. !xs0 x0 xs:1->Exp(X,1+1) n. P3 o Pa(xs0,Pa(x0,Pa(xs,n))) = TRUE <=> xs = Ins(x0,xs0) ==> ?n0:1->N. n = Suc(n0)’ >-- 
  (qby_tac ‘?P4. !n0:1->N xs0:1->Exp(X,1+1) x0:1->X xs:1->Exp(X,1+1) n.
   P4 o Pa(n0,Pa(xs0,Pa(x0,Pa(xs,n)))) = TRUE <=>
   n = Suc(n0)’ >-- 
   (qexists_tac ‘EQ(p55(N,Exp(X,1+1),X,Exp(X,1+1), N),
                    SUC o p51(N,Exp(X,1+1),X,Exp(X,1+1), N))’    >> rw[GSYM EQ_def] >> once_rw[o_assoc] >>
    once_rw[Pa_distr] >> rw[Eq_property_TRUE] >> 
    rw[Pa5_def]  >> 
    rw[p51_of_Pa5,p55_of_Pa5,o_assoc,Suc_def]) >> 
  pop_assum strip_assume_tac >>
  qby_tac ‘?P5. !xs0:1->Exp(X,1+1) x0:1->X xs:1->Exp(X,1+1) n:1->N.
   P5 o Pa(xs0,Pa(x0,Pa(xs,n))) = TRUE <=>
   xs = Ins(x0,xs0)’ >-- 
  (qexists_tac 
   ‘EQ(p43(Exp(X, 1 + 1),X,Exp(X,1 + 1), N),
       Insert(X) o 
       Pa(p42(Exp(X, 1 + 1),X,Exp(X,1 + 1), N),
          p41(Exp(X, 1 + 1),X,Exp(X,1 + 1), N)))’ >>
   rw[Pa4_def] >> rw[GSYM EQ_def,o_assoc,Pa_distr] >>
   rw[p41_of_Pa4,p42_of_Pa4,p43_of_Pa4] >>
   rw[Ins_def,Eq_property_TRUE]) >> 
  pop_assum strip_assume_tac >>
  qexists_tac ‘IMP o Pa(P5,Ex(N) o Tp(P4))’ >>
  rw[o_assoc,Pa_distr,IMP_def] >> rw[Ex_def] >>
  arw[]) >> pop_assum strip_assume_tac >>
 qexists_tac ‘All(Exp(X,1+1)) o Tp(P3)’ >> 
 once_rw[o_assoc] >> once_rw[All_def] >> once_arw[] >> rw[])
 >> pop_assum strip_assume_tac >>
 qexists_tac ‘All(X) o Tp(P2)’ >>
 once_rw[o_assoc] >> once_rw[All_def] >>
 once_arw[] >> rw[])>>
  pop_assum strip_assume_tac >>
  qexists_tac ‘CONJ o Pa(hasCard(X),P1)’ >>
  once_rw[o_assoc] >> once_rw[Pa_distr] >>
  once_rw[CONJ_def]>> once_arw[] >> rw[]) >>
 pop_assum strip_assume_tac >>
 first_x_assum (qsspecl_then [‘P’] assume_tac) >>
 pop_assum mp_tac >> once_arw[] >>
 strip_tac >> strip_tac >> strip_tac >>
 first_x_assum match_mp_tac >> once_rw[hasCard_Empty] >>
 rw[] >> once_rw[GSYM Ins_NONEMPTY]>> rw[] >>
 rpt strip_tac >--
 (drule hasCard_Ins >> first_x_assum drule >>
 first_x_assum accept_tac) >>
 qexists_tac ‘n'’ >> rw[])
(form_goal
 “!X xs n. hasCard(X) o Pa(xs,n) = TRUE ==> hasCard(X) o Pa(xs,n) = TRUE & !n0. n = Suc(n0) ==> ?x0 xs0. xs = Ins(x0,xs0)”));
*)


val Pre_Suc = prove_store("Pre_Suc",
e0
(fs[GSYM Pre_def,GSYM Suc_def,GSYM o_assoc,PRE_def,idL])
(form_goal “!X n:X->N. Pre(Suc(n)) = n”));

val hasCard_Del = prove_store("hasCard_Del",
e0
(strip_tac >> assume_tac hasCard_ind >>
 first_x_assum (qsspecl_then 
 [‘CONJ o Pa(hasCard(X),
   All(X) o 
   Tp(IMP o 
   Pa(Mem(X) o
      Pa(p31(X,Exp(X,1+1),N),p32(X,Exp(X,1+1),N)),
      hasCard(X) o 
      Pa(Delete(X) o Pa(p31(X,Exp(X,1+1),N),p32(X,Exp(X,1+1),N)),PRE o p33(X,Exp(X,1+1),N)))))’] assume_tac) >>
 pop_assum mp_tac >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[CONJ_def] >> once_rw[o_assoc] >> once_rw[All_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[IMP_def] >> once_rw[GSYM p31_def] >>
 once_rw[GSYM p32_def] >> once_rw[GSYM p33_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> 
 once_rw[o_assoc] >>  once_rw[p12_of_Pa] >>
 once_rw[p12_of_Pa] >> once_rw[o_assoc] >>  
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >>  
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >>  
 once_rw[Pa_distr] >> once_rw[p12_of_Pa] >>
 once_rw[Del_def] >> once_rw[Pre_def] >> strip_tac >>
 once_rw[IN_def] >> once_rw[True1TRUE] >>
 strip_tac >> strip_tac>>
 first_x_assum match_mp_tac >> rw[hasCard_Empty] >>
 rw[GSYM IN_def1] >> once_rw[NOTIN_Empty] >> rw[] >>
 rpt strip_tac >--
 (drule hasCard_Ins >> first_x_assum drule >> arw[]) >>
 cases_on “x' = x:1->X” >--
 (fs[] >> drule Del_Ins >> arw[] >> 
 rw[GSYM Pre_def,GSYM Suc_def] >> 
 rw[GSYM o_assoc,PRE_def,idL] >> arw[]) >>
 qby_tac ‘Del(x', Ins(x, xs')) = Ins(x, Del(x', xs'))’
 >-- (irule Del_Ins_SWAP >> dflip_tac >> arw[]) >>
 arw[] >> 
 qby_tac ‘IN(x',xs')’ 
 >-- (irule IN_Ins_SND >> qexists_tac ‘x’ >> arw[]) >>
 first_x_assum drule >>
 drule hasCard_Ins >>
 qby_tac ‘~(IN(x,Del(x',xs')))’ >--
 (rw[IN_Del] >> arw[]) >>
 first_x_assum drule >>
 qby_tac ‘Ins(x',xs') = xs'’ 
 >-- (irule $ iffLR Ins_absorb >> arw[]) >>
 qby_tac ‘hasCard(X) o Pa(Ins(x',xs'),n') = TRUE’ 
 >-- arw[] >>
 drule hasCard_Ins_Suc >>
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘x'’,‘xs'’] assume_tac) >>
 fs[] >> fs[Pre_Suc])
(form_goal
 “!X xs n.hasCard(X) o Pa(xs,n) = TRUE ==> hasCard(X) o Pa(xs,n) = TRUE & 
  !x. IN(x,xs) ==> hasCard(X) o Pa(Del(x,xs),Pre(n)) = TRUE”));


(*
val Card_Empty_unique0 = prove_store("Card_Empty_unique",
e0
(assume_tac hasCard_ind >> strip_tac >>
 qby_tac ‘?P. !xs n.P o Pa(xs,n) = TRUE <=>
 xs = Empty(X) ==> n = O’
 >-- (cheat) >> pop_assum strip_assume_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 strip_tac >> strip_tac >> first_x_assum match_mp_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 )
(form_goal
 “!X xs n.hasCard(X) o Pa(xs,n) = TRUE ==>
  xs = Empty(X) ==> n = O”));
*)

val Card_Empty_unique = prove_store("Card_Empty_unique",
e0
(rpt strip_tac >> ccontra_tac >> 
 drule $ iffLR hasCard_property1 >>
 qsuff_tac 
 ‘?P. IN(Pa(Empty(X), O), P) &
     (!s0 n0.
      IN(Pa(s0, n0), P) ==>
       !e. ~IN(e, s0) ==> 
       IN(Pa(Ins(e, s0), SUC o n0), P)) &
       ~(IN(Pa(Empty(X), n), P))’
 >-- (strip_tac >> 
     qby_tac ‘IN(Pa(Empty(X), n), P)’
     >-- (first_x_assum irule >> arw[]) >>
     fs[]) >>
 rw[IN_o] >> 
 qby_tac ‘?P. !s0 n0. P o Pa(s0,n0)= TRUE <=>
  hasCard(X) o Pa(s0,n0) = TRUE & 
  ~(s0 = Empty(X) & n0 = n)’ >--
 (qexists_tac ‘And(hasCard(X),Not(And(EQ(p1(Exp(X,1+1),N) , Empty(X) o To1(Exp(X,1+1) * N)),
 EQ(p2(Exp(X,1+1),N),n o To1(Exp(X,1+1) * N)))))’ >>
  rw[GSYM And_def] >> rw[o_assoc,Pa_distr,CONJ_def] >>
  rw[GSYM Not_def] >> rw[o_assoc,Pa_distr,NEG_def] >>
  rw[Pa_distr,CONJ_def,TRUE_xor_FALSE] >>
  rw[GSYM EQ_def] >> rw[o_assoc,Pa_distr,Eq_property_TRUE]>>
  once_rw[one_to_one_id] >> rw[idR,p12_of_Pa]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘Tp1(P)’ >> rw[Tp0_Tp1_inv] >>
 arw[] >> strip_tac (* 2 *)
 >-- (rw[hasCard_Empty] >> dflip_tac >> arw[]) >>
 rw[GSYM IN_o] >> rw[Ins_NONEMPTY] >>
 rpt strip_tac >> drule hasCard_Ins >> first_x_assum drule >>
 arw[Suc_def]
)
(form_goal
 “!X n.hasCard(X) o Pa(Empty(X),n) = TRUE ==> n = O”));


val Fin_Card = prove_store("Card_Fun",
e0
(assume_tac Finite_ind >> strip_tac >> 
 qby_tac ‘?P.!xs. P o xs = TRUE <=>
  ?!n. hasCard(X) o Pa(xs,n) = TRUE’
 >-- (qexists_tac ‘UE(hasCard(X) o Swap(N,Exp(X,1+1)))’
      >> rw[UE_property] >> rw[o_assoc,Swap_Pa] >>
      rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
      >-- (uex_tac >> qexists_tac ‘x’ >> arw[]) >>
      pop_assum (strip_assume_tac o uex_expand) >>
      qexists_tac ‘n’ >> arw[]) >> pop_assum strip_assume_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 strip_tac >> first_x_assum match_mp_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘O’ >> rw[hasCard_Empty] >>
     rpt strip_tac >> drule Card_Empty_unique >> arw[]) >>
 pop_assum (K all_tac) >> rpt strip_tac >>
 pop_assum (strip_assume_tac o uex_expand) >>
 uex_tac >> 
 cases_on “IN(x:1->X,xs')” 
 >-- (qexists_tac ‘n’ >> 
     qby_tac ‘Ins(x,xs') = xs'’ 
     >-- arw[GSYM Ins_absorb] >> arw[]) >>    
 qexists_tac ‘Suc(n)’ >> drule hasCard_Ins >> 
 first_x_assum drule >> arw[] >>
 rpt strip_tac >> 
 drule hasCard_Del >> fs[] >>
 qby_tac ‘IN(x, Ins(x, xs'))’ >-- fs[IN_Ins] >>
 first_x_assum drule >> drule Del_Ins >> fs[] >>
 first_x_assum drule >>
 qpick_x_assum ‘hasCard(X) o Pa(Ins(x, xs'), n') = TRUE’ assume_tac >>
 drule hasCard_Ins_Suc >> fs[] >>
 first_x_assum (qspecl_then [‘x’,‘xs'’] assume_tac) >> 
 fs[] >>  fs[Pre_Suc])
(form_goal
 “!X xs.isFinite(X) o xs= TRUE ==> ?!n.hasCard(X) o Pa(xs,n) = TRUE”));

val _ = new_pred "FINITE" [("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)"))]


val FINITE_def0 = store_ax("FINITE_def0",
“!A X xs:A-> Exp(X,1+1). FINITE(xs) <=> isFinite(X) o xs = True(A)”);

val FINITE_def = FINITE_def0 |> allE ONE 
                             |> rewr_rule[True1TRUE]
                             |> store_as "FINITE_def";

val FINITE_hasCard = Fin_Card |> rewr_rule[GSYM FINITE_def]

val Card_ex = prove_store("Card_ex",
e0
(strip_tac >>
 assume_tac Rel2Ar' >>
 qby_tac
 ‘?R: Exp(X,1+1) * N -> 1+1.
  !xs n.R o Pa(xs,n) = TRUE <=>
  (FINITE(xs) & hasCard(X) o Pa(xs,n) = TRUE) | 
  (~(FINITE(xs)) & n = O)’ >-- 
 (qexists_tac 
 ‘Or(And(isFinite(X) o p1(Exp(X,1+1),N),
         hasCard(X)),
     And(NEG o isFinite(X) o p1(Exp(X,1+1),N),Eq(N) o Pa(p2(Exp(X,1+1),N),O o To1(Exp(X,1+1) * N))))’
  >--  once_rw[GSYM Or_def] >> once_rw[o_assoc] >>
       once_rw[Pa_distr] >> once_rw[DISJ_def] >>
       once_rw[GSYM And_def] >> once_rw[o_assoc] >>
       once_rw[Pa_distr] >> once_rw[CONJ_def] >>
       once_rw[o_assoc] >> once_rw[Pa_distr] >>
       once_rw[Eq_property_TRUE] >>
       once_rw[o_assoc] >> once_rw[NEG_def]>>
       once_rw[TRUE_xor_FALSE] >> 
       once_rw[one_to_one_id] >> rw[idR] >>
       rw[p12_of_Pa] >> rw[GSYM FINITE_def])  >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘!xs. ?!n. R o Pa(xs,n) = TRUE’ >--
 (strip_tac >> uex_tac >> 
 arw[] >> 
 cases_on “FINITE(xs:1->Exp(X,1+1))” >> arw[] (* 2 *)
 >-- (drule FINITE_hasCard >>
     pop_assum (assume_tac o uex_expand) >> arw[]) >>
 qexists_tac ‘O’ >> rw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >> strip_tac >>
 cases_on “FINITE(xs:1->Exp(X,1+1))”
 >-- (arw[] >> 
      first_x_assum 
      (qsspecl_then [‘xs’] $ strip_assume_tac o uex_expand) >>
      rfs[] >> 
      qsuff_tac ‘f o xs = n’ 
      >-- (strip_tac >> arw[]) >> arw[]) >>
 arw[])
(form_goal
 “!X. ?cx:Exp(X,1+1) -> N. 
  !xs. (FINITE(xs) ==> hasCard(X) o Pa(xs,cx o xs) = TRUE) & 
       (~FINITE(xs) ==> cx o xs = O)”));






val Card_ex = prove_store("Card_ex",
e0
(strip_tac >>
 assume_tac Rel2Ar' >>
 qby_tac
 ‘?R: Exp(X,1+1) * N -> 1+1.
  !xs n.R o Pa(xs,n) = TRUE <=>
  (FINITE(xs) & hasCard(X) o Pa(xs,n) = TRUE) | 
  (~(FINITE(xs)) & n = O)’ >-- 
 (qexists_tac 
 ‘Or(And(isFinite(X) o p1(Exp(X,1+1),N),
         hasCard(X)),
     And(NEG o isFinite(X) o p1(Exp(X,1+1),N),Eq(N) o Pa(p2(Exp(X,1+1),N),O o To1(Exp(X,1+1) * N))))’
  >--  once_rw[GSYM Or_def] >> once_rw[o_assoc] >>
       once_rw[Pa_distr] >> once_rw[DISJ_def] >>
       once_rw[GSYM And_def] >> once_rw[o_assoc] >>
       once_rw[Pa_distr] >> once_rw[CONJ_def] >>
       once_rw[o_assoc] >> once_rw[Pa_distr] >>
       once_rw[Eq_property_TRUE] >>
       once_rw[o_assoc] >> once_rw[NEG_def]>>
       once_rw[TRUE_xor_FALSE] >> 
       once_rw[one_to_one_id] >> rw[idR] >>
       rw[p12_of_Pa] >> rw[GSYM FINITE_def])  >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘!xs. ?!n. R o Pa(xs,n) = TRUE’ >--
 (strip_tac >> uex_tac >> 
 arw[] >> 
 cases_on “FINITE(xs:1->Exp(X,1+1))” >> arw[] (* 2 *)
 >-- (drule FINITE_hasCard >>
     pop_assum (assume_tac o uex_expand) >> arw[]) >>
 qexists_tac ‘O’ >> rw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >> strip_tac >>
 cases_on “FINITE(xs:1->Exp(X,1+1))” >> arw[]
 (*>-- arw[] >>
 arw[]>-- (arw[] >> 
      first_x_assum 
      (qsspecl_then [‘xs’] $ strip_assume_tac o uex_expand) >>
      rfs[] >> 
      qsuff_tac ‘f o xs = n’ 
      >-- (strip_tac >> arw[]) >> arw[]) >>
 arw[] *))
(form_goal
 “!X. ?cx:Exp(X,1+1) -> N. 
  !xs. (FINITE(xs) ==> (!n. cx o xs = n <=> hasCard(X) o Pa(xs,n) = TRUE)) & 
       (~FINITE(xs) ==> cx o xs = O)”));


val Card_def = Card_ex |> strip_all_and_imp
                        |> ex2fsym0 "Card" ["X"]
                        |> gen_all
                        |> store_as "Card_def";


val CARD_ex = prove_store("CARD_ex",
e0
(rpt strip_tac >> qexists_tac ‘Card(X) o xs’ >> rw[])
(form_goal
 “!A X xs:A -> Exp(X,1+1). ?c. Card(X) o xs = c”));

val CARD_def = CARD_ex |> spec_all |> ex2fsym0 "CARD" ["xs"]
                       |> gen_all
                       |> store_as "CARD_def";

(*want CARD: Exp(X,1+1) -> N.
 hasCard: Exp(X,1+1) * N -> 2.

 Exp(X,1+1) -> Exp(N,1+1)

 Exp(N,1+1) -> N

 

*)
