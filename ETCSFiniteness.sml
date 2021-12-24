val p31_ex = prove_store("p31_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p31: A * B * C ->A. p1(A,B * C) = p31”));

val p31_def = p31_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p31" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all

val p32_ex = prove_store("p32_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(B,C) o p2(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p32: A * B * C ->B.p1(B,C) o p2(A,B * C) = p32”));

val p32_def = p32_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p32" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all

val p33_ex = prove_store("p33_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(B,C) o p2(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p33: A * B * C ->C.p2(B,C) o p2(A,B * C) = p33”));

val p33_def = p33_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p33" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all

                    

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




val p31_of_Pa = prove_store("p31_of_Pa",
                            e0
                                (rpt strip_tac >> rw[GSYM p31_def,p1_of_Pa] )
                                (form_goal
                                     “!A B C X a:X-> A bc: X-> B * C. p31(A,B,C) o Pa(a, bc) = a”));


val p32_of_Pa = prove_store("p32_of_Pa",
e0
(rpt strip_tac >> rw[GSYM p32_def,o_assoc,p12_of_Pa] )
(form_goal
“!A B C X a:X-> A b: X-> B c: X-> C. p32(A,B,C) o Pa(a, Pa(b,c)) = b”));


val p33_of_Pa = prove_store("p33_of_Pa",
e0
(rpt strip_tac >> rw[GSYM p33_def,o_assoc,p2_of_Pa] )
(form_goal
“!A B C X a:X-> A b: X-> B c: X-> C. p33(A,B,C) o Pa(a, Pa(b,c)) = c”));

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




val Pa3_ex = prove_store("Pa3_ex",
e0
(rpt strip_tac >> qexists_tac ‘Pa(f,Pa(g,h))’ >> rw[])
(form_goal
 “!A B C X f:X->A g:X ->B h:X->C. ?Pa3.
 Pa(f,Pa(g,h)) = Pa3 
”));


val Pa3_def = Pa3_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa3" ["f","g","h"]
              |> C mp (trueI []) |> gen_all

val Pa4_ex = prove_store("Pa4_ex",
e0
(rpt strip_tac >> qexists_tac ‘Pa(f,Pa(g,Pa(h,j)))’ >> rw[])
(form_goal
 “!A B C D X f:X->A g:X ->B h:X->C j:X->D. ?Pa4.
 Pa(f,Pa(g,Pa(h,j))) = Pa4
”));

val Pa4_def = Pa4_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa4" ["f","g","h","j"]
              |> C mp (trueI []) |> gen_all

val p41_ex = prove_store("p41_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A, B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p41. p1(A,B * C * D) = p41”));

val p41_def = p41_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p41" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val p42_ex = prove_store("p42_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p42. p1(B, C * D) o p2(A,B * C * D) = p42”));


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


val fst_conjunct = 
rastt $ q2str 
‘Ev(Exp(X,1+1),1+1) o Pa(p42(X,Exp(X,1+1),Exp(X,1+1),Exp(Exp(X,1+1),1+1)),p44(X,Exp(X,1+1),Exp(X,1+1),Exp(Exp(X,1+1),1+1)) )’


val snd_conjunct = 
rastt $ q2str
‘Eq(Exp(X,1+1)) o Pa(p43(X,Exp(X,1+1),Exp(X,1+1),Exp(Exp(X,1+1),1+1)),
 Ins(p41(X,Exp(X,1+1),Exp(X,1+1),Exp(Exp(X,1+1),1+1)),
     p42(X,Exp(X,1+1),Exp(X,1+1),Exp(Exp(X,1+1),1+1))))’



val trd_conjunct = 
rastt $ q2str
‘NEG o Ev(X,1+1) o Pa(p41(X,Exp(X,1+1),Exp(X,1+1),Exp(Exp(X,1+1),1+1)),p42(X,Exp(X,1+1),Exp(X,1+1),Exp(Exp(X,1+1),1+1)))’

fun mk_o a1 a2 = mk_fun "o" [a1,a2]

val CONJ = mk_fun "CONJ" []

fun Pa f g = mk_fun "Pa" [f,g]

fun Ex X = mk_fun "Ex" [X]

fun Tp f = mk_fun "Tp" [f]

val from4_pred0 = 
mk_o CONJ $
 Pa trd_conjunct (mk_o CONJ (Pa fst_conjunct snd_conjunct))



val Ex_x_from4_pred = 
 mk_o (Ex (mk_ob "X")) (Tp from4_pred0)
 
val Ex_s0_Ex_x_from4_pred = 
mk_o (rastt "Ex(Exp(X,1+1))") (Tp Ex_x_from4_pred)

val required_map2 = Tp Ex_s0_Ex_x_from4_pred


val map2_ex = prove_store("map2_ex",
e0
(exists_tac required_map2 >> rw[])
(form_goal
$ mk_exists "m2" (sort_of required_map2)
(mk_eq required_map2 (rastt "m2:Exp(Exp(X, 1+1), 1+1) -> Exp(Exp(X, 1+1), 1+1)")) 
));


val map2_def = 
    map2_ex |> eqT_intro
            |> iffRL |> ex2fsym "map2" ["X"]
            |> C mp (trueI []) |> gen_all


val Empty_ex = prove_store("Empty_ex",
e0
(strip_tac >> qexists_tac ‘Tp(False(X) o p1(X,1))’ >> rw[])
(form_goal
“!X.?ept:1->Exp(X,1+1). Tp(False(X) o p1(X,1))= ept”));


val Empty_def = 
    Empty_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Empty" ["X"]
             |> C mp (trueI []) |> gen_all

val required_map1 =
Tp (rastt $ q2str
‘Eq(Exp(X,1+1)) o Pa(id(Exp(X,1+1)),Empty(X) o To1(Exp(X,1+1))) o 
 p1(Exp(X,1+1),1)’)

val map1_ex = prove_store("map1_ex",
e0
(exists_tac required_map1 >> rw[])
(form_goal
$ mk_exists "m1" (sort_of required_map1)
(mk_eq required_map1 (rastt "m1:1 -> Exp(Exp(X, 1+1), 1+1)")) 
));


val map1_def = 
    map1_ex |> eqT_intro
            |> iffRL |> ex2fsym "map1" ["X"]
            |> C mp (trueI []) |> gen_all

fun Nind x t = mk_fun "Nind" [x,t]

val card0 = Nind (rastt "map1(X)") (rastt "map2(X)")


val hasCard =
mk_o (rastt "Ev(Exp(X,1+1),1+1)") 
(Pa (rastt "p1(Exp(X,1+1),N)")
 (mk_o card0 (rastt "p2(Exp(X,1+1),N)")))



val Mem_ex = prove_store("Mem_ex",
e0
(strip_tac >> qexists_tac ‘Ev(X,1+1)’ >> rw[])
(form_goal
 “!X. ?mem. Ev(X,1+1) = mem”));

val Mem_def = Mem_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Mem" ["X"]
             |> C mp (trueI []) |> gen_all



val contain_empty = 
mk_o (rastt "Mem(Exp(X,1+1))") $
Pa
(rastt "Empty(X) o To1(Exp(Exp(X,1+1),1+1))")
(rastt "id(Exp(Exp(X,1+1),1+1))")



val longpred_ant = rastt "Ev(Exp(X,1+1),1+1)"
(*mk_o (rastt "Ev(Exp(X,2),2)")
(Pa (rastt "Pr2(X,Exp(X,2),Exp(Exp(X,2),2))")
 (rastt "Pr3(X,Exp(X,2),Exp(Exp(X,2),2))"))
*)

val longpred_conc = 
rastt $ q2str
‘All(X) o Tp(Ev(Exp(X,1+1),1+1) o 
 Pa(Ins(p31(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1)),
           p32(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1))),
p33(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1))))’

val IMP = mk_fun "IMP" []

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

(*fun Exp A B = mk_fun "Exp" [A,B]*)

val two = rastt "1+1";
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




val p31_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p31_def,p1_of_Pa])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p31(A,B,C) o Pa3(f,g,h) = f”)



val p32_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p32_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p32(A,B,C) o Pa3(f,g,h) = g”)


val p33_of_Pa3 = prove_store("p33_of_Pa3",
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p33_def,p2_of_Pa,o_assoc])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p33(A,B,C) o Pa3(f,g,h) = h”));

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


val Ev_of_Tp_el' = prove_store("Ev_of_Tp_el'",
e0
(rpt strip_tac >> 
 qby_tac ‘Tp(f) = Tp(f) o id(P)’ >-- rw[idR] >>
 once_arw[] >> rw[Ev_of_Tp_el])
(form_goal
“!A B P f:A * P -> B  a:P -> A.
Ev(A, B) o Pa(a, Tp(f)) = f o Pa(a, id(P))”));


val Ev_of_el = prove_store("Ev_of_el",
e0
(rpt strip_tac >>
 qby_tac 
 ‘f = Tp1(Tp0(f))’ >-- rw[Tp1_Tp0_inv] >> once_arw[] >>
 rw[GSYM Tp1_def,Ev_of_Tp_el'] >> rw[Tp1_def,Tp1_Tp0_inv] >>
 rw[o_assoc,p1_of_Pa,idR])
(form_goal
 “!A B f:1->Exp(A,B) a:1->A.
  Ev(A,B) o Pa(a,f) = Tp0(f) o a”));


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

fun Po A B = mk_fun "*" [A,B]

val hasCard_ex = prove_store("hasCard_ex",
e0
(strip_tac >> 
 exists_tac hasCard >> rw[])
(form_goal $
mk_forall "X" ob_sort
 (mk_exists "f" (ar_sort (Po (Exp (mk_ob "X") two) N) two)
  (mk_eq hasCard (rastt "f:Exp(X,1+1) * N -> 1+1")))
));


val hasCard_def = 
hasCard_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "hasCard" ["X"] 
            |> C mp (trueI []) |> gen_all

val _ = new_pred "FINITE" [("X",ob_sort)]

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




val N_equality = prove_store("N_equality",
e0
(rpt strip_tac >> fs[Nind_def])
(form_goal
“!X x0:1->X t. Nind(x0,t) o O = x0 &
  Nind(x0,t) o SUC = t o Nind(x0,t)”));



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





val p41_of_Pa4 = prove_store("p41_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p41_def,p12_of_Pa])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p41(A,B,C,D) o Pa4(f,g,h,k) = f”));

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


val p44_of_Pa4 = prove_store("p44_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p44_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p44(A,B,C,D) o Pa4(f,g,h,k) = k”));

val hasCard_property = prove_store("hasCard_property",
e0
(strip_tac >> rw[GSYM hasCard_def] >> strip_tac >--
  (rw[o_assoc,Pa_distr,p12_of_Pa] >>
  rw[N_equality] >> rw[GSYM map1_def] >>
  rw[Ev_of_Tp_el'] >> rw[o_assoc,Pa_distr,p12_of_Pa,idL] >>
  once_rw[one_to_one_id] >> rw[idR] >> 
  once_rw[GSYM True1TRUE] >> rw[GSYM Eq_property]) >>
 strip_tac >> strip_tac >>
 rw[o_assoc,Pa_distr,p12_of_Pa] >>
 once_rw[GSYM o_assoc] >> rw[N_equality] >>
 once_rw[GSYM map2_def] >>
 rw[o_assoc,Pa_distr] >> rw[Ev_of_Tp_el] >>
 rw[o_assoc] >> rw[Ex_def] >> rw[o_assoc] >> rw[Ex_def] >>
 (*if use rw, then too slow*)
 once_rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[CONJ_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[map2_def] >>
 rw[o_assoc,NEG_def] >>
 once_rw[Pa_distr] >> once_rw[Pa4_def] >> 
 once_rw[p42_of_Pa4] >> once_rw[p41_of_Pa4] >>
 once_rw[p43_of_Pa4] >> once_rw[p44_of_Pa4] >>
 rw[GSYM Ins_def] >> rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[p42_of_Pa4] >> once_rw[p41_of_Pa4] >>
 once_rw[GSYM True1TRUE] >>
 once_rw[GSYM Eq_property] >> once_rw[True1TRUE] >>
 once_rw[GSYM Mem_def] >> rpt strip_tac >>
 qexistsl_tac [‘s0’,‘x’] >> 
 once_arw[] >> fs[TRUE2FALSE]
 )
(form_goal
“!X. hasCard(X) o Pa(Empty(X),O) = TRUE &
 !s0 n. hasCard(X) o Pa(s0,n) = TRUE ==>
 !x:1->X. ~ (Mem(X) o Pa(x,s0) = TRUE) ==>
 hasCard(X) o Pa(Ins(x,s0),SUC o n) = TRUE”));


val Tp0_INJ = prove_store("Tp0_INJ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >-- 
 (once_rw[GSYM Tp1_Tp0_inv] >> arw[]) >> arw[])
(form_goal
 “!A B f:1->Exp(A,B) g:1->Exp(A,B).
  Tp0(f) = Tp0(g) <=> f = g”));

val pred_ext = prove_store("pred_ext",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (cases_on “p1:1->1+1 = TRUE” >-- fs[] >>
 fs[TRUE2FALSE] >> fs[TRUE_ne_FALSE] >>
 fs[TRUE2FALSE]) >>
 arw[])
(form_goal
“!p1 p2. (p1 = TRUE <=> p2 = TRUE) <=> p1 = p2”));


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





val Swap_ex = prove_store("Swap_ex",
e0
(rpt strip_tac >> qexists_tac ‘Pa(p2(A,B),p1(A,B))’ >> rw[])
(form_goal
 “!A B. ?swap:A * B ->B * A. Pa(p2(A,B),p1(A,B)) = swap”));

val Swap_def = 
    Swap_ex |> spec_all |> eqT_intro
               |> iffRL |> ex2fsym "Swap" ["A","B"] 
               |> C mp (trueI []) |> gen_all



val Swap_Pa = proved_th $
e0
(rw[GSYM Swap_def,Pa_distr] >> rpt strip_tac >>
 irule to_P_eq >> rw[p12_of_Pa])
(form_goal
“!A B X f:X->A g:X->B. Swap(A,B) o Pa(f,g) = Pa(g,f)”)



val NOT_IN_Empty = prove_store("NOT_IN_Empty",
e0
(rpt strip_tac >> rw[GSYM Mem_def,GSYM Empty_def,Ev_of_Tp_el',o_assoc] >> once_rw[one_to_one_id] >> rw[idR,False2FALSE]>>
 rw[TRUE2FALSE])
(form_goal
“!X x:1->X. ~(Mem(X) o Pa(x,Empty(X)) = TRUE)”));

val isFinite_hasCard0 = prove_store("isFinite_hasCard0",
e0
(rpt strip_tac >> fs[isFinite_property1] >>
 first_x_assum irule >> rw[o_assoc,Ex_def] >>
 rw[Swap_Pa] >> assume_tac hasCard_property >>
 rpt strip_tac (* 2 *) >--
 (cases_on “s0 = Empty(X)” (* 2 *) >--
  (qexists_tac ‘SUC o O’ >> 
   first_x_assum (qspecl_then [‘X’] strip_assume_tac) >>
   first_x_assum irule >> arw[NOT_IN_Empty]) >>
  cases_on “Mem(X) o Pa(e,s0) = TRUE” (* 2 *) >--
  (fs[ABSORPTION_RWT] (*fs bug here, so does arw[]*) >> qexists_tac ‘x’ >> arw[]) >>
  first_x_assum (qspecl_then [‘X’] strip_assume_tac) >>
  first_x_assum rev_drule >> first_x_assum drule >>
  qexists_tac ‘SUC o x’ >> arw[]) >>
 first_x_assum (qspecl_then [‘X’] strip_assume_tac) >>
 qexists_tac ‘O’ >> arw[])
(form_goal
 “!X a:1->Exp(X,1+1).isFinite(X) o a = TRUE ==>
   (Ex(N) o Tp(hasCard(X) o Swap(N,Exp(X,1+1)))) o a = TRUE”));

val isFinite_hasCard = prove_store("isFinite_hasCard",
e0
(rpt strip_tac >> drule isFinite_hasCard0 >>
 fs[o_assoc,Ex_def,Swap_Pa] >> qexists_tac ‘x’ >> arw[]) 
(form_goal
 “!X a:X->1+1.isFinite(X) o Tp1(a) = TRUE ==>
  ?n. hasCard(X) o Pa(Tp1(a),n) = TRUE”));

(*
FINITE(a:X->1+1) <=>
 isFinite(X) o Tp(a) = TRUE

make definition of FINITE 

th = 
P ==> !a. Q(a)


!a. Q(a)

irule with th 

strip_tac >> irule 


Theorem foo:
P a ==> !a. Q a
Proof
cheat
QED


“”

*)


val FINITE_hasCard = prove_store("FINITE_hasCard",
e0
(rpt strip_tac >> irule isFinite_hasCard >>
 fs[GSYM FINITE_def])
(form_goal
 “!X. FINITE(X) ==> ?n:1->N. hasCard(X) o Pa(Tp1(True(X)),n) = TRUE”));
 
val Card_def = 
    FINITE_hasCard |> spec_all |> ex2fsym "Card" ["X"] 
                   |> gen_all



(*

Inductive Cd:
R {} 0 ∧
(∀xs n x0. R xs n ∧ x0∉ xs ⇒  R ({x0} ∪ xs)  (SUC n) )
End

(*how does HOL know that the only thing which has card 0 is 0∃*)


Theorem foo:
!s0 n. R s0 n ⇒
 R s0 n ∧ ∀m. n = (SUC m) ⇒  ∃x0 xs0. x0∉ xs0 ∧ s0 = {x0} ∪ xs0 ∧ R xs0 m
Proof
ho_match_mp_tac Cd_ind >> simp[] >> rpt strip_tac
>> simp[Cd_rules] >>
qexists_tac ‘x0’ >> qexists_tac ‘s0’ >>
rw[]
QED

Theorem foo1:
∀s n. R s n ⇒ ∀x. x∈ s ⇒ R (s DELETE x) (n -1)
Proof
Induct_on ‘R’ >> simp[] >> rpt strip_tac
>- (rw[] >>
   ‘{x} ∪ s DELETE x = s’ by cheat >>
   fs[] ) >>
first_x_assum drule >> cheat
QED

                    
Theorem foo':
!n:num. !s:'a set. R s n ==> (!m. R s m ==> (n = m))
Proof
Induct_on ‘R’ >> strip_tac >- cheat >>
rpt strip_tac >>
‘R s (m - 1)’ by
(drule foo1 >> strip_tac >>
 first_x_assum (qspecl_then [‘x0’] assume_tac) >> fs[] >>
 ‘{x0} ∪ s DELETE x0 = s’ by
  (simp[EXTENSION] >> metis_tac[]) >>
 fs[]) >>
first_x_assum drule >>
strip_tac >> rw[] >>
cheat
QED


*)
