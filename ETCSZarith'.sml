val relJ_ex = prove_store("relJ_ex",
e0
(exists_tac $
 form2IL [dest_var $ rastt "ab:1-> N * N",
          dest_var $ rastt "cd:1-> N * N"] 
 “Add(Fst(ab:1-> N * N),Snd(cd)) = Add(Snd(ab),Fst(cd))” >>
 rw[GSYM p21_def,GSYM p22_def,GSYM Add_def,
    Eq_property_TRUE,Pa_distr,p12_of_Pa,o_assoc,
    GSYM Fst_def,GSYM Snd_def])
(form_goal
 “?rel:(N * N) * N * N -> 1+1.
  !ab cd. rel o Pa(ab,cd) = TRUE <=> 
  Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))”));


(*thing to be defined should be on LHS Mul_def seems wrong direction*)


(*

!(ab : ar(1, N * N))  (cd : ar(1, N * N)).
               ADD o
                 Pa((p1(N, N) o p21(N * N, N * N)) o Pa(ab#, cd#), (p2(N, N)
                  o p22(N * N, N * N)) o Pa(ab#, cd#)) = ADD o
                 Pa((p2(N, N) o p21(N * N, N * N)) o Pa(ab#, cd#), (p1(N, N)
                  o p22(N * N, N * N)) o Pa(ab#, cd#)) <=>
               ADD o Pa(p1(N, N) o ab#, p2(N, N) o cd#) = ADD o
                 Pa(p2(N, N) o ab#, p1(N, N) o cd#)

edit pp after "," 

*)
val relJ_ex = prove_store("relJ_ex",
e0
(exists_tac $
 form2IL [dest_var $ rastt "ab:1-> N * N",
          dest_var $ rastt "cd:1-> N * N"] 
 “Add(Fst(ab:1-> N * N),Snd(cd)) = Add(Snd(ab),Fst(cd))” >>
 rw[o_assoc] >> rw[Pa_distr] >>
 rw[Eq_property_TRUE] >> rw[GSYM Add_def] >>
 rw[o_assoc] >> rw[Pa_distr] >>
 rw[GSYM Fst_def] >> rw[GSYM Snd_def] >>
 rw[GSYM p21_def,GSYM p22_def] >>
 rw[o_assoc,p12_of_Pa])
(form_goal
 “?rel:(N * N) * N * N -> 1+1.
  !ab cd. rel o Pa(ab,cd) = TRUE <=> 
  Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))”));


val relJ_def = relJ_ex |> ex2fsym0 "relJ" []

val _ = new_psym2IL ("Sim",(mk_fun "relJ" [],[]))

val Sim_def = define_pred 
“!X ab cd. Sim(ab,cd) <=> relJ o Pa(ab,cd) = True(X)”


val PZ_ex = prove_store("PZ_ex",
e0
(exists_tac $
 form2IL [dest_var $ rastt "pairs:1->Exp(N* N,1+1)"] 
 “?ab:1-> N * N. IN(ab,pairs:1->Exp(N* N,1+1)) &
      (!cd. IN(cd,pairs) <=> Sim(ab,cd))” >>
 rw[ALL_property,GSYM And_def,CONJ_def,o_assoc,Pa_distr,
    Eq_property_TRUE,GSYM Iff_def,IFF_def,
    EX_property] >> 
 rw[GSYM p21_def,GSYM p22_def,p12_of_Pa] >>
 rw[p31_of_Pa3,p32_of_Pa3,p33_of_Pa3,Pa3_def,
    IN_def,Sim_def,True1TRUE])
(form_goal
 “?P: Exp(N * N,1+1) -> 1+1.
  !pairs:1->Exp(N * N,1+1). P o pairs = TRUE <=>
  (?ab. IN(ab,pairs) &
      (!cd. IN(cd,pairs) <=> Sim(ab,cd)))”));




val pred_define_Z_ex = prove_store("pred_define_Z_ex",
e0
(exists_tac $
 form2IL [dest_var $ rastt "pairs:1->Exp(N* N,1+1)"] 
 “!ab:1->N * N cd. IN(ab,pairs) & IN(cd,pairs) ==> 
          Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))” >>
 rw[ALL_property,GSYM Imp_def,IMP_def,o_assoc,Pa_distr,
    Eq_property_TRUE,GSYM And_def,CONJ_def] >> 
 rw[GSYM Fst_def,GSYM Snd_def] >>
 rw[GSYM p31_def,GSYM p32_def,GSYM p33_def] >>
 rw[o_assoc,Pa_distr] >> rw[p12_of_Pa] >>
 rw[GSYM Add_def,Pa_distr,p12_of_Pa,o_assoc] >>
 rw[GSYM IN_def1])
(form_goal
 “?P: Exp(N * N,1+1) -> 1+1.
  !pairs:1->Exp(N * N,1+1). P o pairs = TRUE <=>
  !ab cd. IN(ab,pairs) & IN(cd,pairs) ==> 
          Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))”));



val pred_define_Z_ex = prove_store("pred_define_Z_ex",
e0
(exists_tac $
 form2IL [dest_var $ rastt "pairs:1->Exp(N* N,1+1)"] 
 “!ab:1->N * N cd. IN(ab,pairs) & IN(cd,pairs) ==> 
          Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))” >>
 rw[ALL_property,GSYM Imp_def,IMP_def,o_assoc,Pa_distr,
    Eq_property_TRUE,GSYM And_def,CONJ_def,GSYM Fst_def,GSYM Snd_def,GSYM p31_def,GSYM p32_def,GSYM p33_def,o_assoc,Pa_distr,p12_of_Pa,GSYM Add_def,Pa_distr,GSYM IN_def1])
(form_goal
 “?P: Exp(N * N,1+1) -> 1+1.
  !pairs:1->Exp(N * N,1+1). P o pairs = TRUE <=>
  !ab cd. IN(ab,pairs) & IN(cd,pairs) ==> 
          Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))”));


val pred_define_Z = pred_define_Z_ex |> ex2fsym0 "PZ" []
 


(*
val TY_DEF = define_pred
“TY_DEF(P:A->1+1,rep:B -> A) <=> 
 Mono(rep) & !X a:X->A. P o a = True(A) <=> ”

TYPE_DEFINITION is just pred_subset_ex'
*)


val Z_def = pred_subset_ex' 
            |> specl [rastt "Exp(N * N,1+1)",rastt "PZ"]
            |> ex2fsym0 "Z" []
            |> ex2fsym0 "repZ" []

val ADDj_ex = prove_store("ADDj_ex",
e0
(qexists_tac
 ‘Pa(ADD o Pa(p1(N,N) o p1(N * N,N * N),
             p1(N,N) o p2(N * N,N * N)) , 
    ADD o Pa(p2(N,N) o p1(N * N,N * N),
             p2(N,N) o p2(N * N,N * N)))’ >> rw[])
(form_goal
 “?addj. 
 Pa(ADD o Pa(p1(N,N) o p1(N * N,N * N),
             p1(N,N) o p2(N * N,N * N)) , 
    ADD o Pa(p2(N,N) o p1(N * N,N * N),
             p2(N,N) o p2(N * N,N * N)))= addj”));


val ADDj_def = ex2fsym0 "ADDj" [] ADDj_ex;



val MULj_ex = prove_store("MULj_ex",
e0
(qexists_tac
 ‘Pa(Add(Mul(p1(N,N) o p1(N * N,N * N),p1(N,N) o p2(N * N,N * N)),
        Mul(p2(N,N) o p1(N * N,N * N),p2(N,N) o p2(N * N,N * N))),
    Add(Mul(p1(N,N) o p1(N * N,N * N),p2(N,N) o p2(N * N,N * N)),
        Mul(p2(N,N) o p1(N * N,N * N),p1(N,N) o p2(N * N,N * N))))’ >> rw[])
(form_goal
 “?mulj. 
 Pa(Add(Mul(p1(N,N) o p1(N * N,N * N),p1(N,N) o p2(N * N,N * N)),
        Mul(p2(N,N) o p1(N * N,N * N),p2(N,N) o p2(N * N,N * N))),
    Add(Mul(p1(N,N) o p1(N * N,N * N),p2(N,N) o p2(N * N,N * N)),
        Mul(p2(N,N) o p1(N * N,N * N),p1(N,N) o p2(N * N,N * N)))) = mulj”));

val MULj_def = ex2fsym0 "MULj" [] MULj_ex;

val Mulj_ex = prove_store("Mulj_ex",
e0
(rpt strip_tac >> qexists_tac ‘MULj o Pa(ab,cd)’ >> rw[])
(form_goal “!X ab:X->N * N cd. ?m.MULj o Pa(ab,cd) = m”));

val Mulj_def = Mulj_ex |> spec_all |> ex2fsym0 "Mulj" ["ab","cd"]
              |> gen_all |> store_as "Mulj_def";


val element_not_zero = prove_store("element_not_zero",
e0
(rpt strip_tac >> ccontra_tac >> drule zero_no_MEM >>
 qsuff_tac ‘?f:1->A.T’ >-- arw[] >>
 qexists_tac ‘f’ >> arw[])
(form_goal
 “!A f:1->A. ~is0(A)”));

val Z_non_zero = prove_store("Z_non_zero",
e0
(qsuff_tac ‘?f:1->Z.T’ >-- (strip_tac >>
 qsspecl_then [‘f’] accept_tac element_not_zero) >>
 strip_assume_tac Z_def >>
 qsuff_tac
 ‘?pairs:1->Exp(N * N,1+1). PZ o pairs = TRUE’ 
 >-- (fs[GSYM True1TRUE] >> strip_tac >> qexists_tac ‘x0’ >> rw[]) >>
 pop_assum (K all_tac) >>
 rw[pred_define_Z] >>
 qby_tac
 ‘?P:N * N->1+1. 
 !pair:1->N * N. P o pair = TRUE <=> Fst(pair) = Snd(pair)’ 
 >-- (exists_tac $ 
     (form2IL [dest_var $ rastt "pair:1->N * N"] 
     “Fst(pair:1->N * N) = Snd(pair)”) >>
     rw[o_assoc,Eq_property_TRUE,GSYM p11_def,Pa_distr,GSYM Fst_def,
       GSYM Snd_def,idL]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘Tp1(P)’ >> 
 arw[GSYM Tp1_def,IN_def1,GSYM Mem_def,
     Ev_of_Tp_el',o_assoc,p12_of_Pa] >> rpt strip_tac >>
 arw[])
(form_goal “~is0(Z)”));

val absZ_ex = prove_store("absZ_ex",
e0
(rpt strip_tac >>
 qsuff_tac ‘?pinv:Exp(N * N,1+1) ->Z. pinv o repZ = id(Z)’
 >-- (strip_tac >> qexists_tac ‘pinv’ >> 
     arw[Z_def] >> rpt strip_tac >> dimp_tac >>
     strip_tac >-- (arw[] >>
     qby_tac ‘repZ o pinv o repZ o x0 = repZ o (pinv o repZ) o x0’ 
     >-- arw[o_assoc] >> arw[idL]) >>
     qexists_tac ‘pinv o pairs’ >> arw[]) >>
 irule Mono_no_zero_post_inv >> rw[Z_def] >> 
 rw[Z_non_zero])
(form_goal
 “?abs:Exp(N * N,1+1) ->Z. 
  abs o repZ = id(Z) & 
  (!X pairs:X->Exp(N * N,1+1). 
   PZ o pairs = True(X) <=> repZ o abs o pairs = pairs)”));

val absZ_def = absZ_ex |> ex2fsym0 "absZ" [] |> store_as "absZ_def";

val ADDs0_ex = prove_store("ADDs0_ex",
e0
(exists_tac $
 form2IL [dest_var $ rastt "ab:1-> N * N",
          dest_var $ rastt "ps1:1->Exp(N * N,1+1)",
          dest_var $ rastt "ps2:1->Exp(N * N,1+1)"] 
 “(?r1:1->N * N r2. IN(r1,ps1) & IN(r2,ps2) & Addj(r1,r2) = ab)” >>
 rw[EX_property] >> 
 rw[GSYM And_def,Pa_distr,o_assoc,CONJ_def] (*slow*) >>
 once_rw[Eq_property_TRUE] >>
 once_rw[Pa_distr] >> once_rw[Pa5_def] >> 
 once_rw[p52_of_Pa5] >> once_rw[p53_of_Pa5] >> 
 once_rw[p54_of_Pa5] >> once_rw[p51_of_Pa5] >> 
 once_rw[p55_of_Pa5] >> once_rw[GSYM Addj_def] >>
 rw[o_assoc] >> once_rw[Pa_distr] >> 
 once_rw[p52_of_Pa5] >> once_rw[p51_of_Pa5] >>
 rw[IN_def,True1TRUE])
(form_goal
 “?P: (N * N) * Exp(N * N,1+1) * Exp(N * N,1+1) -> 1+1.
  !ab ps1 ps2. P o Pa(ab,Pa(ps1,ps2)) = TRUE <=> 
  (?r1 r2. IN(r1,ps1) & IN(r2,ps2) & Addj(r1,r2) = ab)”));


 rw[EX_property,GSYM And_def,Pa_distr,o_assoc,CONJ_def,Eq_property_TRUE,Pa_distr,Pa5_def,p52_of_Pa5,p53_of_Pa5,p54_of_Pa5,p51_of_Pa5,p55_of_Pa5,GSYM Addj_def,o_assoc,Pa_distr,p52_of_Pa5,p51_of_Pa5,IN_def,True1TRUE]


val ADDs0_ex = prove_store("ADDs0_ex",
e0
(exists_tac $
 form2IL [dest_var $ rastt "ab:1-> N * N",
          dest_var $ rastt "ps1:1->Exp(N * N,1+1)",
          dest_var $ rastt "ps2:1->Exp(N * N,1+1)"] 
 “(?r1:1->N * N r2. IN(r1,ps1) & IN(r2,ps2) & Addj(r1,r2) = ab)” >>
 rw[EX_property,GSYM And_def,Pa_distr,o_assoc,CONJ_def] (*slow*) >>
 rw[Eq_property_TRUE,Pa_distr,Pa5_def,p52_of_Pa5,p53_of_Pa5] >> 
 rw[p54_of_Pa5,p51_of_Pa5,p55_of_Pa5,GSYM Addj_def,o_assoc,Pa_distr,p52_of_Pa5,p51_of_Pa5,IN_def,True1TRUE])
(form_goal
 “?P: (N * N) * Exp(N * N,1+1) * Exp(N * N,1+1) -> 1+1.
  !ab ps1 ps2. P o Pa(ab,Pa(ps1,ps2)) = TRUE <=> 
  (?r1 r2. IN(r1,ps1) & IN(r2,ps2) & Addj(r1,r2) = ab)”));


val ADDs0_def = ADDs0_ex |> ex2fsym0 "ADDs0" []

val ADDs_ex = prove_store("ADDs_ex",
e0
(qexists_tac ‘Tp(ADDs0)’ >> rw[])
(form_goal “?adds. Tp(ADDs0) = adds”));

val ADDs_def = ADDs_ex |> ex2fsym0 "ADDs" []

val IN_ADDs = prove_store("IN_ADDs",
e0
(rw[GSYM ADDs_def,IN_def,GSYM Mem_def,Ev_of_Tp_el,
    True1TRUE,ADDs0_def])
(form_goal
 “!ps1 ps2 ab:1-> N * N. IN(ab, ADDs o Pa(ps1,ps2)) <=> 
  ?r1 r2. IN(r1,ps1) & IN(r2,ps2) & Addj(r1,r2) = ab”));


(*
val ADDs_property = prove_store("ADDs_property",
e0
(rw[GSYM ADDs_def,IN_def,GSYM Mem_def,Ev_of_Tp_el,
    True1TRUE,ADDs0_def])
(form_goal
 “!ps1 ps2 abs:1-> N * N.
  ADDs o Pa()
 IN(ab, ADDs o Pa(ps1,ps2)) <=> 
  ?r1 r2. IN(r1,ps1) & IN(r2,ps2) & Addj(r1,r2) = ab”));
*)
val PZ_def = pred_define_Z

val PZ_refl = prove_store("PZ_refl",
e0
()
(form_goal
 “!ab:1->N * N. PZ o Pa(ab,ab) = TRUE”));


val IN_repZ = prove_store("IN_repZ",
e0
()
(form_goal
 “!z:1->Z r. IN(r,repZ o z) <=> 
   (!r'. IN(r',repZ o z) <=> PZ o Pa(r,r') = TRUE)”));

val ADDz_ex = prove_store("ADDz_ex",
e0
(dflip_tac >> rw[GSYM Z_def] >>
 irule FUN_EXT >> strip_tac >>
 rw[True2TRUE] >> rw[o_assoc,pred_define_Z] >>
 rw[IN_ADDs,Pa_distr] >> 
 qsspecl_then [‘a’] strip_assume_tac has_components >>
 arw[o_assoc,p12_of_Pa] >> rpt strip_tac >>
 
 )
(form_goal
 “?addz:Z * Z -> Z. repZ o addz =
   ADDs o Pa(repZ o p1(Z,Z),repZ o p2(Z,Z))”));


 “!ADDs:Exp(N * N,1+1) * Exp(N * N,1+1) -> Exp(X,1+1). 
   Tp() =  ADDs”));

val ADDz_ex = prove_store("ADDz_ex",
e0
()
(form_goal
 “?add:Z * Z ->Z. 
  !z1 z2:1->Z pairs. repZ o add o Pa(z1,z2) = pairs <=> 
  !pair:1->N * N. IN(pair,pairs) <=> 
  ?
  ”));




“!P. ?pred. P(x) <=> pred o x = TRUE”

“”
