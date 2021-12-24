
val INV_SUC_EQ = prove_store("INV_SUC_EQ",
e0
(assume_tac Thm2_2 >> fs[Mono_def] >> 
 rpt strip_tac >> dimp_tac >> strip_tac >--
 (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal 
“!m n:1->N. SUC o m = SUC o n <=> m = n”));
(*SUC_EQ_IFF_EQ is just INV_SUC_EQ*)




val SoE_lemma_2_5_5 = proved_th $
e0
(rw[iscoPr_def] >> rpt strip_tac >>
 uex_tac >> 
 qexists_tac 
 ‘p2(N,X) o Nind(Pa(O, f), Pa(SUC, g) o p1(N,X))’ >>
 rw[o_assoc,Nind_def,p12_of_Pa] >>
 rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc] >>
 qby_tac ‘p1(N, X) o Nind(Pa(O, f), Pa(SUC, g) o p1(N, X)) = 
 id(N)’ >-- 
 (irule comm_with_SUC_id >>
  rw[Nind_def,o_assoc,p1_of_Pa] >> 
  rw[GSYM o_assoc,p1_of_Pa]) >> 
 arw[idR] >> 
 qsuff_tac 
 ‘!fg:N->X. fg o O = f:1->X & fg o SUC = g ==>
   Pa(id(N),fg) = Nind(Pa(O, f), Pa(SUC, g) o p1(N,X))’
 >-- (strip_tac >> strip_tac >> disch_tac >>
     first_assum drule >> 
     qby_tac 
     ‘p2(N,X) o Pa(id(N), fg') = 
      p2(N,X) o Nind(Pa(O, f), Pa(SUC, g) o p1(N, X))’
     >-- arw[] >> fs[p2_of_Pa]) >>
 rpt strip_tac >> 
 assume_tac Nind_def >>
 first_assum (qspecl_then [‘N * X’,‘Pa(SUC, g) o p1(N, X)’,‘Pa(O, f)’] strip_assume_tac) >>
 first_assum irule >> rw[o_assoc,p12_of_Pa,Pa_distr,idR] >>
 rw[Pa_eq_eq] >> arw[idL])
(form_goal “iscoPr(O,SUC)”);



val O_xor_SUC = prove_store("O_xor_SUC",
e0
(strip_tac >> assume_tac SoE_lemma_2_5_5 >>
 drule copr_disjoint >>
 first_x_assum (qspecl_then [‘n’] assume_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 cases_on “n = O” >> arw[] >>
 ccontra_tac >> fs[] >> pop_assum mp_tac >>
 rw[] >> once_rw[one_to_one_id] >>
 arw[idR] >> qexists_tac ‘id(1)’ >> rw[]
 )
(form_goal
“!n:1->N. ~(n = O) <=> ?n0:1->N. n = SUC o n0”));


val PRED_O_cases = prove_store("PRED_O_cases",
e0
(assume_tac PRE_def >> strip_tac >>
 cases_on “n = O” >-- arw[] >>
 arw[] >> assume_tac O_xor_SUC >>
 first_x_assum (qspecl_then [‘n’] assume_tac) >>
 rfs[] >> arw[GSYM o_assoc,idL] >>
 assume_tac INV_SUC_EQ >> arw[])
(form_goal
“!n:1->N. PRE o n = O <=> (n = O | n = SUC o O)”));



val PRE_eq_0 = prove_store("PRE_eq_0",
e0
(strip_tac >> assume_tac PRE_def >> cases_on “n = O” >>
 arw[] >> dimp_tac >> strip_tac (* 2 *) >--
 (assume_tac O_xor_SUC >> 
 first_x_assum (qspecl_then [‘n’] assume_tac) >>
 rfs[] >> fs[GSYM o_assoc,idL] >> rfs[idL] >> 
 arw[] >> arw[GSYM o_assoc,idL]) >>
 arw[GSYM o_assoc,idL])
(form_goal
“!n:1->N. PRE o n = O <=> (n = O | n = SUC o O)”));



val NE_ex = prove_store("NE_ex",
e0
(rpt strip_tac >> 
 qspecl_then [‘N’] assume_tac Diag_Mono >> drule Thm5 >>
 first_x_assum accept_tac)
(form_goal
“?NE ne:NE -> N * N. Mono(ne) & Iso(coPa(Diag(N),ne))”));

val SUB_def = Thm1 |> specl
(List.map rastt ["N","N","id(N)","PRE o p2(N * N,N)"])
|> uex_expand |> ex2fsym0 "SUB" [] |> rewr_rule[idL]
|> store_as "SUB_def";

val SUB_eqn = SUB_def |> conjE1 |> store_as "SUB_eqn";

val Suc_ex = prove_store("Suc_ex",
e0
(rpt strip_tac >> qexists_tac ‘SUC o n’ >> rw[])
(form_goal “!X n:X->N.?sn. SUC o n = sn”));

val Suc_def = Suc_ex |> spec_all |> ex2fsym0 "Suc" ["n"]
                     |> gen_all
                     |> store_as "Suc_def";


val Suc_ex = prove_store("Suc_ex",
e0
(rpt strip_tac >> qexists_tac ‘SUC o n’ >> rw[])
(form_goal “!X n:X->N.?sn. SUC o n = sn”));

val Suc_def = Suc_ex |> spec_all |> ex2fsym0 "Suc" ["n"]
                     |> gen_all
                     |> store_as "Suc_def";


val Sub_ex = prove_store("Sub_ex",
e0
(rpt strip_tac >> qexists_tac ‘SUB o Pa(n1,n2)’ >> rw[])
(form_goal “!X n1:X->N n2:X->N.?sn12. SUB o Pa(n1,n2) = sn12”));

val Sub_def = Sub_ex |> spec_all 
                     |> ex2fsym0 "Sub" ["n1","n2"]
                     |> gen_all
                     |> store_as "Sub_def";

val Sub_property = SUB_def |> rewr_rule[Sub_def]
                           |> store_as "Sub_property"


(*TODO: automatic this:
 val it =
   A(u : ar(1, N))(pred : ar(N, 1 + 1))(a : ar(A, N))(At1 : ar(A, 1))
   1.isPb(pred, TRUE, a, At1)
   2.!(u : ar(1, N)). (?(a' : ar(1, A)). a o a'# = u#) <=> pred o u# = TRUE
   ----------------------------------------------------------------------
   (?(a' : ar(1, A)). u = a o a'#) <=> pred o u = TRUE
*)

val ind_principle = prove_store("ind_principle",
e0
(rpt strip_tac >> 
 qspecl_then [‘N’,‘1+1’,‘pred’,‘1’,‘TRUE’] 
 (x_choosel_then ["A","a","At1"] assume_tac) isPb_ex >>
 drule Pb_fac_iff_1 >> 
 qby_tac ‘!u. (?a':1->A. u = a o a') <=> pred o u = TRUE’
 >-- (strip_tac >> 
     (pop_assum (assume_tac o GSYM)) >> arw[] >>
     fconv_tac 
     (rand_fconv no_conv 
                 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "ar"))) >> arw[]) >>
 qby_tac ‘Mono(a)’
 >-- (drule Pb_Mono_Mono >> first_x_assum irule >>
      once_rw[from_one_Mono]) >>
 qby_tac ‘pred = TRUE o To1(N) <=> Iso(a)’ >-- 
 (dimp_tac >> strip_tac >--
  (irule Thm2_3' >> arw[] >> drule $ iffLR isPb_expand >>
  pop_assum strip_assume_tac >> rw[o_assoc] >>
  once_rw[one_to_one_id] >> rw[idR]) >>
  fs[Iso_def] >> irule FUN_EXT >> strip_tac >>
  rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR] >>
  drule $ iffLR isPb_def >> pop_assum strip_assume_tac >>
  qby_tac 
  ‘pred o (a o f') o a' = TRUE o At1 o f' o a'’
  >-- (rw[GSYM o_assoc] >> arw[]) >>
  rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
  fs[True_def] >>
  dimp_tac >> strip_tac (* 2 *) >--
  (fs[Iso_def] >> drule $ iffLR isPb_def >> 
   pop_assum strip_assume_tac >> 
   qby_tac 
   ‘!n0:1->N. pred o (a o f') o n0 = TRUE o At1 o f' o n0’
   >-- (strip_tac >> arw[GSYM o_assoc]) >>
   rpt strip_tac (* 2 *)
   >-- (first_x_assum (qspecl_then [‘O’] assume_tac) >> 
       rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
   first_x_assum (qspecl_then [‘SUC o n’] assume_tac) >> 
  rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
 irule Thm2_3' >> arw[])
(form_goal
“!pred:N->1 + 1. pred = True(N) <=>
 (pred o O = TRUE & 
  (!n:1->N. pred o n = TRUE ==> pred o SUC o n = TRUE))”));


val ind_principle_elements = prove_store
("ind_principle_elements",
e0
(rpt strip_tac >> 
 qspecl_then [‘pred’] assume_tac ind_principle >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule FUN_EXT >> rpt strip_tac >> 
      rw[GSYM True_def,o_assoc] >>
      once_rw[one_to_one_id] >> rw[idR] >> arw[]) >>
 arw[GSYM True_def] >> rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!pred:N->1+1. (!n.pred o n = TRUE) <=>
 (pred o O = TRUE & (!n:1->N. pred o n = TRUE ==> pred o SUC o n = TRUE))”));




val equality_ind = prove_store("equality_ind",
e0
(rpt strip_tac >> once_rw[GSYM Char_Diag] >>  fs[TRUE_def] >>
 qspecl_then [‘Char(Diag(A)) o Pa(f o (Pa(x o To1(N),id(N))), g o (Pa(y o To1(N),id(N))))’] mp_tac ind_principle_elements >>
 rw[o_assoc,Pa_distr] >> once_rw[one_to_one_id] >>
 rw[idL,idR])
(form_goal 
“!X A f:X*N->A Y g:Y*N->A.
 !x:1->X y:1->Y.(!n.f o Pa(x,n) = g o Pa(y,n)) <=>
 f o Pa(x,O) = g o Pa(y,O) & 
 !n0:1->N. f o Pa(x,n0) = g o Pa(y,n0) ==> 
 f o Pa(x,SUC o n0) = g o Pa(y,SUC o n0)”));


(*ind_one_component*)

val INDUCT_one_component = prove_store("INDUCT_one_component",
e0
(rpt strip_tac >> rw[equality_ind])
(form_goal
“!f:N * N->N g:N * N->N.
 !n0.(!n.f o Pa(n0,n) = g o Pa(n0,n)) <=>
 f o Pa(n0,O) = g o Pa(n0,O) & 
 !n:1->N. f o Pa(n0,n) = g o Pa(n0,n) ==> 
 f o Pa(n0,SUC o n) = g o Pa(n0,SUC o n)”));

val SUB = mk_fun "SUB" [];
val N = mk_fun "N" []
val O = mk_fun "O" []

val LEo_def = isPb_ex |> specl [Po N N,N,SUB,ONE,O] 
                       |> ex2fsym0 "LEo" []
                       |> store_as "LEo_def";

val LEo = mk_fun "LEo" [];

val LE_def = LEo_def |> ex2fsym0 "LE" [] |> store_as "LE_def"

val LE = mk_fun "LE" [];

val LE_Pb = prove_store("LE_Pb",
e0
(strip_assume_tac LE_def >> 
 pop_assum mp_tac >> once_rw[To1_def] >> rw[])
(form_goal “isPb(SUB,O,LE,To1(LEo))”));


val O_Mono = prove_store("O_Mono",
e0
(rw[from_one_Mono])
(form_goal “Mono(O)”));

val LE_Mono = prove_store("LE_Mono",
e0
(strip_assume_tac LE_def  >> drule Pb_Mono_Mono >> first_x_assum irule >>
 rw[O_Mono])
(form_goal “Mono(LE)”));

fun p1 A B = mk_fun "p1" [A,B]
fun p2 A B = mk_fun "p2" [A,B]

val NEo_def = NE_ex |> ex2fsym0 "NEo" []
                    |> store_as "NEo_def";

val NE_def = NEo_def |> ex2fsym0 "NE" []
                     |> store_as "NE_def";

val NE = mk_fun "NE" []

val NEo = mk_fun "NEo" []


val LTo_def = isPb_ex |> specl [LEo,Po N N,LE]
                      |> specl [NEo,NE] 
                      |> ex2fsym0 "LTo" []
                      |> store_as "LTo_def";

val LTLE_def = LTo_def |> ex2fsym0 "LTLE" []
                       |> store_as "LTLE_def";


val LTNE_def = LTLE_def |> ex2fsym0 "LTNE" []
                        |> store_as "LTNE_def";



val LT0_Mono = prove_store("LT_Mono",
e0
(irule o_Mono_Mono >> rw[NE_def] >>
 assume_tac LTNE_def >> drule Pb_reorder  >> drule Pb_Mono_Mono >> 
 first_x_assum irule >> rw[LE_Mono])
(form_goal “Mono(NE o LTNE)”));


val LT_ex = prove_store("LT_ex",
e0
(qexists_tac ‘NE o LTNE’ >> rw[])
(form_goal “?LT. NE o LTNE = LT”));

val LT_def = LT_ex |> ex2fsym0 "LT" [] |> store_as "LT_def"

(*
val Iso_Epi = prove_store("Iso_Epi",
e0
(rw[Iso_def,Epi_def] >> rpt strip_tac >>
 qsuff_tac ‘h o f o f' = g o f o f'’ 
 >-- (arw[idR] >> strip_tac >> arw[]) >> 
 arw[GSYM o_assoc])
(form_goal “!A B f:A->B. Iso(f) ==> Epi(f)”));


val iso_coPr_coPr = prove_store("iso_coPr_coPr",
e0
(rpt strip_tac >> rw[iscoPr_expand] >> rpt strip_tac >>
 drule $ iffLR Iso_def >> drule copa_def >> fs[] >>
 first_x_assum (qspecl_then [‘X'’,‘f’,‘g’] assume_tac) >>
 qexists_tac ‘copa(iA,iB,f,g) o f'’ >> rw[o_assoc] >>
 qby_tac ‘f' o f0 = iA & f' o g0 = iB’ >-- 
 (qby_tac ‘f' o copa(iA, iB, f0, g0) o iA = id(AB) o iA & 
           f' o copa(iA, iB, f0, g0) o iB = id(AB) o iB’
  >-- arw[GSYM o_assoc] >>
  pop_assum mp_tac >> drule i12_of_copa >> arw[idL]) >>
 arw[] >> 
 drule i12_of_copa >> arw[] >> 
 rpt strip_tac >> irule $ iffLR Epi_def >>
 qexistsl_tac [‘AB’,‘copa(iA, iB, f0, g0)’] >>
 drule Iso_Epi >> arw[o_assoc,idR] >>
 drule from_cop_eq >> first_x_assum irule >> 
 drule i12_of_copa >> arw[o_assoc]
 )
(form_goal “!A B AB iA:A->AB iB:B->AB. iscoPr(iA,iB) ==>
 !X f0:A->X g0:B->X. Iso(copa(iA,iB,f0,g0)) ==> iscoPr(f0,g0)”));


val copa_coPa = prove_store("copa_coPa",
e0
(rpt strip_tac >> flip_tac >> irule is_copa >> 
 rw[i12_of_coPa,i2_def])
(form_goal
 “!A X f:A->X B g:B->X. copa(i1(A,B),i2(A,B),f,g) = coPa(f,g)”));

*)


val NE_property = prove_store("NE_property",
e0
(rpt strip_tac >> strip_assume_tac NE_def >>
 fs[GSYM copa_coPa] >> 
 qspecl_then [‘N’,‘NEo’] assume_tac i2_def >>
 drule iso_coPr_coPr >> first_x_assum drule >>
 drule copr_disjoint >>
 fconv_tac (land_fconv no_conv (once_depth_fconv no_conv (rewr_fconv (eq_sym "ar")))) >> 
 pop_assum (assume_tac o GSYM) >>
 once_arw[] >> arw[fac_Diag_eq_iff |> rewr_rule[Diag_def]])
(form_goal 
 “!nn:1->N * N.(?nnb:1->NEo. NE o nnb = nn) <=> ~
 (p1(N,N) o nn = p2(N,N) o nn)”));




(*TODO: use char to define pred LESS,after removing all LE and LT etc*)


(*sub_z_iff_le*)
val SUB_EQ_00 = prove_store("SUB_EQ_00",
e0
(rpt strip_tac >> strip_assume_tac LE_def >> 
 drule $ iffLR isPb_expand >> pop_assum strip_assume_tac >>
 first_x_assum $ qspecl_then [‘1’,‘Pa(n1,n2)’,‘id(1)’] assume_tac >> 
 fs[idR] >> dimp_tac >> strip_tac (* 2 *)
 >-- (arw[GSYM o_assoc] >> rw[o_assoc] >>
      once_rw[one_to_one_id] >> rw[idR]) >>
 first_x_assum drule >>  pop_assum strip_assume_tac >>
 qexists_tac ‘a’ >> arw[])
(form_goal 
“!n1:1->N n2:1->N.
 (?le0:1->LEo. Pa(n1,n2) = LE o le0) <=>
 SUB o Pa(n1,n2) = O”));


(*sub_zero_id*)
val SUB_0_cj2 = prove_store("SUB_0_cj2",
e0
(strip_tac >> strip_assume_tac SUB_def >>
 qby_tac ‘SUB o Pa(p1(N, 1), O o p2(N, 1)) o Pa(n,id(1)) = 
          p1(N, 1) o Pa(n,id(1))’
 >-- arw[GSYM o_assoc] >> 
 pop_assum mp_tac >> rw[Pa_distr,p12_of_Pa] >> rw[o_assoc,p12_of_Pa,idR])
(form_goal 
“!n:1->N. SUB o Pa(n,O) = n”));

(*le_Z,LESS_EQ_00*)
val LE_O = prove_store("LE_O",
e0
(rpt strip_tac >> 
 qspecl_then [‘n0’,‘O’] assume_tac SUB_EQ_00 >>
 qby_tac ‘?le0. Pa(n0,O) = LE o le0’ 
 >-- (qexists_tac ‘a’ >> arw[]) >>
 assume_tac SUB_0_cj2 >> fs[])
(form_goal
“!n0:1->N a:1->LEo. Pa(n0,O) = LE o a ==> n0 = O”));

(*lt_le*)
val LT_IMP_LE = prove_store("LT_IMP_LE",
e0
(rpt strip_tac >> assume_tac LT_def >>
 assume_tac LTNE_def >> drule $ iffLR isPb_expand >>
 qexists_tac ‘LTLE o lt0’ >> arw[GSYM o_assoc])
(form_goal 
“!n1:1->N n2:1->N. 
 (?lt0: 1->LTo. Pa(n1,n2) = LT o lt0) ==>
 (?le0: 1->LEo. Pa(n1,n2) = LE o le0) ”));


(*lt_ne0*)
val LT_NOT_EQ00 = prove_store("LT_NOT_EQ00",
e0
(rpt strip_tac >> assume_tac LT_def >>
 assume_tac LTNE_def >> drule $ iffLR isPb_expand >>
 pop_assum strip_assume_tac >> fs[] >>
 qexists_tac ‘LTNE o lt0’ >> arw[GSYM o_assoc])
(form_goal 
“!n1:1->N n2:1->N. 
 (?lt0: 1->LTo. Pa(n1,n2) = LT o lt0) ==>
 (?ne0: 1->NEo. Pa(n1,n2) = NE o ne0)”));


(*lt_ne*)
val LT_NOT_EQ0 = prove_store("LT_NOT_EQ0",
e0
(strip_tac >> strip_tac >> disch_tac >>
 assume_tac LT_NOT_EQ00 >> first_x_assum drule >>
 assume_tac NE_property >> pop_assum mp_tac >>
 pop_assum (assume_tac o GSYM) >> strip_tac >> 
 pop_assum (assume_tac o iffLR) >> first_x_assum drule >>
 fs[p12_of_Pa])
(form_goal 
“!n1:1->N n2:1->N. 
 (?lt0: 1->LTo. Pa(n1,n2) = LT o lt0) ==> ~(n1 = n2)”));


(*le_ne_lt*)
val LE_NE_LT = prove_store("LE_NE_LT",
e0
(rpt strip_tac >>
 assume_tac LT_def >> assume_tac LTNE_def >>
 drule $ iffLR isPb_expand >> pop_assum strip_assume_tac >>
 assume_tac NE_property >>
 first_x_assum (qspecl_then [‘Pa(n1,n2)’] assume_tac)>>
 fs[p12_of_Pa] >>
 qpick_x_assum 
 ‘(?nnb : 1 -> NEo. NE o nnb = Pa(n1, n2)) <=> ~(n1 = n2)’
 (assume_tac o GSYM) >>
 fs[] >> 
 first_x_assum (qspecl_then [‘1’,‘le0’,‘nnb’] assume_tac) >>
 rfs[] >> qexists_tac ‘a’ >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >> fs[] >>
 arw[o_assoc] >> rw[GSYM LT_def] >> arw[o_assoc])
(form_goal 
“!n1:1->N n2:1->N.
 ((?le0: 1->LEo. Pa(n1,n2) = LE o le0) & ~(n1 = n2))
 ==> (?lt0: 1->LTo. Pa(n1,n2) = LT o lt0)”));


(*lt_iff_le_ne*)
val LT_iff_LE_NE = prove_store("LT_iff_LE_NE",
e0
(rpt strip_tac >> dimp_tac >> disch_tac (* 2 *)
 >-- (assume_tac LT_NOT_EQ0 >> first_x_assum drule >>
      assume_tac LT_IMP_LE >> first_x_assum drule >> arw[]) >>
 assume_tac LE_NE_LT >> first_x_assum drule >> arw[])
(form_goal 
“!n1:1->N n2:1->N.
 (?lt0: 1->LTo. Pa(n1,n2) = LT o lt0) <=> 
 ((?le0: 1->LEo. Pa(n1,n2) = LE o le0) & ~(n1 = n2))”));

(*clt_iff_le_ne*)
val CLT_iff_LE_NE = prove_store("CLT_iff_LE_NE",
e0
(rpt strip_tac >>
 assume_tac LT_iff_LE_NE >> pop_assum (assume_tac o GSYM) >>
 arw[] >>
 assume_tac LT0_Mono >>
 assume_tac $ GSYM LT_def >> fs[] >>
 drule Char_def >> fs[TRUE_def] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘x0’ >> arw[]) >>
 qexists_tac ‘lt0’ >> arw[])
(form_goal 
“!n1:1->N n2:1->N.
 (Char(LT) o Pa(n1, n2) = TRUE) <=> 
 ((?le0: 1->LEo. Pa(n1,n2) = LE o le0) & ~(n1 = n2))”));

(*not_lt_z *)
val NOT_LT_O = prove_store("NOT_LT_O",
e0
(rpt strip_tac >>
 ccontra_tac >>
 qby_tac
 ‘Char(LT) o Pa(n0, O) = TRUE <=> 
 (?a:1->LEo.Pa(n0,O) = LE o a) & ~(n0:1->N = O)’
 >-- rw[CLT_iff_LE_NE] >> fs[] >>
 drule LE_O >> fs[]  
 )
(form_goal 
“!n0:1->N. ~(Char(LT) o Pa(n0,O) = TRUE)”));

(*sub_def'*)
val SUB_def' = prove_store("SUB_def'",
e0
(strip_assume_tac SUB_def >>
 qby_tac 
 ‘SUB o Pa(p1(N, 1), O o p2(N, 1)) o Pa(id(N),To1(N)) =
  p1(N, 1) o Pa(id(N),To1(N))’ 
 >-- arw[GSYM o_assoc] >>
 fs[Pa_distr,p12_of_Pa,o_assoc])
(form_goal 
“SUB o Pa(id(N), O o To1(N)) = id(N) &
 PRE o SUB = SUB o Pa(p1(N,N), SUC o p2(N,N))”));



(*add_ex*)
val ADD_ex = prove_store("ADD_ex",
e0
(qspecl_then [‘N’,‘N’,‘id(N)’,‘SUC o p2(N * N,N)’] strip_assume_tac Thm1 >>
 pop_assum (strip_assume_tac o uex_expand) >> 
 first_x_assum (qspecl_then [‘f’] assume_tac) >> fs[] >>
 qexists_tac ‘f’ >> fs[o_assoc,idL,To1_def] >>
 qby_tac
 ‘f o Pa(p1(N, 1), O o To1(N * 1)) o Pa(id(N),To1(N)) = 
  p1(N, 1) o Pa(id(N),To1(N))’ >-- arw[GSYM o_assoc] >>
 fs[Pa_distr,p12_of_Pa] >> fs[o_assoc,To1_def])
(form_goal 
“?Add:N * N->N.Add o Pa(id(N),O o To1(N)) = id(N) & 
 Add o Pa(p1(N,N),SUC o p2(N,N)) = SUC o p2(N * N,N) o Pa(id(N * N),Add)”));



(*add_def0*)
val ADD_def0 = ADD_ex |> ex2fsym0 "ADD" [] |> store_as "ADD_def0";


val ADD = mk_fun "ADD" [] 


val Add_ex = prove_store("Add_ex",
e0
(rpt strip_tac >> qexists_tac ‘ADD o Pa(a,b)’ >> rw[])
(form_goal
 “!a:X->N b. ?ab. ADD o Pa(a,b) = ab”));

val Add_def = Add_ex |> spec_all |> ex2fsym0 "Add" ["a","b"]
                     |> gen_all
                     |> store_as "Add_def";



(*add_def*)
val ADD_def = prove_store("ADD_def",
e0
(assume_tac ADD_def0 >> fs[p12_of_Pa])
(form_goal
“ADD o Pa(id(N),O o To1(N)) = id(N) & 
 ADD o Pa(p1(N,N),SUC o p2(N,N)) = SUC o ADD”));

(*add_elements*)
val ADD_el = prove_store("ADD_el",
e0
(rpt strip_tac >> assume_tac ADD_def (* 2 *)
 >-- (by_tac “ADD o Pa(id(N), O o To1(N)) o n:1->N = id(N) o n”
      >-- arw[GSYM o_assoc] >>
      fs[Pa_distr] >>
      pick_x_assum “ADD o Pa(id(N) o n:1->N, (O o To1(N)) o n) = 
      id(N) o n” mp_tac >>
      rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idL,idR]) >>
 by_tac “ADD o Pa(p1(N,N), SUC o p2(N,N)) o Pa(n, n0:1->N) = SUC o ADD o Pa(n, n0)” >-- arw[GSYM o_assoc] >>
 fs[o_assoc,p12_of_Pa,Pa_distr])
(form_goal 
“!n:1->N. ADD o Pa(n,O) = n &
 !n0:1->N. ADD o Pa(n, SUC o n0) = SUC o ADD o Pa(n,n0)”));


val Add_El = ADD_el |> rewr_rule [Add_def] |> store_as "Add_El";



(*sub_elements*)
val SUB_el = prove_store("SUB_el",
e0
(strip_assume_tac SUB_def' >> rpt strip_tac >--
 (by_tac 
 “SUB o Pa(id(N), O o To1(N)) o n:1->N = id(N) o n”
 >-- arw[GSYM o_assoc] >> fs[Pa_distr,idL,o_assoc] >>
(* assume_tac nN_def >> drule distr_to_pa >> fs[idL] >> *)
 pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR]) >>
 by_tac 
 “PRE o SUB o Pa(n:1->N, n0) = 
  SUB o Pa(p1(N,N), SUC o p2(N,N)) o Pa(n, n0)”
 >-- arw[GSYM o_assoc] >> fs[o_assoc,Pa_distr,p12_of_Pa])
(form_goal
“!n:1->N. SUB o Pa(n,O) = n & 
 !n0.SUB o Pa(n,SUC o n0) = PRE o SUB o Pa(n,n0)”));


(*

val All_ex = prove_store("All_ex",
e0
(strip_tac >> qexists_tac ‘Char(Tp1(True(X)))’ >>
 qby_tac ‘Mono(Tp1(True(X)))’ >-- rw[from_one_Mono] >> 
 drule Char_def >> pop_assum (assume_tac o GSYM) >>
 fs[TRUE_def] >> once_rw[one_to_one_id] >> rw[idR] >> rpt strip_tac >>
 qby_tac
 ‘(?x0:1->1. Tp1(True(X)) = Tp(pxy) o y) <=> 
  Tp1(True(X)) = Tp(pxy) o y’ 
 >-- (dimp_tac >> strip_tac >> qexists_tac ‘id(1)’ >> arw[]) >>
 arw[] >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (qby_tac ‘Ev(X,1+1) o Pa(p1(X,1),Tp1(True(X)) o p2(X,1)) =
          Ev(X,1+1) o Pa(p1(X,1),Tp(pxy) o y o p2(X,1))’
 >-- arw[GSYM o_assoc] >>
 fs[GSYM Tp1_def,Ev_of_Tp,GSYM True_def] >>
 fs[Pa_o_split,GSYM o_assoc,Ev_of_Tp] >> fs[o_assoc] >> 
 qby_tac
 ‘(TRUE o To1(X) o p1(X, 1)) o Pa(x,id(1)) =
  (pxy o Pa(p1(X, 1), y o p2(X, 1))) o Pa(x,id(1))’ 
 >-- arw[] >> fs[o_assoc,Pa_distr,p12_of_Pa,idR] >>
 pop_assum  mp_tac >> once_rw[one_to_one_id] >> rw[idR] >> 
 strip_tac >> arw[]) >>
 flip_tac >> rw[GSYM Tp1_def] >> irule is_Tp >>
 rw[o_assoc,Pa_o_split] >> rw[GSYM o_assoc,Ev_of_Tp] >>
 irule FUN_EXT >> strip_tac >> rw[o_assoc,Pa_distr] >>
 once_rw[one_to_one_id] >> rw[idR] >> arw[] >>
 rw[GSYM True_def] >> rw[o_assoc] >> once_rw[one_to_one_id] >>
 rw[idR])
(form_goal
“!X.?Uq:Exp(X,1+1) -> 1+1. 
 !Y pxy:X * Y-> 1+1 y:1->Y.
 (Uq o Tp(pxy) o y = TRUE  <=> 
  !x:1->X. pxy o Pa(x,y) = TRUE)”));


val All_def = All_ex |> spec_all |> ex2fsym0 "All" ["X"]
                     |> gen_all
                     |> store_as "All_def";



val pxy_true = prove_store("pxy_true",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (arw[o_assoc,GSYM True_def] >> once_rw[one_to_one_id] >> 
 rw[idR]) >>
 irule FUN_EXT >> strip_tac >> once_rw[to_P_component] >>
 arw[GSYM True_def] >> rw[o_assoc] >> 
 once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!X Y pred:X * Y -> 1+1.pred = True(X * Y) <=> 
    !x:1->X y:1->Y. pred o Pa(x,y) = TRUE”));
*)



val ind_gen_principle = prove_store("ind_gen_principle",
e0
(rpt strip_tac >> 
 qspecl_then [‘X’,‘N’,‘pred’] assume_tac All_def >> 
 dimp_tac >--
 (rpt strip_tac >> arw[GSYM True_def,o_assoc] >> once_rw[one_to_one_id] >>
  rw[idR]) >>
 strip_tac >> 
 qsuff_tac ‘!y:1 -> N x:1 -> X. pred o Pa(x, y) = TRUE’ >--
 (rw[pxy_true] >> rpt strip_tac >> arw[]) >>
 strip_tac >> first_x_assum (qspecl_then [‘y’] (assume_tac o GSYM))  >>
 arw[] >> 
 qsuff_tac ‘ All(X) o Tp(pred) = True(N)’
 >-- (strip_tac >> arw[GSYM o_assoc] >> rw[GSYM True_def] >>
     rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) >>
 rw[ind_principle] >>
 rw[All_def,o_assoc] >> arw[] >> rpt strip_tac >> 
 first_x_assum (qspecl_then [‘x’] assume_tac)  >>
 first_x_assum (qspecl_then [‘x’] strip_assume_tac)  >>
 first_x_assum irule >> arw[])
(form_goal 
“!X pred:X * N-> 1+1. pred = True(X * N) <=>
 (!x:1->X. pred o Pa(x,O) = TRUE & 
  (!n:1->N. pred o Pa(x,n) = TRUE ==> pred o Pa(x, SUC o n) = TRUE))”));



val ind_gen_principle' = prove_store("ind_gen_principle'",
e0
(rpt strip_tac >> rw[ind_gen_principle] >>
 dimp_tac >> rpt strip_tac (* 4 *)
 >-- arw[] 
 >-- (first_x_assum (qspecl_then [‘x’] assume_tac) >>
     fs[] >> first_x_assum rev_drule >> 
     first_x_assum accept_tac)
 >-- arw[] >>
 first_x_assum drule >> arw[])
(form_goal 
“!X pred:X * N->1+1. pred = True(X * N) <=>
 (!x:1->X. pred o  Pa(x,O) = TRUE) & 
 (!x n:1->N. pred o Pa(x,n) = TRUE ==> pred o Pa(x, SUC o n) = TRUE)”));



(*sub_mono_eq*) 
val SUB_MONO_EQ = prove_store("SUB_MONO_EQ",
e0
(rpt strip_tac >>
 qsuff_tac ‘Char(Diag(N)) o Pa(SUB o Pa(SUC o p1(N,N), SUC o p2(N,N)),SUB) = 
 True(N * N)’
 >-- (strip_tac >> 
      qby_tac 
      ‘(Char(Diag(N)) o Pa(SUB o Pa(SUC o p1(N, N), SUC o p2(N, N)), SUB)) o 
       Pa(m,n) = True(N * N) o Pa(m,n)’ >-- arw[] >>
      fs[o_assoc,Pa_distr] >> 
      pop_assum mp_tac >> rw[GSYM True_def] >> rw[o_assoc] >>
      once_rw[one_to_one_id] >> rw[idR] >> rw[Char_Diag',p12_of_Pa]) >>
rw[ind_gen_principle,o_assoc,Pa_distr,Char_Diag',p12_of_Pa] >>
assume_tac SUB_el >> assume_tac PRE_def >> rpt strip_tac (* 2 *)
>-- (arw[] >> rw[GSYM o_assoc,PRE_def,idL]) >>
arw[])
(form_goal 
“!m:1->N n:1->N. 
 SUB o Pa(SUC o m, SUC o n) = SUB o Pa(m,n)”));

(*add_sub0*)
val ADD_SUB0 = prove_store("ADD_SUB0",
e0
(rw[INDUCT_one_component] >> 
 rw[o_assoc,Pa_distr,p12_of_Pa] >>
 rw[ADD_el,SUB_MONO_EQ] >> rw[SUB_el])
(form_goal 
“!a:1->N. (!c:1->N. (SUB o Pa(ADD,p2(N,N))) o Pa(a,c) = p1(N,N) o Pa(a,c))”));


(*add_sub*)
val ADD_SUB = prove_store("ADD_SUB",
e0
(assume_tac ADD_SUB0 >> fs[o_assoc,Pa_distr,p12_of_Pa])
(form_goal 
“!a:1->N c:1->N. SUB o Pa(ADD o Pa(a,c),c) = a”));



val ind_N_element = prove_store("ind_N_element",
e0
(rpt strip_tac >> assume_tac INDUCT_one_component >>
 first_x_assum (qspecl_then [‘f o p2(N,N)’,‘g o p2(N,N)’,‘O’] assume_tac) >>
 fs[o_assoc,p12_of_Pa])
(form_goal
“!f:N->N g:N->N. (!n:1->N.f o n = g o n) <=>
  f o O = g o O & 
  !n:1->N. f o n = g o n ==> f o SUC o n = g o SUC o n”));


(*add_z_n0*)
val ADD_O_n0 = prove_store("ADD_O_n0",
e0
(rw[ind_N_element,o_assoc,Pa_distr,idL] >> 
 once_rw[one_to_one_id] >> rw[idR] >>
 rw[ADD_el] >> rpt strip_tac >> arw[])
(form_goal
“!n:1->N. (ADD o Pa(O o To1(N),id(N))) o n = id(N) o n”));

(*add_z_n*)
val ADD_O_n = prove_store("ADD_O_n",
e0
(assume_tac ADD_O_n0 >> fs[Pa_distr,idL,o_assoc] >>
 pop_assum mp_tac >> once_rw[one_to_one_id] >>
 rw[idR])
(form_goal
“!n:1->N. ADD o Pa(O,n) = n”));

val Add_O_n = ADD_O_n |> rewr_rule[Add_def] |> store_as "Add_O_n";

(*add_clauses1*)
val ADD_CLAUSES1 =  ADD_O_n;

(*sub_equal_0*)
val SUB_equal_0 = prove_store("SUB_equal_0",
e0
(strip_tac >> assume_tac ADD_SUB >>
  first_x_assum (qspecl_then [‘O’,‘n’] assume_tac) >>
  fs[ADD_O_n])
(form_goal 
“!n. SUB o Pa(n,n) = O”));

(*n_sub_n_z*)
val n_SUB_n_O = SUB_equal_0



(*le_refl*)
val LE_refl = prove_store("LE_refl",
e0
(rpt strip_tac >> assume_tac LE_Mono >>
 drule Char_def >> fs[TRUE_def] >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 strip_assume_tac LE_def >> 
 drule Pb_fac_iff_1 >> arw[] >> rw[n_SUB_n_O])
(form_goal 
“!x:1->N. Char(LE) o Pa(x, x) = TRUE”));

(*le_z_z*)
val LE_O_O = prove_store("LE_O_O",
e0
(rpt strip_tac >> assume_tac LE_Mono >>
 drule Char_def >> fs[TRUE_def] >>
 pop_assum (assume_tac o GSYM) >> fs[] >>
 strip_assume_tac LE_def >> drule Pb_fac_iff_1 >>
 qsuff_tac ‘SUB o Pa(n0,O) = O’ >-- rw[SUB_0_cj2] >>
 first_x_assum $ irule o iffLR >> 
 qexists_tac ‘x0’ >> arw[])
(form_goal 
“!n0:1->N. Char(LE) o Pa(n0, O) = TRUE ==> n0 = O”));


(*le_cases*)
val LE_cases = prove_store("LE_cases",
e0
(rpt strip_tac >> cases_on “n0 = n:1->N” (* 2 *)
 >-- arw[] >>
 assume_tac CLT_iff_LE_NE >> 
 arw[] >> assume_tac LE_Mono >> drule Char_def >>
 fs[TRUE_def] >> 
 pop_assum (assume_tac o GSYM) >> fs[] >>
 qexists_tac ‘x0’ >> arw[])
(form_goal
 “!n0:1->N n:1->N. Char(LE) o Pa(n0, n) = TRUE ==> 
  Char(LT) o  Pa(n0, n) = TRUE | n0 = n”));

(*sub_s*)
val SUB_SUC = prove_store("SUB_SUC",
e0
(rpt strip_tac >> assume_tac SUB_def' >>
 by_tac
 “PRE o SUB o Pa(a:1->N, b:1->N) = 
  SUB o Pa(p1(N,N), SUC o p2(N,N)) o Pa(a, b)”
 >-- arw[GSYM o_assoc] >>
 fs[o_assoc,Pa_distr,p12_of_Pa])
(form_goal
“!a:1->N b:1->N. SUB o Pa(a,SUC o b) = 
 PRE o SUB o Pa(a,b)”));

(*double_ind*)
val double_IND = prove_store("double_IND",
e0
(rpt strip_tac >>  rw[GSYM All_def,GSYM o_assoc] >>
 assume_tac ind_principle_elements >> arw[] >> 
 qsuff_tac
 ‘(!n : 1 -> N.
   (All(N) o Tp(pred)) o n = TRUE ==>
   (All(N) o Tp(pred)) o SUC o n = TRUE) <=>
  (!n : 1 -> N.
    (All(N) o Tp(pred)) o n = TRUE ==>
    pred o Pa(O, SUC o n) = TRUE &
    !m : 1 -> N.
     pred o Pa(m, SUC o n) = TRUE ==>
     pred o Pa(SUC o m, SUC o n) = TRUE)’
 >-- (strip_tac >> arw[]) >> 
 qsuff_tac
 ‘!n:1->N. 
  (All(N) o Tp(pred)) o n = TRUE ==>
    ((All(N) o Tp(pred)) o SUC o n = TRUE <=>
      pred o Pa(O, SUC o n) = TRUE &
      !m : 1 -> N.
      pred o Pa(m, SUC o n) = TRUE ==>
      pred o Pa(SUC o m, SUC o n) = TRUE)’ 
 >-- (strip_tac >> dimp_tac >> strip_tac >> strip_tac >> 
      strip_tac >-- (last_x_assum drule >> 
                    first_x_assum drule >> fs[]) >>
      first_x_assum drule >> first_x_assum drule >> fs[]) >>
 rpt strip_tac >> 
 first_x_assum (qspecl_then [‘pred o Pa(id(N),SUC o n o To1(N))’] assume_tac) >>
 fs[o_assoc,Pa_distr] >> pop_assum mp_tac >>
 once_rw[one_to_one_id] >> rw[idL,idR] >>
 rw[All_def])
(form_goal
“!pred:N * N-> 1+1.(!n m:1->N. pred o Pa(m,n) = TRUE) <=>
 (!m.pred o Pa(m,O) = TRUE) &
 (!n.(!m.pred o Pa(m,n) = TRUE) 
   ==>
   pred o Pa(O,SUC o n) = TRUE & 
   (!m.pred o Pa(m,SUC o n) = TRUE ==> pred o Pa(SUC o m, SUC o n) = TRUE))”));


val All_Pr = prove_store("All_Pr",
e0
(rpt strip_tac >> rw[All_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- arw[] >>
 qby_tac ‘x = Pa(p1(X,Y) o x, p2(X,Y) o x)’ >-- 
 rw[GSYM to_P_component] >> once_arw[] >>
 pop_assum (K all_tac) >> arw[])
(form_goal
 “!X Y Z pxyz: (X * Y) * Z -> 1+1 z0:1->Z. All(X * Y) o Tp(pxyz) o z0 = TRUE <=> !x:1->X y:1->Y.pxyz o Pa(Pa(x,y),z0) = TRUE”));


val All_Pr' = prove_store("All_Pr'",
e0
(rpt strip_tac >> rw[All_Pr] >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X Y Z pxyz: (X * Y) * Z -> 1+1 z0:1->Z. All(X * Y) o Tp(pxyz) o z0 = TRUE <=> !y:1->Y x:1->X.pxyz o Pa(Pa(x,y),z0) = TRUE”));

val triple_IND = prove_store("triple_IND",
e0
(rpt strip_tac >>
 qby_tac 
 ‘(!a:1->N m:1-> N n:1->N.
   pred o Pa(Pa(n, m), a) = TRUE) <=> 
  (!a:1->N. All(N * N) o Tp(pred) o a = TRUE)’ >--
 (rw[All_def] >> dimp_tac >> rpt strip_tac (* 2 *) >--
  (first_x_assum (qspecl_then [‘a’,‘p2(N,N) o x’,‘p1(N,N) o x’] assume_tac) >>
   fs[GSYM to_P_component]) >> arw[]) >>
 arw[GSYM o_assoc,ind_principle_elements] >> 
 rw[o_assoc,All_Pr'] >> 
qsuff_tac
‘!a:1->N.(!m:1->N n:1->N.pred o Pa(Pa(n,m),a) = TRUE) ==>
 ((All(N * N) o Tp(pred)) o SUC o a = TRUE <=>
  (!n:1->N.pred o Pa(Pa(n,O),SUC o a) = TRUE) & 
  !m:1->N. 
  (!n:1->N. pred o Pa(Pa(n,m),SUC o a) = TRUE) ==>
   pred o Pa(Pa(O,SUC o m),SUC o a) = TRUE &
   !n:1->N. pred o Pa(Pa(n,SUC o m),SUC o a) = TRUE ==>
            pred o Pa(Pa(SUC o n,SUC o m),SUC o a) = TRUE)’
>-- (rw[GSYM All_Pr'] >> strip_tac >>
    dimp_tac >> strip_tac (* 2 *) >--
    (arw[] >> strip_tac >> strip_tac >> 
     first_x_assum drule >>
     pop_assum mp_tac >> first_x_assum drule >> 
     fs[GSYM o_assoc]) >>
    arw[] >> strip_tac >> strip_tac >>
    first_x_assum drule >> first_x_assum drule >>
    fs[o_assoc]) >>
rpt strip_tac >> arw[o_assoc] >> 
assume_tac double_IND >>
first_x_assum (qspecl_then [‘pred o Pa(id(N * N),(SUC o a) o To1(N * N))’] assume_tac) >>
rw[All_Pr'] >> pop_assum mp_tac >>
rw[o_assoc] >> once_rw[Pa_distr] >>
rw[o_assoc] >> once_rw[one_to_one_id] >> 
once_rw[idL] >> once_rw[idR] >> rw[])
(form_goal
 “!pred:(N * N) * N-> 1+1. 
  (!a:1->N m n. pred o Pa(Pa(n,m),a) = TRUE) <=>
   (!m:1->N n. pred o Pa(Pa(n,m),O) = TRUE) &
   (!a:1->N. 
     (!m:1->N n. pred o Pa(Pa(n,m),a) = TRUE)==>
     (!n.pred o Pa(Pa(n,O),SUC o a) = TRUE) & 
     (!m.(!n.pred o Pa(Pa(n,m),SUC o a) = TRUE) ==>
         pred o Pa(Pa(O,SUC o m),SUC o a) = TRUE &
         (!n. pred o Pa(Pa(n,SUC o m),SUC o a) = TRUE              ==> 
              pred o Pa(Pa(SUC o n,SUC o m),SUC o a) = TRUE)))”));




val triple_IND' = prove_store("triple_IND'",
e0
(rpt strip_tac >>
 qby_tac
 ‘?P:(N * N) * N -> 1+1. 
  !a m n. pred o Pa(n,Pa(m,a)) = TRUE <=> 
  P o Pa(Pa(n,m),a) = TRUE’
 >--
 (qexists_tac ‘pred o Pa(p1(N,N) o p1(N * N,N),
                         Pa(p2(N,N) o p1(N * N,N),
                         p2(N * N,N)))’
  >> rw[Pa_distr,o_assoc,p12_of_Pa]) >> 
 pop_assum strip_assume_tac >>
 arw[] >> rw[triple_IND])
(form_goal
 “!pred:N * N * N-> 1+1. 
  (!a:1->N m n. pred o Pa(n,Pa(m,a)) = TRUE) <=>
   (!m:1->N n. pred o Pa(n,Pa(m,O)) = TRUE) &
   (!a:1->N. 
     (!m:1->N n. pred o Pa(n,Pa(m,a)) = TRUE)==>
     (!n.pred o Pa(n,Pa(O,SUC o a)) = TRUE) & 
     (!m.(!n.pred o Pa(n,Pa(m,SUC o a)) = TRUE) ==>
         pred o Pa(O,Pa(SUC o m,SUC o a)) = TRUE &
         (!n. pred o Pa(n,Pa(SUC o m,SUC o a)) = TRUE              ==> 
              pred o Pa(SUC o n,Pa(SUC o m,SUC o a)) = TRUE)))”));


(*le_sub*)
val LE_SUB = prove_store("LE_SUB",
e0
(rpt strip_tac >> strip_assume_tac LE_def >>
 assume_tac LE_Mono >>
 drule Char_def >> fs[TRUE_def] >>
 pop_assum (assume_tac o GSYM) >>
 once_arw[] >> 
 drule Pb_fac_iff_1 >> arw[] >> fs[Char_def])
(form_goal
“(!m:1->N n. Char(LE) o Pa(m,n) = TRUE <=> SUB o Pa(m,n) = O)”));




(*TODO automatic rw A ==> B ==>C <=> A & B ==>C*)
(*if in the position of LE, write LEQ, then o_assoc has new variable ob 209, strange error*)
val CANCEL_SUB_pred = prove_store("CANCEL_SUB_pred",
e0
(rpt strip_tac >> 
 qexists_tac ‘IMP o 
  Pa(CONJ o 
    Pa(Char(LE) o Pa(p2(N * N,N),p1(N,N) o p1(N * N,N)),
       Char(LE) o Pa(p2(N * N,N),p2(N,N) o p1(N * N,N))),
     IFF o 
    Pa(Eq(N) o 
       Pa(SUB o Pa(p1(N,N) o p1(N * N,N),p2(N * N,N)), 
          SUB o Pa(p2(N,N) o p1(N * N,N),p2(N * N,N))),
       Eq(N) o 
       Pa(p1(N,N) o p1(N * N,N),p2(N,N) o p1(N * N,N))))’ >>
 rpt strip_tac >>
 rw[o_assoc,Pa_distr,IMP_def] >>
 rw[p12_of_Pa] >>
 rw[CONJ_def] >> rw[IFF_def] >> 
 rw[GSYM True1TRUE] >> rw[GSYM Eq_property] >>
 dimp_tac >> rpt strip_tac >> fs[])
(form_goal
“?pred:(N * N) * N-> 1+1. 
!a:1->N m n.(Char(LE) o Pa(a,n) = TRUE ==>
     Char(LE) o Pa(a,m) = TRUE ==>
 (SUB o Pa(n,a) = SUB o Pa(m,a) <=> n = m)) <=>
 pred o Pa(Pa(n,m),a) = TRUE”));


(*cancel_sub00*)
val CANCEL_SUB00 = prove_store("CANCEL_SUB00",
e0
(strip_assume_tac CANCEL_SUB_pred >> arw[] >>
rw[triple_IND] >> pop_assum (assume_tac o GSYM) >> arw[] >>
strip_tac (* 2 *) >-- rw[SUB_0_cj2] >>
strip_tac >> strip_tac >> strip_tac (* 2 *) >--
rw[LE_SUB,SUB_0_cj2,Thm2_1] >>
strip_tac >> strip_tac >> strip_tac (* 2 *) >--
rw[LE_SUB,SUB_0_cj2,Thm2_1] >>
rpt strip_tac >> rw[SUB_MONO_EQ,INV_SUC_EQ] >>
first_x_assum irule >> fs[SUB_MONO_EQ,LE_SUB]
)
(form_goal 
“!a m n. Char(LE) o Pa(a,n) = TRUE ==>
 Char(LE) o Pa(a,m) = TRUE ==>
 (SUB o Pa(n,a) = SUB o Pa(m,a)  <=> n = m)”));

(*cancel_sub00'*)
val CANCEL_SUB00' = prove_store("CANCEL_SUB00'",
e0
(rpt strip_tac >> rev_drule CANCEL_SUB00 >>
 first_x_assum drule >> arw[]
 )
(form_goal 
“!a n. Char(LE) o Pa(a,n) = TRUE ==>
 !m. Char(LE) o Pa(a,m) = TRUE ==>
 (SUB o Pa(n,a) = SUB o Pa(m,a)  <=> n = m)”));

(*sub_0*)
val SUB_0 = prove_store("SUB_0",
e0
(suffices_tac
 “!n:1->N. (SUB o Pa(O o To1(N), id(N))) o n = O o To1(N) o n” >--
 (rpt strip_tac >> 
 pop_assum mp_tac >> rw[o_assoc,Pa_distr] >>
 once_rw[one_to_one_id] >> rw[idL,idR] >> rpt strip_tac >>
 arw[]) >>
 rw[GSYM o_assoc] >> rw[ind_N_element] >>
 assume_tac SUB_el >> rw[o_assoc,Pa_distr] >>
 once_rw[one_to_one_id] >> rw[idL,idR] >> arw[] >>
 rpt strip_tac >> arw[PRE_def])
(form_goal 
“!n:1->N. SUB o Pa(O,n) = O”));

(*zero_less_eq*)
val ZERO_LESS_EQ = prove_store("ZERO_LESS_EQ",
e0
(rw[LE_SUB,SUB_0])
(form_goal
 “!x. Char(LE) o Pa(O, x) = TRUE”));

(*less_eq_mono*)
val LESS_EQ_MONO = prove_store("LESS_EQ_MONO",
e0
(rw[SUB_MONO_EQ,LE_SUB])
(form_goal
 “(!m n.Char(LE) o Pa(SUC o m, SUC o n) = TRUE <=>
        Char(LE) o Pa(m, n) = TRUE)”));


(*lt_char_LT*)
val LT_Char_LTo = prove_store("LT_Char_LTo",
e0
(rpt strip_tac >> assume_tac $ GSYM LT_def >>
 assume_tac LT0_Mono >> rfs[] >> drule Char_def >> fs[TRUE_def] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 fconv_tac (rand_fconv no_conv (once_depth_fconv no_conv (rewr_fconv (eq_sym "ar")))) >> rw[])
(form_goal
“!x:1->N * N. (?(x0 : 1 -> LTo). x = LT o x0) <=>
  Char(LT) o x = TRUE”));

(*le_char_LE*)
val LE_Char_LEo = prove_store("LE_Char_LEo",
e0
(rpt strip_tac >> strip_assume_tac LE_def >>
 assume_tac LE_Mono >> drule Char_def >> fs[TRUE_def] >> 
 pop_assum (assume_tac o GSYM) >> fs[] >> 
 fconv_tac (rand_fconv no_conv (once_depth_fconv no_conv (rewr_fconv (eq_sym "ar")))) >> rw[])
(form_goal
“!x:1->N * N. (?(x0 : 1 -> LEo). x = LE o x0) <=>
   Char(LE) o x = TRUE”));

(*less_0*)
val LESS_0 = prove_store("LESS_0",
e0
(rpt strip_tac >> 
 rw[GSYM LT_Char_LTo] >> 
 rw[LT_iff_LE_NE] >> 
 rw[GSYM Thm2_1] >> 
 rw[LE_Char_LEo] >> rw[ZERO_LESS_EQ]
 )
(form_goal
 “!n. Char(LT) o Pa(O, SUC o n) = TRUE”));

(*less_mono_eq*)
val LESS_MONO_EQ = prove_store("LESS_MONO_EQ",
e0
(assume_tac LT0_Mono >>
 (*assume_tac LESS_def >> *)drule Char_def >> fs[TRUE_def] >>
 fs[GSYM LT_def] >> pop_assum (assume_tac o GSYM) >> 
 fs[GSYM LT_Char_LTo] >> rw[LT_def] >>
 fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "ar"))) >>
 rw[LT_iff_LE_NE] >> 
 rw[INV_SUC_EQ] >> assume_tac LE_Char_LEo >> 
 arw[LESS_EQ_MONO])
(form_goal
 “(!m n.Char(LT) o Pa(SUC o m, SUC o n) = TRUE <=>
        Char(LT) o Pa(m, n) = TRUE)”));



(*less_cases_pred*)
val LT_cases_pred = prove_store("LT_cases_pred",
e0
(rpt strip_tac >>
 qexists_tac 
 ‘DISJ o 
  Pa(Char(LT),Char(LE) o Pa(p2(N,N),p1(N,N)))’ >>
 rw[o_assoc,Pa_distr,DISJ_def,p12_of_Pa])
(form_goal
“ ?pred:N * N-> 1+1.
  (!m n. (Char(LT) o Pa(m,n) = TRUE | 
         Char(LE) o Pa(n,m) = TRUE) <=> 
         pred o Pa(m,n) = TRUE)”));

(*less_cases*)
val LESS_cases = prove_store("LESS_cases",e0
(strip_assume_tac LT_cases_pred >> arw[] >>
 qsuff_tac
 ‘!n:1->N m:1->N. pred o Pa(m,n) = TRUE’
 >-- (strip_tac >> arw[]) >>
 rw[double_IND] >> pop_assum (assume_tac o GSYM) >>
 arw[] >> 
 strip_tac (* 2 *) >-- rw[ZERO_LESS_EQ] >>
 strip_tac >> strip_tac >> strip_tac (* 2 *) >-- 
 rw[LESS_0] >>
 arw[LESS_MONO_EQ,LESS_EQ_MONO]
)
(form_goal
 “!m n.Char(LT) o Pa(m,n) = TRUE | Char(LE) o Pa(n,m) = TRUE”));

(*less_eq_cases*)
val LESS_EQ_cases =prove_store("LESS_EQ_cases",
e0
(rpt strip_tac >> assume_tac LESS_cases >>
 cases_on “Char(LE) o Pa(m:1->N, n) = TRUE” (* 2 *)
 >-- arw[] >>
 fs[] >> 
 first_x_assum (qspecl_then [‘n’,‘m’] assume_tac) >>
 fs[] >>
 assume_tac LT_iff_LE_NE >> 
 assume_tac LE_Mono >>
 drule Char_def >> fs[TRUE_def] >> 
 first_x_assum (qspecl_then [‘n’,‘m’] assume_tac) >>
 pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
 arw[] >> strip_tac >>
 assume_tac LT0_Mono >> drule Char_def >>
 fs[LT_def] >>
 first_x_assum (qspecl_then [‘Pa(n,m)’] assume_tac) >> rfs[TRUE_def] >>
 fs[GSYM LT_def] >> assume_tac LTNE_def >> drule $ iffLR isPb_expand >>
 pop_assum strip_assume_tac >> pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> fs[] >> 
 qexists_tac ‘LTLE o x0’ >> fs[o_assoc])
(form_goal
 “!m n.Char(LE) o Pa(m,n) = TRUE |
       Char(LE) o Pa(n,m) = TRUE”));

(*cancel_sub0*)
val CANCEL_SUB0 = prove_store("CANCEL_SUB0",
e0
(rpt strip_tac >> 
 assume_tac TRUE_def >>
 assume_tac CANCEL_SUB00 >> assume_tac LESS_EQ_cases >>
 first_x_assum irule >> fs[GSYM LE_SUB] >>
 first_assum (qspecl_then [‘n’,‘a’] assume_tac) >>
 first_x_assum (qspecl_then [‘m’,‘a’] assume_tac) >>
 fs[]
 )
(form_goal 
“!a n m. ~(SUB o Pa(n,a) = O) & ~(SUB o Pa(m,a) = O) ==>
 (SUB o Pa(n,a) = SUB o Pa(m,a)  <=> n = m)”));

(*equality_NN_ind*)
val equality_NN_IND = prove_store("equality_NN_IND",
e0
(rpt strip_tac >> rw[equality_ind])
(form_goal
“!f:N* N->N g:N * N->N.
 !m:1->N.(!n.f o Pa(m,n) = g o Pa(m,n)) <=>
 f o Pa(m,O) = g o Pa(m,O) & 
 !n0:1->N. f o Pa(m,n0) = g o Pa(m,n0) ==> 
 f o Pa(m,SUC o n0) = g o Pa(m,SUC o n0)”));

(*add_suc0*)
val ADD_SUC0 = prove_store("ADD_SUC0",
e0
(rw[equality_NN_IND] >>
 fs[p12_of_Pa,Pa_distr,o_assoc,idL,ADD_el] >>
 rpt strip_tac >> arw[])
(form_goal
“!n m:1->N.(ADD o Pa(SUC o p1(N,N),id(N) o p2(N,N))) o Pa(n,m) = (SUC o ADD) o Pa(n,m)”));


(*add_suc*)
val ADD_SUC = prove_store("ADD_SUC",
e0
(assume_tac ADD_SUC0 >> fs[idL,o_assoc,Pa_distr,p12_of_Pa])
(form_goal 
“!n:1->N m:1->N. ADD o Pa(SUC o n,m) = SUC o ADD o Pa(n,m)”));

(*add_sym0*)
val ADD_SYM0 = prove_store("ADD_SYM0",
e0
(rw[equality_NN_IND] >> rw[ADD_el,Pa_distr,o_assoc,p12_of_Pa,ADD_O_n,ADD_SUC] >> rpt strip_tac >> arw[])
(form_goal “!m:1->N. (!n. ADD o Pa(m,n) = 
   (ADD o Pa(p2(N,N),p1(N,N))) o Pa(m,n))”));

(*add_sym*)
val ADD_SYM = prove_store("ADD_SYM",
e0
(assume_tac ADD_SYM0 >> fs[Pa_distr,p12_of_Pa,o_assoc])
(form_goal 
“!m:1->N n:1->N. ADD o Pa(m,n) = ADD o Pa(n,m)”));

val Add_sym = ADD_SYM |> rewr_rule[Add_def] |> store_as "Add_sym";

(*suc_sub*)
val SUC_SUB = prove_store("SUC_SUB",
e0
(assume_tac ADD_SUB >> strip_tac >>
 first_x_assum (qspecl_then [‘SUC o O’,‘n’] assume_tac) >>
 qsuff_tac
 ‘ADD o Pa(SUC o O,n) = SUC o n’
 >-- (strip_tac >> fs[]) >>
 once_rw[ADD_SYM] >> rw[ADD_el])
(form_goal
 “!n:1->N. SUB o Pa(SUC o n,n) = SUC o O”));

(*sub_diff_1*)
val SUB_DIFF_1 = prove_store("SUB_DIFF_1",
e0
(rpt strip_tac >> dimp_tac >--
 (strip_tac >> irule $ iffLR CANCEL_SUB0 >> qexists_tac ‘b’ >>
 assume_tac SUC_SUB >> once_arw[] >> arw[Thm2_1]) >>
 rpt strip_tac >> arw[SUC_SUB])
(form_goal 
“!a:1->N b. SUB o Pa(a,b) = SUC o O <=> a = SUC o b”));


(*sub_s_z_cases*)
val SUB_SUC_O_cases = prove_store("SUB_SUC_O_cases",
e0
(rpt strip_tac >> assume_tac SUB_SUC >> fs[] >>
 by_tac “SUB o Pa(a, b) = O | 
         SUB o Pa(a, b) = SUC o O”
 >-- (drule $ iffLR PRED_O_cases >> arw[])>>
 pop_assum strip_assume_tac >-- arw[] >>
 disj1_tac >>
 fs[SUB_DIFF_1] 
 )
(form_goal 
“!a:1->N b:1->N. SUB o Pa(a,SUC o b) = O ==>
 a = SUC o b | SUB o Pa(a,b) = O”));


(*le_cases_iff*)
val LE_cases_iff = prove_store("LE_cases_iff",
e0
(rpt strip_tac >> cases_on “n0 = n:1->N” (* 2 *)
 >-- (arw[] >> rw[LE_refl]) >>
 assume_tac CLT_iff_LE_NE >> arw[])
(form_goal “!n0:1->N n:1->N. Char(LE) o Pa(n0, n) = TRUE <=> 
   Char(LE) o  Pa(n0, n) = TRUE | n0 = n”));


(*sub_eq_0*)
val SUB_EQ_0 = prove_store("SUB_EQ_0",
e0
(rpt strip_tac >> assume_tac LE_def >>
 pop_assum strip_assume_tac >>
 drule $ iffLR isPb_expand >> pop_assum strip_assume_tac >>
 assume_tac LE_Mono >> drule Char_def >> fs[TRUE_def] >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 drule Pb_fac_iff_1 >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >> arw[])
(form_goal
“(!m:1->N n:1->N. SUB o Pa(m,n) = O <=> Char(LE) o Pa(m,n) = TRUE)”));

(*lt_succ_le*)
val LESS_SUC_LEQ = prove_store("LESS_SUC_LEQ",
e0
(rpt strip_tac >> 
 assume_tac CLT_iff_LE_NE >> arw[] >>
 pop_assum (K all_tac) >> assume_tac LE_Mono >>
 drule Char_def >> fs[TRUE_def] >>
 (*assume_tac LE_cases_iff >> *)
 first_x_assum 
  (qspecl_then [‘Pa(n0,SUC o n)’] assume_tac) >>
 by_tac 
 “(?le0 : 1 -> LEo. Pa(n0:1->N, SUC o n:1->N) = LE o le0) <=> 
  (?x0 : 1 -> LEo. LE o x0 = Pa(n0, SUC o n))”
 >-- (dimp_tac >> strip_tac
      >-- (qexists_tac ‘le0’ >> arw[]) >>
      qexists_tac ‘x0’ >> arw[]) >> once_arw[] >>
 pop_assum (K all_tac) >> 
 pop_assum mp_tac >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 strip_tac >> assume_tac (GSYM SUB_EQ_0) >>
 arw[] >>
 assume_tac SUB_el >> arw[] >> 
 cases_on “SUB o Pa(n0:1->N,n) = O” (* 2 *) >--
 (arw[] >> assume_tac PRE_def >> arw[] >>
  assume_tac (GSYM SUB_DIFF_1) >> once_arw[] >>
  pop_assum (K all_tac) >> ccontra_tac >> fs[Thm2_1]) >>
 arw[] >> ccontra_tac >> pop_assum strip_assume_tac >>
 pop_assum mp_tac >>
 assume_tac (GSYM SUB_DIFF_1) >> 
 once_arw[] >> once_arw[] >> rw[] >>
 pop_assum (K all_tac) >>
 assume_tac PRE_eq_0 >> fs[])
(form_goal “!n0:1->N n:1->N. Char(LT) o Pa(n0, SUC o n) = TRUE  <=> Char(LE) o Pa(n0, n) = TRUE”));




(*strong_ind_lemma*)
val strong_IND_lemma = prove_store("strong_IND_lemma",
e0
(rpt strip_tac >> qsuff_tac ‘Iso(q)’
 >-- (strip_tac >> irule Mono_Epi_Iso >> arw[] >>
      drule Iso_Epi >>
      qsuff_tac ‘?q2p. p0 o q2p = q’
      >-- (strip_tac >> pop_assum (assume_tac o GSYM) >> 
           fs[] >> drule o_Epi_imp_Epi >>
           first_x_assum accept_tac) >>
      irule prop_2_half2 >> arw[] >> rpt strip_tac >>
      rev_drule Char_def >> fs[TRUE_def] >> 
      last_x_assum (qspecl_then [‘x’] assume_tac) >>
      first_assum (assume_tac o iffLR) >>
      first_x_assum irule >> 
      by_tac “?(nb : 1 -> Q). x = q:Q->N o nb”
      >-- (qexistsl_tac [‘xb’] >> arw[]) >>
      arw[] >> assume_tac LE_refl >> arw[]) >>
irule Thm2_3' >> arw[] >> strip_tac (* 2 *) >--
(rpt strip_tac >> drule LE_O_O >> arw[] >> first_x_assum irule >> 
 suffices_tac 
 “!n0:1->N. ~(Char(LT) o Pa(n0,O) = TRUE)”
 >-- (rpt strip_tac >> rfs[]) >>
 rw[NOT_LT_O]) >>
 rpt strip_tac >> 
 assume_tac LE_cases >>
 first_x_assum drule >> 
 first_x_assum strip_assume_tac >--
 (first_x_assum irule >>
  assume_tac (GSYM LESS_SUC_LEQ) >> arw[]) >>
 qpick_x_assum
 ‘!n.(!n0.Char(LT) o Pa(n0,n) = TRUE ==> Char(p0) o n0 = TRUE) ==>
      Char(p0) o n = TRUE’ irule >>
 arw[] >> rpt strip_tac >> first_x_assum irule >>
 fs[LESS_SUC_LEQ])
(form_goal 
“!P p0:P->N. Mono(p0) ==>
 !Q q:Q->N. 
  (Mono(q) & !n:1->N. (?nb:1->Q. n = q o nb) <=> 
            (!n0:1->N. Char(LE) o Pa(n0,n) = TRUE
==> Char(p0) o n0 = TRUE))
 ==>
 (!n:1->N. 
  (!n0:1->N. 
    Char(LT) o Pa(n0,n) = TRUE ==> Char(p0) o n0 = TRUE) ==> Char(p0) o n = TRUE) ==> Iso(p0)”));


val Q_Ex = prove_store("Q_Ex",
e0
(rpt strip_tac >> 
 abbrev_tac 
  “IMP o Pa(Char(LE),Char(p0:P->N) o p1(N,N)) = lep0” >>
 abbrev_tac
  “All(N) o Tp(lep0:N * N -> 1+1) = cq” >>
 qspecl_then [‘N’,‘1+1’,‘cq’,‘1’,‘TRUE’] (x_choosel_then ["Q","q","Qto1"] assume_tac) isPb_ex >>
 qexistsl_tac [‘Q’,‘q’] >>
 by_tac “Mono(q:Q->N)”
 >-- (drule Pb_Mono_Mono >> first_x_assum irule >> rw[from_one_Mono]) >>
 arw[] >> strip_tac >>
 by_tac “(?nb:1->Q. n:1->N = q o nb) <=> cq:N->1+1 o n = TRUE”
 >-- (drule Pb_fac_iff_1 >> pop_assum (assume_tac o GSYM) >> arw[] >>
      dimp_tac >> strip_tac >-- (qexists_tac ‘nb’ >> arw[]) >>
      qexists_tac ‘a’ >> arw[]) >>
 arw[] >> 
 qpick_x_assum ‘All(N) o Tp(lep0) = cq’ (assume_tac o GSYM)>>
 once_arw[] >> rw[o_assoc] >> rw[All_def] >>
 qpick_x_assum
 ‘IMP o Pa(Char(LE), Char(p0) o p1(N, N)) = lep0’
 (assume_tac o GSYM) >> once_arw[] >>
 rw[Pa_distr,o_assoc,IMP_def,p1_of_Pa]
)
(form_goal 
“!P p0:P->N. Mono(p0) ==>
 ?Q q:Q->N. 
  Mono(q) & !n:1->N. (?nb:1->Q. n = q o nb) <=> 
            (!n0:1->N. Char(LE) o Pa(n0,n) = TRUE
==> Char(p0) o n0 = TRUE)”));

val strong_IND = prove_store("strong_IND",
e0
(rpt strip_tac >> drule strong_IND_lemma >>
 drule Q_Ex >>
 pop_assum (x_choosel_then ["Q","q"] assume_tac) >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal 
“!P p0:P->N. Mono(p0) ==>
 (!n:1->N. 
  (!n0:1->N. 
    Char(LT) o Pa(n0,n) = TRUE ==> Char(p0) o n0 = TRUE) ==> Char(p0) o n = TRUE) ==> Iso(p0)”));





(*
fun exists_forall (n,s) = 
    let 
        val f0 = mk_fvar "f0" []
        val af0 = mk_forall n s (mk_neg f0)
        val ef0 = mk_exists n s f0
        val d1 = (C negI)
                     (existsE (n,s) (assume ef0)
                 (negE (assume f0) 
                   ((C allE) (assume af0) (mk_var(n,s)))))
                 af0 |>
                 disch ef0
        val d2 = elim_double_neg
                     ((C negI)
                          (negE
                               (allI (n,s)
                                     ((C negI)
                                          (negE
                                               (existsI (n,s) (mk_var(n,s)) f0 ((C add_cont) (assume f0) (HOLset.add(essps,(n,s))))
                                                        )
                                               (assume (mk_neg ef0)))
                                          f0))
                               (assume (mk_neg af0))
)
                          (mk_neg ef0))|>
                     disch (mk_neg af0)
    in dimpI d1 d2
    end


val Exq_ex = prove_store("Exq_ex",
e0
(strip_tac >> 
 qexists_tac ‘NEG o All(X) o Tp(NEG o Ev(X,1+1))’ >>
 rpt strip_tac >>
 rw[o_assoc,NEG_def] >>
 qby_tac
 ‘Tp(NEG o Ev(X,1+1)) o Tp(pxy) = Tp(NEG o pxy)’ 
 >-- (irule is_Tp >> rw[o_assoc,Pa_o_split] >> rw[GSYM o_assoc,Ev_of_Tp] >>
      rw[o_assoc,Ev_of_Tp]) >>
rw[TRUE_xor_FALSE,All_def] >> rw[o_assoc,NEG_def,Ev_of_Tp_el] >>
dimp_tac >> strip_tac (* 2 *) >--
(ccontra_tac >> 
 qsuff_tac ‘!x:1->X. pxy o Pa(x,y) = FALSE’ >-- arw[] >>
 strip_tac >>
 qpick_x_assum ‘~(!x:1->X. pxy o Pa(x,y) = FALSE)’ (K all_tac) >>
 rw[TRUE_xor_FALSE] >> ccontra_tac >>
 qsuff_tac ‘?x:1->X. pxy o Pa(x,y) = TRUE’ >-- arw[] >>
 qexists_tac ‘x’ >> arw[]) >>
ccontra_tac >>
first_x_assum (qspecl_then [‘x’] assume_tac) >> fs[TRUE_ne_FALSE]
)
(form_goal
“!X.?Exq:Exp(X,1+1) -> 1+1. 
 !Y pxy:X * Y->1+1 y:1->Y. 
 (Exq o Tp(pxy) o y = TRUE  <=> 
  ?x:1->X. pxy o Pa(x,y) = TRUE)”));

val Ex_def = Exq_ex |> spec_all |> ex2fsym0 "Ex" ["X"] |> gen_all
                    |> store_as "Ex_def"


val Eq_property_TRUE = prove_store("Eq_property_TRUE",
e0
(rpt strip_tac >> rw[GSYM True1TRUE] >> rw[GSYM Eq_property])
(form_goal
 “!X p1 p2.Eq(X) o Pa(p1,p2) = TRUE <=> p1 = p2”));

(*better have p1 p2 p3*)
val E1_ex = prove_store("E1_ex",
e0
(strip_tac >>
 abbrev_tac
 “IMP o 
    Pa(CONJ o Pa(Ev(X,1+1) o Pa(p1(X,X * Exp(X,1+1)), p2(X,Exp(X,1+1)) o p2(X,X * Exp(X,1+1))),
                 Ev(X,1+1) o Pa(p1(X,Exp(X,1+1)) o p2(X,X * Exp(X,1+1)),p2(X,Exp(X,1+1)) o p2(X,X * Exp(X,1+1)))),
      Eq(X) o 
      Pa(p1(X,X * Exp(X,1+1)), p1(X,Exp(X,1+1)) o p2(X,X * Exp(X,1+1)))) = p0” >>
 qexists_tac 
 ‘CONJ o
  Pa(Ex(X),All(X) o Tp(All(X) o Tp(p0)))’ >> rpt strip_tac >>
  rw[o_assoc,Pa_distr,CONJ_def] >> rw[All_def] >> rw[o_assoc,All_def] >>
 rw[Ex_def] >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 rw[o_assoc,Pa_distr,IMP_def] >> once_rw[CONJ_def] >>
 rw[p12_of_Pa] >> once_rw[Eq_property_TRUE] >>
 rw[Ev_of_Tp_el] >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘x’ >> arw[] >> rpt strip_tac >> first_x_assum irule >> arw[]) >>
 strip_tac >-- (qexists_tac ‘x’ >> arw[]) >>
 rpt strip_tac >> 
 qsuff_tac ‘x'' = x  & x' = x’ >-- (strip_tac >> arw[]) >> strip_tac >>
 first_x_assum irule >> arw[]
 )
(form_goal
“!X.?Exq: Exp(X,1+1) -> 1+1. 
 !Y pxy:X * Y->1+1 y:1->Y. 
 (Exq o Tp(pxy) o y = TRUE  <=> 
  ?x:1->X. pxy o Pa(x,y) = TRUE & 
  !x0:1->X. pxy o Pa(x0,y) = TRUE ==> x0 = x)”));


val E1_def =  E1_ex |> spec_all |> ex2fsym0 "E1" ["X"] |> gen_all
                    |> store_as "E1_def";
 


fun NEG_CONJ2IMP_NEG0 A B = 
    let 
        val AB = mk_conj A B
        val l = mk_neg AB
        val nB = mk_neg B
        val r = mk_imp A nB
        val l2r = negE (conjI (assume A) (assume B)) (assume l) |> negI B |> disch A |> disch l
        val r2l = negE (conjE2 (assume AB)) (mp (assume r) (conjE1 (assume AB))) 
                       |> negI AB |> disch r
    in dimpI l2r r2l
    end

val NEG_CONJ2IMP_NEG = NEG_CONJ2IMP_NEG0 (mk_fvar "A" []) (mk_fvar "B" [])



val FUN_EXT_iff = prove_store("FUN_EXT_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (drule FUN_EXT >> arw[]) >>
 rpt strip_tac >> arw[])
(form_goal
“!A B f:A->B g. (!a:1->A. f o a = g o a) <=> f = g”));


val True2TRUE = prove_store("True2TRUE",
e0
(rpt strip_tac >> rw[GSYM True_def,o_assoc] >>
 once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!X x:1->X. True(X) o x = TRUE”));


val False2FALSE = prove_store("False2FALSE",
e0
(rw[GSYM False_def,o_assoc] >> once_rw[one_to_one_id] >>
 rw[idR])
(form_goal
 “!X x:1->X. False(X) o x = FALSE”)); 
*)


val IP_el = prove_store("IP_el",
e0
(assume_tac $ GSYM ind_principle >> arw[] >>
 rpt strip_tac >>
 fconv_tac 
 (rand_fconv no_conv (rewr_fconv (GSYM $ spec_all FUN_EXT_iff))) >>
 rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR] >> fs[True2TRUE]) 
(form_goal
 “!P:N->1+1. (!n. P o n = TRUE) <=>
  P o O = TRUE &
  (!n. P o n = TRUE ==> P o SUC o n = TRUE)”));

val WOP = prove_store("WOP",
e0
(rpt strip_tac >> 
 ccontra_tac >>
 qby_tac 
 ‘!l:1->N. P o l = TRUE ==>
  ?n:1->N. P o n = TRUE & ~(Char(LE) o Pa(l,n) = TRUE)’ 
 >-- (rpt strip_tac >> ccontra_tac >>
      qsuff_tac ‘?l :1->N.
               P o l = TRUE &
               !n:1->N.
                 P o n = TRUE ==> Char(LE) o Pa(l, n) = TRUE’
      >-- arw[] >> 
      qexists_tac ‘l’ >> 
      arw[] >> rpt strip_tac >> ccontra_tac >>
      qsuff_tac ‘?n : 1->N. P o n = TRUE & ~(Char(LE) o Pa(l, n) = TRUE)’
      >-- arw[] >>
      qexists_tac ‘n’ >> arw[]) >>
 qsuff_tac 
 ‘!n:1->N. (All(N) o Tp(IMP o Pa(Char(LE),NEG o P o p1(N,N)))) o n = TRUE’ >-- 
 (rw[o_assoc,All_def,Pa_distr,IMP_def,p1_of_Pa,NEG_def] >>
 ccontra_tac >>
 qsuff_tac 
 ‘P = False(N)’ >-- fs[] >>
 irule FUN_EXT >> rw[False2FALSE] >> strip_tac >>
 first_x_assum irule >> 
 qexists_tac ‘a’ >> rw[LE_refl]) >>
 rw[IP_el,o_assoc,All_def,Pa_distr,IMP_def,p1_of_Pa,
    NEG_def,GSYM TRUE2FALSE] >> rpt strip_tac (* 2 *) >--
 (qby_tac ‘x = O’ >--
  (drule LE_O_O >> arw[]) >> arw[] >>
 ccontra_tac >> first_x_assum drule >>
 pop_assum strip_assume_tac >> fs[ZERO_LESS_EQ]
 (*~Le o Pa(ZERO, n) = TRUE is false*)) >> 
 cases_on “Char(LE) o Pa(x:1->N,n:1->N) = TRUE” >--
 (first_x_assum drule >> arw[]) >>
 qby_tac ‘x = SUC o n’ >-- 
 (drule LE_cases >> fs[LESS_SUC_LEQ]
  (*TODO: lemma x <= n ^ + /\ x ~<= n <=> x = n+*)) >>
 arw[] >> ccontra_tac >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 (*~Le o Pa(SUC o n, n') = TRUE 
  use ~(n + 1 <= n') <=> n' < n + 1 <=> n' <= n*) 
 qby_tac ‘Char(LE) o Pa(n',n) = TRUE’ >-- 
 (rw[GSYM LESS_SUC_LEQ] >> assume_tac LESS_cases >>
 first_x_assum (qspecl_then [‘n'’,‘SUC o n’] assume_tac) >>
 fs[]) >>
 first_x_assum drule >> fs[]
 )
(form_goal
 “!P:N->1+1. ~(P = False(N)) ==> 
  ?l:1->N. P o l = TRUE &
  !n:1->N. P o n = TRUE ==>
  Char(LE) o Pa(l,n) = TRUE”));



val _ = new_pred "Le" [("m",ar_sort (mk_ob "X") N),
                       ("n",ar_sort (mk_ob "X") N)]

val Le_def0 = store_ax("Le_def0",
 “!X a:X->N b:X->N. Le(a,b) <=> Char(LE) o Pa(a,b) = True(X)”);


val Le_def1 = Le_def0 |> allE (rastt "1")
                      |> rewr_rule[True1TRUE]

val _ = new_pred "Lt" [("m",ar_sort (mk_ob "X") N),
                       ("n",ar_sort (mk_ob "X") N)]

val Lt_def0 = store_ax("Lt_def0",
 “!X a:X->N b:X->N. Lt(a,b) <=> Char(LT) o Pa(a,b) = True(X)”);


val Lt_def1 = Lt_def0 |> allE (rastt "1")
                     |> rewr_rule[True1TRUE]


val Le_def = LE_SUB |> rewr_rule[GSYM Le_def1,Sub_def]

val Lt_def = prove_store("Lt_def",
e0
(rw[Lt_def1,CLT_iff_LE_NE,Le_def1,LE_Char_LEo])
(form_goal 
 “!a:1->N b. Lt(a,b) <=> Le(a,b) & ~(a = b)”));

val Sub_of_O = SUB_0 |> rewr_rule[Sub_def]
                     |> store_as "Sub_of_O";

val Sub_O = SUB_0_cj2 |> rewr_rule[Sub_def]
                      |> store_as "Sub_O";

val Add_O = ADD_el |> spec_all |> conjE1
                   |> gen_all 
                   |> rewr_rule[Add_def]
                   |> store_as "Add_O";


val Add_Suc = ADD_el |> spec_all |> conjE2
                   |> gen_all 
                   |> rewr_rule[Add_def,Suc_def]
                   |> store_as "Add_O";

val Add_O2 = ADD_O_n |> rewr_rule[Add_def]
                      |> store_as "Add_O2";

val Add_Suc1 = ADD_SUC |> rewr_rule[Add_def,Suc_def]
                       |> store_as "Add_Suc1";

val Sub_mono_eq = SUB_MONO_EQ
                      |> rewr_rule[Sub_def,Suc_def]
                      |> store_as "Sub_mono_eq";


(*
a - (b + c) = (a - b) - c

ALL A * B -> 1+1 = 2


A * B -> 2

a + b = a

B -> 2

!a. a + b = a
*)

val Sub_Add = prove_store("Sub_Add",
e0
(qby_tac
 ‘?P0. !c b a:1->N. P0 o Pa3(c,b,a) = TRUE <=> 
  Sub(a,Add(b,c)) = Sub(Sub(a,b),c)’ >-- 
 (qexists_tac 
  ‘Eq(N) o Pa(SUB o Pa(p33(N,N,N),ADD o Pa(p32(N,N,N),p31(N,N,N))),SUB o Pa(SUB o Pa(p33(N,N,N),p32(N,N,N)),p31(N,N,N)))’
(*

 ‘Eq(N) o Pa(SUB o Pa(p33(N,N,N),ADD o Pa(p32(N,N,N),p31(N,N,N))),SUB o Pa(SUB o Pa(p33(N,N,N),p32(N,N,N)),p31(N,N,N)))’ *) >>
  once_rw[GSYM Pa3_def] >> 
  once_rw[GSYM p31_def] >> once_rw[GSYM p32_def] >>
  once_rw[o_assoc] >> once_rw[Pa_distr] >>
  once_rw[Eq_property_TRUE] >> 
  once_rw[GSYM p33_def] >>
  rw[o_assoc,p12_of_Pa,Pa_distr] >>
  rw[Sub_def,Add_def]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac 
 ‘!a b c. P0 o Pa3(c,b,a) = TRUE’
 >-- (rpt strip_tac >> fs[]) >>
 rw[triple_IND',GSYM Pa3_def] >>
 fs[GSYM Pa3_def] >> rw[Suc_def] >>
 rw[Sub_of_O] >> strip_tac >> strip_tac >> 
 strip_tac (* 2 *)
 >-- rw[Sub_O,Add_O2] >>
 rpt strip_tac (* 2 *)
 >-- rw[Sub_O,Add_O] >>
 rw[Add_Suc1] >> rw[Sub_mono_eq] >> arw[])
(form_goal
 “!a:1->N b c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”));

val Le_O_iff = prove_store("Le_O_iff",
e0
(strip_tac >> dimp_tac >> strip_tac 
 >-- (fs[Le_def1] >> drule LE_O_O >> arw[]) >>
 arw[] >> rw[Le_def] >> rw[Sub_O])
(form_goal
 “!a. Le(a,O) <=> a = O”));

val Le_cases = LE_cases 
                   |> rewr_rule[GSYM Le_def1,
                                GSYM Lt_def1]
                   |> store_as "Le_cases";

val Lt_Suc_Le = LESS_SUC_LEQ 
                    |> rewr_rule[GSYM Le_def1,
                                GSYM Lt_def1,
                                Suc_def]
                   |> store_as "Lt_Suc_Le";

val Le_Suc = prove_store("Le_Suc",
e0
(rpt strip_tac >> drule Le_cases >>
 pop_assum strip_assume_tac >--
 (drule $ iffLR Lt_Suc_Le >> arw[]) >> arw[])
(form_goal 
 “!a:1->N b. Le(a,Suc(b)) ==> (Le(a,b) | a = Suc(b))”));


val Le_Add_ex = prove_store("Le_Add",
e0
(qby_tac
 ‘?P. !n m. P o Pa(n,m) = TRUE <=> 
  (Le(n,m) ==> ?p. Add(p,n) = m)’
 >-- (qexists_tac 
      ‘Imp(Char(LE), EX(Eq(N) o Pa(ADD o Pa(p31(N,N,N),p32(N,N,N)), p33(N,N,N))))’
      >>
      rpt strip_tac >> rw[GSYM Imp_def,o_assoc,IMP_def,Pa_distr] >>
      rw[GSYM Le_def1,EX_property,o_assoc,Pa_distr,Eq_property_TRUE] >> 
      rw[Pa3_def,p31_of_Pa3,p32_of_Pa3,p33_of_Pa3] >> rw[Add_def]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘!m. ALL(P) o m = TRUE’ 
 >-- arw[ALL_property] >>
 rw[IP_el] >> arw[ALL_property,Suc_def,Le_O_iff] >>
 rpt strip_tac (* 2 *)
 >-- (arw[] >> qexists_tac ‘O’ >> rw[Add_O]) >>
 drule Le_Suc >> pop_assum strip_assume_tac (* 2 *)
 >-- (first_x_assum drule >>
     pop_assum strip_assume_tac >>
     qexists_tac ‘Suc(p)’ >> arw[Add_Suc1]) >>
 arw[] >> qexists_tac ‘O’ >> rw[Add_O2])
(form_goal
 “!m:1->N n. Le(n,m) ==> ?p. Add(p,n) = m”));


val Le_trans = prove_store("Le_trans",
e0
(rpt strip_tac >> rw[Le_def] >>
 drule Le_Add_ex >> pop_assum (strip_assume_tac o GSYM)>>
 arw[] >> 
 qsspecl_then [‘p’,‘b’] assume_tac Add_sym >>
 once_arw[] >> rw[Sub_Add] >> fs[Le_def] >>
 rw[Sub_of_O])
(form_goal
 “!a:1->N b c. Le(a,b) & Le(b,c) ==> Le(a,c)”));

val Lt_mono_eq = 
LESS_MONO_EQ 
    |> rewr_rule[GSYM Lt_def1,Suc_def]
    |> store_as "Lt_mono_eq";

val LESS_MONO_ADD = prove_store("LESS_MONO_ADD",
e0
(strip_tac >> strip_tac >>
qby_tac
 ‘?P. !p.  
 P o p = TRUE <=> 
 (Lt(m,n) <=> Lt(Add(m,p),Add(n,p))) ’
 >-- (
 qexists_tac ‘Iff(Char(LT) o Pa(m,n) o To1(N),
              Char(LT) o 
              Pa(ADD o Pa(m o To1(N),id(N)),
                 ADD o Pa(n o To1(N),id(N))))’
 >-- rw[GSYM Iff_def,Pa_distr,p12_of_Pa,o_assoc,
        IFF_def] >>
     once_rw[one_to_one_id] >> rw[idR,idL] >>
     rw[GSYM Lt_def1] >> rw[Add_def])>>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘!p. P o p = TRUE’
 >-- fs[ALL_property] >>
 rw[IP_el] >> strip_tac >-- 
 (*  why arw makes no change? after rw[IP_el], if use 
 arw, no change, and if arw with Suc_def, no change, it use rw, mmakes change*) 
 arw[Add_O] >> 
 rw[Suc_def] >> rpt strip_tac >> rfs[]
 (*the thing that should be done by arw is done by 
  rfs*)
 >>fs[Add_Suc,Lt_mono_eq])
(form_goal
 “!m:1->N n p. Lt(m,n) <=> Lt(Add(m,p),Add(n,p))”));

val Suc_eq_eq = 
INV_SUC_EQ |> rewr_rule[Suc_def]
           |> store_as "Suc_eq_eq";



val EQ_MONO_ADD_EQ = prove_store("EQ_MONO_ADD_EQ",
e0
(strip_tac >> strip_tac >>
qby_tac
 ‘?P. !p.  
 P o p = TRUE <=> 
 Add(m,p) = Add(n,p) <=> m = n’
 >-- (
 qexists_tac ‘Iff(Eq(N) o 
                  Pa(Add(m o To1(N),id(N)),
                     Add(n o To1(N),id(N))),
                  Eq(N) o Pa(m,n) o To1(N))’
 >-- rw[GSYM Iff_def,Pa_distr,p12_of_Pa,o_assoc,
        IFF_def,GSYM Add_def] >>
     once_rw[one_to_one_id] >> rw[idR,idL] >>
     rw[Eq_property_TRUE,Add_def])>>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘!p. P o p = TRUE’
 >-- fs[ALL_property] >>
 rw[IP_el] >> strip_tac
 >-- arw[Add_O] >>
 rpt strip_tac >> rfs[] >>
 fs[Add_Suc,Suc_def,Suc_eq_eq])
(form_goal
 “!m:1->N n p. Add(m,p) = Add(n,p) <=> m = n”));

val LESS_MONO_ADD_EQ = GSYM LESS_MONO_ADD
                            |> store_as
                            "LESS_MONO_ADD_EQ";

val Sub_EQ_O = 
 SUB_equal_0 |> rewr_rule[Sub_def]
             |> store_as "Sub_EQ_O";

val LESS_OR_EQ = prove_store("LESS_OR_EQ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (drule Le_cases >> arw[]) 
 >-- fs[Lt_def] >>
 arw[Le_def,Sub_EQ_O] )
(form_goal
 “!m n:1->N. Le(m,n) <=> (Lt(m,n) | m = n)”));

val LESS_EQ_MONO_ADD_EQ = prove_store
("LESS_EQ_MONO_ADD_EQ",
e0
(rw[LESS_OR_EQ,LESS_MONO_ADD_EQ,EQ_MONO_ADD_EQ])
(form_goal
 “!m:1->N n p.Le(Add(m,p),Add(n,p)) <=> Le(m,n)”));


val Le_refl = LE_refl |> rewr_rule[GSYM Le_def1]
                      |> store_as "Le_refl";


val Le_Add = prove_store("Le_Add",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(a,d)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘a’,‘b’] assume_tac Add_sym >>
 arw[] >>
 qsspecl_then [‘a’,‘d’] assume_tac Add_sym >>
 arw[] >> arw[LESS_EQ_MONO_ADD_EQ])
(form_goal
 “!a:1->N b c d. Le(a,c) & Le(b,d) ==> Le(Add(a,b),Add(c,d))”));


val Suc_NONZERO = prove_store("Suc_NONZERO",
e0
(rw[O_xor_SUC] >> 
 strip_tac >> qexists_tac ‘n’ >> rw[Suc_def])
(form_goal
 “!n. ~(Suc(n) =O)”));

val WOP' = prove_store("WOP'",
e0
(assume_tac WOP >>
 rw[Le_def1] >> rpt strip_tac >> first_x_assum irule >>
 ccontra_tac >>
 fs[False2FALSE,TRUE_ne_FALSE])
(form_goal
 “!P:N -> 1+1 a.
        P o a = TRUE ==>
        ?(l : ar(1, N)).
          P o l = TRUE &
          !n. P o n = TRUE ==> Le(l,n)”));

val Suc_NEQ = prove_store("Suc_NEQ",
e0
(qby_tac
 ‘?P. !a. P o a = TRUE <=> (a = Suc(a))’
 >-- (qexists_tac ‘Eq(N) o Pa(id(N),SUC)’ >>
      rw[o_assoc,Pa_distr,Eq_property_TRUE,
       idL,Suc_def]) >>
 pop_assum (strip_assume_tac o GSYM) >>
 strip_tac >> ccontra_tac >>
 rfs[] >> drule WOP' >>
 pop_assum strip_assume_tac >>
 cases_on “l = O” >--
 (last_x_assum (assume_tac o GSYM) >> fs[GSYM Suc_NONZERO]) >>
 fs[O_xor_SUC] >>
 last_x_assum (assume_tac o GSYM) >> fs[Suc_eq_eq,Suc_def] >>
 first_x_assum drule >> 
 drule $ iffRL Lt_Suc_Le >> fs[Lt_def])
(form_goal “!a:1->N. ~(a = Suc(a))”));

val Sub_Suc = SUB_SUC |> rewr_rule[Sub_def,Suc_def,Pre_def]
                      |> store_as "Sub_Suc";

val Pre_O = PRE_def |> conjE1 |> conjE1 |> rewr_rule[Pre_def]
                    |> store_as "Pre_O";

val Lt_Suc = prove_store("Lt_Suc",
e0
(rw[Lt_def,Le_def,Sub_Suc,Suc_NEQ,Sub_EQ_O,Pre_O])
(form_goal “!a:1->N. Lt(a,Suc(a))”));

val O_xor_Suc = O_xor_SUC |> rewr_rule[Suc_def]
                          |> store_as "O_xor_Suc";

val Add_Suc_Lt = prove_store("Add_Suc_Lt",
e0
(strip_tac >>
 qby_tac ‘?P. !b. Lt(a,Add(a,Suc(b))) <=> P o b = TRUE’
 >-- (qexists_tac 
      ‘Char(LT) o Pa(a o To1(N), ADD o Pa(a o To1(N),SUC))’ >>
      rw[GSYM Lt_def1,o_assoc,Pa_distr,Suc_def] >>
      once_rw[one_to_one_id] >> rw[idR,Add_def]) >>
 pop_assum strip_assume_tac >> arw[] >>
 rw[IP_el] >> pop_assum (assume_tac o GSYM) >> arw[] >> strip_tac>--
(rw[Lt_def,Le_def,Add_Suc,Add_O,Sub_Suc,Pre_O,O_xor_Suc,
        Suc_NEQ,Pre_O,Sub_EQ_O]) >>
 rpt strip_tac >> rw[Add_Suc] >> rw[Lt_Suc_Le] >>
 rw[GSYM Add_Suc] >> fs[Lt_def,Suc_def]
 )
(form_goal
 “!a:1->N b. Lt(a,Add(a,Suc(b)))”));




val ADD_assoc = prove_store("ADD_assoc",
e0
(assume_tac equality_ind >>
 pop_assum (qspecl_then [‘N * N’,‘N’,‘ADD o Pa(p2(N * N,N),ADD o p1(N * N,N))’,‘N * N’,‘ADD o Pa(ADD o Pa(p2(N * N,N),p1(N,N) o p1(N * N,N)), p2(N,N) o p1(N * N,N))’] assume_tac) >> 
 qsuff_tac
 ‘!n0:1->N p m.ADD o Pa(m, ADD o Pa(n0,p)) = 
           ADD o Pa(ADD o Pa(m,n0),p)’
 >-- (strip_tac >>  arw[]) >>
 strip_tac >> strip_tac >>
 first_x_assum
 (qsspecl_then [‘Pa(n0,p)’,‘Pa(n0,p)’] assume_tac) >>
 fs[Pa_distr,o_assoc,p12_of_Pa] >>
 pop_assum (K all_tac) >>
 rw[ADD_O_n,ADD_el,ADD_SUC] >> rpt strip_tac >>
 arw[])
(form_goal
 “!m:1->N n0 p. ADD o Pa(m, ADD o Pa(n0,p)) = 
           ADD o Pa(ADD o Pa(m,n0),p)”));



val Add_assoc = ADD_assoc |> rewr_rule[Add_def] |> store_as "Add_assoc";

val Lt_trans = prove_store("Lt_trans",
e0
(rw[Lt_def] >>
 assume_tac Le_trans >> rpt strip_tac >--
 (first_x_assum irule >> qexists_tac ‘a2’ >> arw[]) >>
 qby_tac ‘(?p1. Add(a1,Suc(p1)) = a2) & 
          ?p2. Add(a2,Suc(p2)) = a3’ >-- 
 (drule Le_Add_ex >> rev_drule Le_Add_ex >> fs[] >>
 qby_tac ‘~(p = O)’
 >-- (ccontra_tac >> fs[Add_O2]) >>
 qby_tac ‘~(p' = O)’
 >-- ccontra_tac >> fs[Add_O2] >>
 fs[O_xor_Suc] >> strip_tac 
 >-- (qexists_tac ‘n0'’ >> arw[] >> once_rw[Add_sym] >> fs[]) >>
 (qexists_tac ‘n0’ >> arw[] >> once_rw[Add_sym] >> fs[])) >>
 pop_assum (strip_assume_tac o GSYM) >>
 fs[] >> rw[GSYM Add_assoc] >> once_rw[Add_Suc] >>
 assume_tac Add_Suc_Lt >> fs[Lt_def])
(form_goal “!a1:1->N a2 a3. Lt(a1,a2) & Lt(a2,a3) ==> Lt(a1,a3)”));


(*TODO: delete LE_cases_iff*)

val Le_asym = prove_store("Le_asym",
e0
(rpt strip_tac >> drule Le_cases >> pop_assum strip_assume_tac >>
 arw[] >> rev_drule Le_cases >> pop_assum strip_assume_tac >> arw[] >>
 qby_tac ‘Lt(a,a)’ 
 >-- (irule Lt_trans >> qexists_tac ‘b’ >> arw[]) >>
 fs[Lt_def])
(form_goal
 “!a:1->N b. Le(a,b) & Le(b,a) ==> a = b”));






val Add_sym' = GSYM Add_sym

val MUL_def = Thm1 |> allE $ rastt "N" 
                |> allE $ rastt "N" 
                |> allE $ rastt "O o To1(N)"
                |> allE $ rastt "ADD o Pa(p2(N * N,N),p1(N, N) o p1(N * N,N))"
                |> uex_expand |> ex2fsym0 "MUL" [] |> conjE1
                |> rewr_rule[o_assoc,To1_def,Pa_distr,p12_of_Pa,idR]
                |> conv_rule $ rand_fconv no_conv (rewr_fconv $ eq_sym "ar")
                |> store_as "MUL_def";

val Mul_ex = prove_store("Mul_ex",
e0
(rpt strip_tac >> qexists_tac ‘MUL o Pa(a,b)’ >> rw[])
(form_goal “!X a:X->N b.?ab. MUL o Pa(a,b) = ab”));

val Mul_def = Mul_ex |> spec_all |> ex2fsym0 "Mul" ["a","b"]
                     |> gen_all |> store_as "Mul_def";

val Mul_O = prove_store("Mul_O",
e0
(strip_tac >> rw[GSYM Mul_def] >> 
 assume_tac MUL_def >>
 qby_tac ‘MUL o Pa(p1(N, 1), O o To1(N * 1)) o Pa(n,id(1))= 
          O o To1(N * 1) o Pa(n,id(1))’ 
 >-- arw[GSYM o_assoc] >>
 pop_assum mp_tac >> rw[Pa_distr,p12_of_Pa,o_assoc] >> once_rw[one_to_one_id] >>
 rw[idR])
(form_goal “!n:1->N. Mul(n,O) = O”));

val Mul_Suc = prove_store("Mul_Suc",
e0
(rpt strip_tac >> 
 rw[GSYM Mul_def,GSYM Add_def,GSYM Suc_def] >>
 assume_tac MUL_def >>
 qby_tac ‘MUL o Pa(p1(N, N), SUC o p2(N, N)) o Pa(n,n0) = 
          ADD o Pa(MUL, p1(N, N)) o Pa(n,n0)’
 >-- arw[GSYM o_assoc] >>
 pop_assum mp_tac >> rw[o_assoc,Pa_distr,p12_of_Pa]
 )
(form_goal “!n:1->N n0. Mul(n,Suc(n0)) = Add(Mul(n,n0),n)”));

val Mul_LEFT_O = prove_store("Mul_LEFT_O",
e0
(qby_tac ‘?P. !m. Mul(O,m) = O <=> P o m = TRUE’ >--
 (qexists_tac ‘EQ(Mul(O o To1(N),id(N)),O o To1(N))’ >>
  rw[GSYM EQ_def,Eq_property_TRUE,Pa_distr,o_assoc,idL,idR,GSYM Mul_def]>>
 once_rw[one_to_one_id] >> rw[idL,idR])  >>
 pop_assum strip_assume_tac >> arw[] >> rw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 rw[Mul_O,Suc_def,Mul_Suc] >> rpt strip_tac >> arw[Add_O])
(form_goal
 “!m. Mul(O,m) = O”));

val Mul_LEFT_1 =  prove_store("Mul_LEFT_1",
e0
(qby_tac ‘?P. !m. Mul(Suc(O),m) = m <=> P o m = TRUE’ >--
 (qexists_tac ‘EQ(Mul(Suc(O) o To1(N),id(N)),id(N))’ >>
 rw[GSYM EQ_def,Eq_property_TRUE,Pa_distr,o_assoc,idL,idR,GSYM Mul_def]>>
 once_rw[one_to_one_id] >> rw[idL,idR]) >>
 pop_assum strip_assume_tac >> arw[] >> rw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 rw[Mul_O,Suc_def,Mul_Suc] >> rpt strip_tac >> arw[Add_Suc,Add_O])
(form_goal “!m. Mul(Suc(O),m) = m”));

val Mul_RIGHT_1 = prove_store("Mul_RIGHT_1",
e0
(rw[Mul_Suc,Add_O2,Mul_O])
(form_goal “!m. Mul(m,Suc(O)) = m”));

val Mul_Suc1 = prove_store("Mul_Suc1",
e0
(qby_tac ‘?P.!m. (!n. Mul(Suc(n),m) = Add(m,Mul(n,m))) <=> P o m = TRUE’
 >-- (qexists_tac ‘ALL(EQ(Mul(Suc(p1(N,N)),p2(N,N)) , 
                          Add(p2(N,N),MUL)) )’ >>
      strip_tac >>
      rw[ALL_property,GSYM EQ_def,Eq_property_TRUE,GSYM Mul_def,Pa_distr,p12_of_Pa,o_assoc,GSYM Suc_def,GSYM Add_def] ) >>
 pop_assum strip_assume_tac >> arw[] >> rw[IP_el] >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Mul_O,Add_O] >> rw[Suc_def,Mul_Suc] >> rpt strip_tac >>
 arw[] >> rw[Add_Suc] >> 
 qsspecl_then [‘Suc(n)’,‘ Add(Mul(n', n), n')’] assume_tac Add_sym >> 
 arw[Add_Suc] >> 
 qsspecl_then [‘n’,‘Mul(n',n)’] assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >> 
 qsspecl_then [‘n'’,‘n’] assume_tac Add_sym >> arw[]
 )
(form_goal
 “!m:1->N n. Mul(Suc(n),m) = Add(m,Mul(n,m))”));


val Mul_clauses = prove_store("Mul_clauses",
e0
(rw[Mul_O,Mul_Suc,Mul_Suc1,Mul_LEFT_1,Mul_RIGHT_1,Mul_LEFT_O] >>
 rpt strip_tac >--
 qsspecl_then [‘n’,‘Mul(m,n)’] accept_tac Add_sym >> 
 qsspecl_then [‘Mul(m,n)’,‘m’] accept_tac Add_sym)
(form_goal “!m n. (Mul(O,m) = O) & (Mul(m,O) = O) & 
                  (Mul(Suc(O),m) = m) & (Mul(m,Suc(O)) = m) &
                  (Mul(Suc(m),n) = Add(Mul(m,n),n)) &
                  (Mul(m,Suc(n)) = Add(m,Mul(m,n)))”));



val Mul_clauses' = prove_store("Mul_clauses'",
e0
(rw[Mul_O,Mul_Suc,Mul_Suc1,Mul_LEFT_1,Mul_RIGHT_1,Mul_LEFT_O] >>
 rpt strip_tac >--
 qsspecl_then [‘n’,‘Mul(m,n)’] accept_tac Add_sym >> 
 qsspecl_then [‘Mul(m,n)’,‘m’] accept_tac Add_sym)
(form_goal “!m. (Mul(O,m) = O) & (Mul(m,O) = O) & 
                  (Mul(Suc(O),m) = m) & (Mul(m,Suc(O)) = m) &
                  !n.(Mul(Suc(m),n) = Add(Mul(m,n),n)) &
                  (Mul(m,Suc(n)) = Add(m,Mul(m,n)))”));



val Mul_sym = prove_store("Mul_sym",
e0
(qby_tac ‘?P.!m.(!n. Mul(m,n) = Mul(n,m)) <=> P o m = TRUE’ >--
 (qexists_tac ‘ALL(EQ(MUL o Swap(N,N),MUL))’ >> strip_tac >>
  rw[ALL_property,GSYM EQ_def,Eq_property_TRUE,o_assoc,Pa_distr,p12_of_Pa,Swap_Pa,GSYM Mul_def])>>
 pop_assum strip_assume_tac >> arw[] >> rw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rw[Mul_clauses,Suc_def] >>
 rpt strip_tac >> arw[] >>
 qsspecl_then [‘Mul(n',n)’,‘n'’] accept_tac Add_sym)
(form_goal
 “!m:1->N n. Mul(m,n) = Mul(n,m)”));

val Add_clauses = prove_store("Add_clauses",
e0
(rw[Add_O,Add_O2,Add_Suc,Add_Suc1])
(form_goal “(!m. Add(O,m) = m & Add(m,O) = m) & 
            !m:1->N n.Add(Suc(m),n) = Suc(Add(m,n)) &
                 Add(m,Suc(n)) = Suc(Add(m,n))”));

(*RIGHT_ADD_DISTRIB *)
val RIGHT_DISTR = prove_store("RIGHT_DISTR",
e0
(strip_tac >> strip_tac >>
 qby_tac ‘?P. !p. Mul(Add(m,n),p) = Add(Mul(m,p),Mul(n,p)) <=> P o p = TRUE’ 
 >-- (qexists_tac ‘EQ(Mul(Add(m,n) o To1(N),id(N)),
                      Add(Mul(m o To1(N),id(N)),Mul(n o To1(N),id(N))))’ >>
      rw[GSYM EQ_def,Eq_property_TRUE,GSYM Mul_def,Pa_distr,o_assoc,GSYM Add_def] >>
      once_rw[one_to_one_id] >> rw[idL,idR] )>>
 pop_assum strip_assume_tac >> arw[] >> rw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Mul_clauses,Add_clauses] >>
 rw[Suc_def] >> strip_tac >> arw[] >>
 rw[Mul_clauses,Add_clauses,GSYM Add_assoc] >> strip_tac >>
 arw[]>> 
 qsuff_tac ‘Add(n, Add(Mul(m, n'), Mul(n, n'))) = 
            Add(Mul(m, n'), Add(n, Mul(n, n')))’ 
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘Mul(m, n')’,‘Add(n, Mul(n, n'))’] assume_tac Add_sym >>
 arw[] >> 
 rw[GSYM Add_assoc] >>
 qsspecl_then [‘Mul(m, n')’,‘Mul(n, n')’] assume_tac Add_sym >> arw[]
 )
(form_goal “!m:1->N n p. Mul(Add(m,n),p) = Add(Mul(m,p),Mul(n,p))”));

val LEFT_DISTR = prove_store("LEFT_DISTR",
e0
(rpt strip_tac >>
 qsspecl_then [‘p’,‘Add(m,n)’] assume_tac Mul_sym >> arw[RIGHT_DISTR] >>
 qsspecl_then [‘p’,‘m’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘p’,‘n’] assume_tac Mul_sym >> arw[])
(form_goal “!m:1->N n p. Mul(p,Add(m,n)) = Add(Mul(p,m),Mul(p,n))”));

val Mul_assoc = prove_store("Mul_assoc",
e0
(qby_tac ‘?P. !m. (!n p. Mul(m,Mul(n,p)) = Mul(Mul(m,n),p)) <=> P o m = TRUE’
 >-- (qexists_tac ‘ALL(ALL(EQ(Mul(p33(N,N,N),Mul(p32(N,N,N),p31(N,N,N))),
                              Mul(Mul(p33(N,N,N),p32(N,N,N)),p31(N,N,N)))))’ >>
      strip_tac >> rw[ALL_property,GSYM EQ_def,Eq_property_TRUE,GSYM p31_def,
      GSYM p32_def,GSYM p33_def,Pa_distr,o_assoc,p12_of_Pa,GSYM Mul_def]) >>
 pop_assum strip_assume_tac >> arw[] >> rw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Mul_clauses,RIGHT_DISTR,Suc_def] >> rpt strip_tac >>
 arw[] >> rw[GSYM Add_assoc])
(form_goal “!m:1->N n p. Mul(m,Mul(n,p)) = Mul(Mul(m,n),p)”));


val LESS_EQ_LESS_EQ_MONO = prove_store("LESS_EQ_LESS_EQ_MONO",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(m,q)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 once_rw[Add_sym] >> arw[LESS_EQ_MONO_ADD_EQ])
(form_goal “!m:1->N n p q. (Le(m,p) & Le(n,q)) ==> Le(Add(m,n),Add(p,q))”));

(*LESS_MONO_MULT*)
val Le_MONO_Mul = prove_store("Le_MONO_Mul",
e0
(strip_tac >> strip_tac >>
 qby_tac ‘?P. !p. (Le(m,n) ==> Le(Mul(m,p),Mul(n,p))) <=> P o p = TRUE’ 
 >-- (qexists_tac ‘Imp(Char(LE) o Pa(m,n) o To1(N), 
                       Char(LE) o Pa(Mul(m o To1(N),id(N)),
                                     Mul(n o To1(N),id(N))))’ >>
      strip_tac >> 
      rw[GSYM Imp_def,IMP_def,Pa_distr,p12_of_Pa,o_assoc,GSYM Mul_def] >>
      once_rw[one_to_one_id] >> rw[idL,idR] >> 
      rw[GSYM Le_def1]) >> 
 pop_assum strip_assume_tac >> arw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 (*check behaviour of arw, why it does not make change without strip*)
 rw[Mul_O,Le_refl,Suc_def] >> strip_tac >> arw[] >>
 rw[Mul_Suc] >> rpt strip_tac >>
 first_x_assum drule >> irule LESS_EQ_LESS_EQ_MONO >> arw[])
(form_goal “!m:1->N n p. Le(m,n) ==> Le(Mul(m,p),Mul(n,p))”));

val Le_MONO_Mul' = Le_MONO_Mul |> strip_all_and_imp
                               |> gen_all
                               |> disch_all
                               |> gen_all
                               |> store_as "Le_MONO_Mul'";

val Le_MONO_Mul2 = prove_store("Le_MONO_Mul2",
e0
(rpt strip_tac >> 
 irule Le_trans >> qexists_tac ‘Mul(m,j)’ >> 
 rev_drule Le_MONO_Mul' >> arw[] >>
 drule Le_MONO_Mul' >> once_rw[Mul_sym] >> arw[])
(form_goal “!m:1->N n i j. Le(m,i) & Le(n,j) ==> Le(Mul(m,n),Mul(i,j))”));
