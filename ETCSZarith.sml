
val ZR_subset_ex = 
    pred_subset_ex' |> allE $ rastt "(N * N) * (N * N)"
                   |> allE $ rastt $ q2str
‘Eq(N) o Pa(ADD o 
     Pa(p1(N,N) o p1(N * N,N * N),
        p2(N,N) o p2(N * N,N * N)),
     ADD o 
     Pa(p2(N,N) o p1(N * N,N * N), 
        p1(N,N) o p2(N * N,N * N)))’

val ZR_subset_def = ex2fsym "ZR" [] (iffRL $ eqT_intro $ spec_all ZR_subset_ex)
                        |> C mp (trueI []) |> gen_all

val ZRI_def = 
ex2fsym "ZRI" [] (iffRL $ eqT_intro $ spec_all ZR_subset_def)
                        |> C mp (trueI []) |> gen_all

val ZRI_Mono = conjE1 ZRI_def
                      |> store_as "ZRI_Mono";

val Z_ex = 
    iscoEq_ex |> allE $ rastt "ZR" 
            |> allE $ rastt "N * N"
            |> allE $ rastt "p1(N * N, N * N) o ZRI"
            |> allE $ rastt "p2(N * N, N * N) o ZRI"

val Z_def = ex2fsym "Z" [] (iffRL $ eqT_intro $ spec_all Z_ex)
                        |> C mp (trueI []) |> gen_all

val toZ_def = ex2fsym "toZ" [] (iffRL $ eqT_intro $ spec_all Z_def)
                        |> C mp (trueI []) |> gen_all

(*val _ = new_fun "Pow" (ob_sort,[("A",ob_sort)])*)

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


val toZ_Epi = prove_store("toZ_Epi",
e0
(assume_tac toZ_def >>
 drule coEqa_Epi >> first_x_assum accept_tac)
(form_goal
 “Epi(toZ)”));


val REP_ex = prove_store("REP_ex",
e0
(assume_tac toZ_Epi >> drule Epi_has_section >>
 first_x_assum accept_tac)
(form_goal 
 “?rep. toZ o rep = id(Z)”));

val REP_def = REP_ex|> ex2fsym0 "REP" []
                    |> store_as "REP_def";

val ADDz_ex = prove_store("ADDz_ex",
e0
(qexists_tac ‘toZ o ADDj o Pa(REP o p1(Z,Z),REP o p2(Z,Z))’ >>
 rw[])
(form_goal
 “?addz. toZ o ADDj o Pa(REP o p1(Z,Z),REP o p2(Z,Z)) = addz”));



val ADDz_def = ADDz_ex |> ex2fsym0 "ADDz" []
                       |> store_as "ADDz_def";



val ADDj_SYM = prove_store("ADDj_SYM",
e0
(rw[GSYM Swap_def] >>
 irule FUN_EXT >> rpt strip_tac >>
 qby_tac
 ‘?a0 b0 c0 d0.a = Pa(Pa(a0,b0),Pa(c0,d0))’
 >-- (qsspecl_then [‘a’] assume_tac has_components >>
     pop_assum strip_assume_tac >> 
     qsspecl_then [‘a'’] assume_tac has_components >>
     qsspecl_then [‘b’] assume_tac has_components >>
     pop_assum_list (map_every strip_assume_tac) >>
     qexistsl_tac [‘a'''’,‘b''’,‘a''’,‘b'’] >> arw[]) >>
 pop_assum strip_assume_tac >> arw[] >>
 rw[GSYM ADDj_def] >> rw[Pa_distr,o_assoc,p12_of_Pa] >> 
 qspecl_then [‘c0’,‘a0’] assume_tac ADD_SYM >>
 qspecl_then [‘d0’,‘b0’] assume_tac ADD_SYM >> 
 arw[]
 )
(form_goal
 “ADDj o Swap(N * N,N * N) = ADDj”));


val ADDz_SYM = prove_store("ADDz_SYM",
e0
(rpt strip_tac >>
 rw[GSYM ADDz_def,o_assoc,Pa_distr,p12_of_Pa] >> 
 qsuff_tac
 ‘ADDj o Pa(REP o z1,REP o z2) = 
  ADDj o Pa(REP o z2,REP o z1)’ 
 >-- (strip_tac >> arw[]) >>
 qby_tac
 ‘ADDj o Pa(REP o z1, REP o z2) = 
  ADDj o Swap(N * N,N * N) o Pa(REP o z2, REP o z1)’
 >-- (rw[GSYM Swap_def,Pa_distr,p12_of_Pa,o_assoc]) >>
 arw[] >> rw[GSYM o_assoc,ADDj_SYM])
(form_goal
 “!z1:1->Z z2:1->Z. ADDz o Pa(z1,z2) = ADDz o Pa(z2,z1)”));




val ZR_Refl = prove_store("ZR_Refl",
e0
(rw[Refl_Diag] >>
 rw[GSYM to_P_component] >> 
 fconv_tac 
 (basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))>>
 rw[GSYM ZRI_def] >> 
 irule FUN_EXT >> strip_tac >>
 qsspecl_then [‘a’] assume_tac has_components >>
 pop_assum strip_assume_tac >>
 arw[] >>
 rw[o_assoc,Pa_distr,p12_of_Pa,GSYM Diag_def,idL,
    GSYM True_def] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 rw[Eq_property_TRUE] >> 
 qsspecl_then [‘a'’,‘b’] accept_tac ADD_SYM
 )
(form_goal “Refl(p1(N * N, N * N) o ZRI,p2(N * N, N * N) o ZRI)”));




val ZR_Sym = prove_store("ZR_Sym",
e0
(rw[Sym_alt,GSYM to_P_component,p21_Swap] >>
 irule prop_2_half2 >> 
 assume_tac ZRI_Mono >>
 drule Swap_Mono >> arw[] >>
 rpt strip_tac >>
 dflip_tac >>  rw[GSYM ZRI_def] >>
 qby_tac
 ‘Swap(N * N,N * N) o (Swap(N * N, N * N) o ZRI) o xb = 
  Swap(N * N, N * N) o x’
 >-- arw[] >>
 pop_assum mp_tac >> rw[GSYM o_assoc,Swap_Swap_id,idL]>>
 strip_tac >>
 qby_tac 
 ‘?xb. Swap(N * N,N * N) o x = ZRI o xb’ 
 >-- (qexists_tac ‘xb’ >> arw[]) >>
 pop_assum mp_tac >>
 rw[GSYM ZRI_def,True1TRUE] >>
 rw[Eq_property_TRUE,o_assoc,Pa_distr,p12_of_Pa] >>
 qsspecl_then [‘x’] strip_assume_tac has_components >>
 qsspecl_then [‘a’] strip_assume_tac has_components >>
 qsspecl_then [‘b’] strip_assume_tac has_components >>
 arw[p12_of_Pa] >>
 rw[GSYM Swap_def,o_assoc,Pa_distr,p12_of_Pa] >>
 strip_tac >>
 qsspecl_then [‘a''’,‘b'’] assume_tac ADD_SYM >> fs[] >>
 qsspecl_then [‘b''’,‘a'’] assume_tac ADD_SYM >> fs[] )
(form_goal “Sym(p1(N * N, N * N) o ZRI,p2(N * N, N * N) o ZRI)”));







(*
local 
val l =
fVar_Inst 
[("P",([("m",mem_sort N)],
 “!n0 p. Add(m,Add(n0,p)) = Add(Add(m,n0),p)”))] 
N_ind_P
in
val Add_assoc = prove_store("Add_assoc",
e0
(irule l >> rw[Add_O,Suc_def,Add_Suc,Add_Suc1,Add_O2] >>
 rpt strip_tac >>arw[])
(form_goal
 “!m n0 p. Add(m,Add(n0,p)) = Add(Add(m,n0),p)”));
end

*)
val ZR_Trans =prove_store("ZR_Trans",
e0
(assume_tac ZRI_Mono >>
 irule $ iffRL Trans_alt' >> rw[GSYM to_P_component]>>
 arw[] >> dflip_tac >> rpt strip_tac >>
 qby_tac
 ‘?r01. Pa(h0, h1) = ZRI o r01’
 >-- (qexists_tac ‘r01’ >> arw[]) >>
 qby_tac
 ‘?r12. Pa(h1, h2) = ZRI o r12’
 >-- (qexists_tac ‘r12’ >> arw[]) >>
 pop_assum mp_tac >> pop_assum mp_tac >>
 rw[GSYM ZRI_def,True1TRUE,Pa_distr,
    Eq_property_TRUE,o_assoc,p12_of_Pa] >> 
 qsspecl_then [‘h0’] assume_tac has_components >> 
 pop_assum strip_assume_tac >>
 qsspecl_then [‘h1’] assume_tac has_components >> 
 pop_assum strip_assume_tac >> 
 qsspecl_then [‘h2’] assume_tac has_components >> 
 pop_assum strip_assume_tac >>
 arw[p12_of_Pa] >> rpt strip_tac >>
 qby_tac
 ‘ADD o Pa(ADD o Pa(a, b''),b') = 
  ADD o Pa(a,ADD o Pa(b',b''))’
 >-- (qspecl_then [‘b'’,‘b''’] assume_tac ADD_SYM >>
      arw[] >> rw[ADD_assoc]) >>
 fs[ADD_assoc] >> rfs[] >>
 fs[GSYM ADD_assoc] >> rfs[] >>
 qspecl_then [‘b'’,‘a''’] assume_tac ADD_SYM >> fs[] >>
 fs[ADD_assoc] >>
 assume_tac ADD_SUB >>
 first_assum (qspecl_then [‘ADD o Pa(a, b'')’,‘b'’]
 assume_tac) >>
 first_x_assum (qspecl_then [‘ADD o Pa(b, a'')’,‘b'’]
 assume_tac) >>
 pop_assum (assume_tac o GSYM) >>once_arw[] >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 pop_assum (K all_tac) >>
 arw[])
(form_goal
 “Trans(p1(N * N, N * N) o ZRI,p2(N * N, N * N) o ZRI)”));

val Thm6_ZR = prove_store("Thm6_ZR",
e0
(assume_tac Thm6_isEq >> 
 qby_tac ‘ZRI =  Pa(p1(N * N, N * N) o ZRI, p2(N * N, N * N) o ZRI)’
 >-- rw[GSYM to_P_component] >> once_arw[] >>
 first_x_assum irule >> rw[GSYM to_P_component] >> 
 rw[ZRI_Mono,ZR_Trans,ZR_Sym,ZR_Refl,toZ_def])
(form_goal
 “isEq(toZ o p1(N * N, N * N),toZ o p2(N * N,N * N),ZRI)”));


val Addz_ex = prove_store("Addz_ex",
e0
(rpt strip_tac >> qexists_tac ‘ADDz o Pa(z1,z2)’ >> rw[])
(form_goal
 “!X z1:X->Z z2. ?z12. ADDz o Pa(z1,z2) = z12”));

val Addz_def = Addz_ex |> spec_all |> ex2fsym0 "Addz" ["z1","z2"]
                       |> gen_all |> store_as "Addz_def";

val asz_ex = prove_store("asz_ex",
e0
(rpt strip_tac >> qexists_tac ‘toZ o pair’ >> rw[])
(form_goal “!X pair:X-> N * N. ?z. toZ o pair= z”));

val asz_def = asz_ex |> spec_all |> ex2fsym0 "asz" ["pair"]
                     |> gen_all |> store_as "asz_def";


val Addj_ex = prove_store("Addj_ex",
e0
(rpt strip_tac >> qexists_tac ‘ADDj o Pa(ab,cd)’ >> rw[])
(form_goal “!X ab:X->N * N cd. ?acbd.ADDj o Pa(ab,cd) = acbd”));

val Addj_def = Addj_ex |> spec_all |> ex2fsym0 "Addj" ["ab","cd"]
                       |> gen_all |> store_as "Addj_def";

val _ = new_pred "ZR" [("ab",ar_sort (mk_ob "X") (Po N N)),
                       ("cd",ar_sort (mk_ob "X") (Po N N))]

val ZR_def0 = store_ax("ZR_def0",
“!X ab:X->N * N cd. ZR(ab,cd) <=> ?x0:X-> ZR.Pa(ab,cd) = ZRI o x0”);


val ZR_def = prove_store("ZR_def",
e0
(rpt strip_tac >> 
 rw[ZR_def0,GSYM ZRI_def,GSYM Eq_property,p12_of_Pa,Pa_distr,o_assoc] >>
 qsspecl_then [‘ab’] strip_assume_tac has_components >>
 qsspecl_then [‘cd’] strip_assume_tac has_components >> arw[p12_of_Pa,Fst_Snd_Pa] >> dimp_tac >> strip_tac >> fs[GSYM Add_def])
(form_goal
 “!X ab:X->N * N cd. ZR(ab,cd) <=> 
  Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))”));


val rep_ex = prove_store("rep_ex",
e0
(rpt strip_tac >> qexists_tac ‘REP o z’ >> rw[] )
(form_goal “!X z:X->Z.?r. REP o z = r”));

val rep_def= rep_ex |> spec_all |> ex2fsym0 "rep" ["z"] 
                    |> gen_all |> store_as "rep_def";

val rep_asz = prove_store("rep_asz",
e0
(rpt strip_tac >> rw[GSYM rep_def,GSYM asz_def,REP_def,GSYM o_assoc,idL])
(form_goal “!X z:X->Z. asz(rep(z)) = z”)); 

(*asz_def rep_def toZ_def REP_def*)



val samez_cond = prove_store("samez_cond",
e0
(rw[ZR_def,GSYM asz_def] >> 
 assume_tac Thm6_ZR >> drule via_Eq_iff >> 
 rpt strip_tac >>
 (*qsspecl_then [‘ab’] strip_assume_tac has_components >>
 qsspecl_then [‘cd’] strip_assume_tac has_components >> fs[] >> *)
 first_x_assum (qsspecl_then [‘Pa(ab,cd)’] assume_tac) >> fs[o_assoc,p12_of_Pa] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> lflip_tac >> 
 rw[GSYM ZR_def] >> rw[ZR_def0])
(form_goal “!X ab:X-> N * N cd. asz(ab) = asz(cd) <=> ZR(ab,cd)”));

val ZR_samez = GSYM samez_cond;

val rep_asz_ZR = prove_store("rep_asz_ZR",
e0
(rw[GSYM samez_cond,rep_asz])
(form_goal “!X ab:X->N * N.ZR(ab,rep(asz(ab)))”));

val rep_ZR_eq = prove_store("rep_ZR_eq",
e0
(rw[ZR_samez,rep_asz])
(form_goal
 “!X z1:X->Z z2. ZR(rep(z1),rep(z2)) <=> z1 = z2”));

val z_eq_cond = prove_store("z_eq_cond",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexistsl_tac [‘rep(z1)’,‘rep(z2)’] >> arw[rep_asz,rep_ZR_eq]) >>
 fs[ZR_samez])
(form_goal “!X z1:X->Z z2. z1 = z2 <=> ?ab cd. asz(ab) = z1 & asz(cd) = z2 & ZR(ab,cd) ”));

val ZR_refl = prove_store("ZR_refl",
e0
(rw[ZR_def] >> rpt strip_tac >>
 qsspecl_then [‘Fst(ab)’,‘Snd(ab)’] assume_tac Add_sym >> arw[])
(form_goal “!ab:1->N * N.ZR(ab,ab)”));


val ZR_sym = prove_store("ZR_sym",
e0
(rw[ZR_def] >> rpt strip_tac >> lflip_tac >>
 qsspecl_then [‘Fst(ab)’,‘Snd(cd)’] assume_tac Add_sym >> arw[] >> 
 qsspecl_then [‘Fst(cd)’,‘Snd(ab)’] assume_tac Add_sym >> arw[])
(form_goal “!ab:1->N * N cd.ZR(ab,cd) <=> ZR(cd,ab)”));


val ZR_trans = prove_store("ZR_sym",
e0
(assume_tac ZR_Trans >> 
 assume_tac ZRI_Mono >>
 pop_assum mp_tac >> once_rw[to_P_component] >> strip_tac >> 
 drule Trans_alt' >> fs[GSYM to_P_component] >> pop_assum (K all_tac) >>
 rw[ZR_def0] >> rpt strip_tac >> dflip_tac >> first_x_assum irule >>
 qexistsl_tac [‘cd’,‘x0’,‘x0'’] >> arw[])
(form_goal “!ab:1->N * N  cd ef.ZR(ab,cd) & ZR(cd,ef) ==> ZR(ab,ef)”));

val ZR_cond = prove_store("ZR_cond",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (qexistsl_tac [‘ab’,‘cd’] >> arw[ZR_refl]) >>
 qby_tac ‘ZR(ab,cd1)’ 
 >-- (irule ZR_trans >> qexists_tac ‘ab1’ >> arw[]) >>
 qby_tac ‘ZR(cd1,cd)’
 >-- (irule $ iffLR ZR_sym >> arw[]) >>
 irule ZR_trans >>
 qexists_tac ‘cd1’ >> arw[])
(form_goal “!ab:1->N * N cd.ZR(ab,cd) <=> ?ab1 cd1. ZR(ab,ab1) & ZR(cd,cd1) & ZR(ab1,cd1)”));


val rep_rel_all = prove_store("rep_rel_all",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
      irule $ iffLR ZR_sym >> rw[rep_asz_ZR]) >>
 fs[ZR_samez,rep_asz])
(form_goal
 “!z:1->Z rz.asz(rz) = z <=> ZR(rep(z),rz)”));

val Pa_Fst_Snd = to_P_component |> rewr_rule[Fst_def,Snd_def] |> GSYM
                                |> store_as "Pa_Fst_Snd";

val z_has_rep = prove_store("z_has_rep",
e0
(strip_tac >> rw[GSYM asz_def] >> rpt strip_tac >>
 qexistsl_tac [‘Fst(rep(z))’,‘Snd(rep(z))’] >>
 rw[Pa_Fst_Snd] >> rw[asz_def,rep_asz])
(form_goal
 “!X z:X->Z. ?a b. z = asz(Pa(a,b))”));

val Addj_property =  prove_store("Addj_property",
e0
(rw[GSYM Addj_def,GSYM ADDj_def,p12_of_Pa,Pa_distr,o_assoc,GSYM Add_def])
(form_goal
 “!a:1->N b c d. Addj(Pa(a,b),Pa(c,d)) = Pa(Add(a,c),Add(b,d))”));


val J1_i = prove_store("J1_i",
e0
(rw[ZR_def,Addj_property] >> rpt strip_tac >> 
 rw[Fst_Snd_Pa] >>
 qsspecl_then [‘Add(Add(a, c), e)’,‘Add(b, Add(d, f))’] assume_tac Add_sym >>
 arw[] >> rw[GSYM Add_assoc])
(form_goal “!a b c d e f:1->N. 
 ZR(Addj(Addj(Pa(a,b),Pa(c,d)),Pa(e,f)),
    Addj(Pa(a,b),Addj(Pa(c,d),Pa(e,f))))”));


val ZR_def' = prove_store("ZR_def'",
e0
(rw[ZR_def] >> rpt strip_tac >> 
 qsspecl_then [‘Snd(ab)’,‘Fst(cd)’] assume_tac Add_sym >>
 arw[])
(form_goal
 “!ab:1 ->N * N cd.
        ZR(ab, cd) <=> Add(Fst(ab), Snd(cd)) = Add(Fst(cd), Snd(ab))”));



val J2_i = prove_store("J2_i",
e0
(rw[Addj_property,ZR_def',Fst_Snd_Pa] >>
 rpt strip_tac >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘d'’,‘b'’] assume_tac Add_sym' >> arw[] >>
 qspecl_then [‘c’,‘d'’,‘b'’] assume_tac Add_assoc >>
 arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘Add(c',Add(d,b'))’,‘a’] assume_tac Add_sym' >> 
 arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘a’,‘b'’] assume_tac Add_sym' >>
 arw[] >>
 qsspecl_then [‘Add(c', Add(b, d))’,‘a'’]
 assume_tac Add_sym' >> arw[] >>
 rw[GSYM Add_assoc] >> 
 qsuff_tac
 ‘Add(d, Add(a', b)) = Add(b, Add(d, a'))’
 >-- (strip_tac >> arw[]) >>
 qspecl_then [‘Add(a',b)’,‘d’] assume_tac Add_sym' >>
 arw[] >> 
 qspecl_then [‘a'’,‘d’] assume_tac Add_sym' >> arw[] >>
 rw[Add_assoc] >>
 qspecl_then [‘a'’,‘b’] assume_tac Add_sym' >> arw[])
(form_goal
 “!a:1->N b a' b' c d c' d'. ZR(Pa(a,b),Pa(a',b')) & ZR(Pa(c,d),Pa(c',d')) ==>
 ZR(Addj(Pa(a,b),Pa(c,d)),Addj(Pa(a',b'),Pa(c',d')))”));

val J2_i' = prove_store("J2_i'",
e0
(rpt strip_tac >>
 qsspecl_then [‘ab’] strip_assume_tac has_components >>
 qsspecl_then [‘pq’] strip_assume_tac has_components >>
 qsspecl_then [‘cd’] strip_assume_tac has_components >>
 qsspecl_then [‘rs’] strip_assume_tac has_components >>
 fs[] >> irule J2_i >> arw[])
(form_goal
 “!ab:1->N * N pq cd rs. ZR(ab,pq) & ZR(cd,rs) ==>
 ZR(Addj(ab,cd),Addj(pq,rs))”));


val J2_i_z = prove_store("J2_i_z",
e0
(rpt strip_tac >> assume_tac J2_i >>
 rw[GSYM Addz_def,GSYM ADDz_def,o_assoc,Pa_distr] >> rw[asz_def,p12_of_Pa] >>
 rw[samez_cond] >> arw[] >>
 rw[rep_def,Addj_def]  >> 
 qsspecl_then [‘rep(asz(Pa(a,b)))’] strip_assume_tac has_components >>
 qsspecl_then [‘rep(asz(Pa(c,d)))’] strip_assume_tac has_components >>
 arw[] >> first_x_assum irule >> pop_assum_list (map_every (assume_tac o GSYM)) >>
 arw[] >> rw[GSYM rep_rel_all] >> arw[])
(form_goal
 “!z1:1->Z z2 a b c d. z1 = asz(Pa(a,b)) & z2 = asz(Pa(c,d)) ==>
 Addz(z1,z2) = asz(Addj(Pa(a,b),Pa(c,d)))”));


val Addz_eqn' = prove_store("Addz_eqn'",
e0
(rpt strip_tac >>
 assume_tac J2_i_z >>
 first_x_assum irule >> rw[])
(form_goal
 “!a:1->N b c d.
  Addz(asz(Pa(a,b)),asz(Pa(c,d))) = 
  asz(Addj(Pa(a,b),Pa(c,d)))”));

val ADDz_assoc = prove_store("ADDz_assoc",
e0
(rpt strip_tac >> 
 qsspecl_then [‘z1’] strip_assume_tac z_has_rep >>
 qsspecl_then [‘z2’] strip_assume_tac z_has_rep >>
 qsspecl_then [‘z3’] strip_assume_tac z_has_rep >>
 arw[] >> 
 rw[Addz_eqn'] >> rw[Addj_property] >>
 rw[Addz_eqn'] >> rw[GSYM Addj_property] >>
 assume_tac J1_i >> fs[ZR_samez])
(form_goal
 “!z1:1->Z z2 z3. Addz(Addz(z1,z2),z3) = Addz(z1,Addz(z2,z3))”));




val zj_ex = prove_store("zj_ex",
e0
(qexists_tac ‘Pa(O,O)’ >> rw[])
(form_goal
 “?zj.Pa(O,O) = zj”));

val zj_def = zj_ex |> ex2fsym0 "0j" []
                   |> store_as "zj_def";



val NEGj_ex = prove_store("NEGj_ex",
e0
(rpt strip_tac >> qexists_tac ‘Swap(N,N)’ >> rw[])
(form_goal “?NEGj.Swap(N,N) =NEGj ”));

val NEGj_def = NEGj_ex |> spec_all |> ex2fsym0 "NEGj" []
                       |> gen_all |> store_as "NEGj_def";



val NEGj_property = prove_store("NEGj_property",
e0
(rpt strip_tac >> rw[GSYM NEGj_def,Swap_Pa])
(form_goal “!X a:X->N b. NEGj o Pa(a,b) = Pa(b,a)”));


val Negj_ex = prove_store("Negj_ex",
e0
(rpt strip_tac >> qexists_tac ‘NEGj o ab’ >> rw[])
(form_goal “!X ab:X->N * N. ?nab. NEGj o ab = nab”));

val Negj_def = Negj_ex |> spec_all |> ex2fsym0 "Negj" ["ab"] 
                       |> gen_all |> store_as "Negj_def";

val Negj_property = NEGj_property |> rewr_rule[Negj_def]



val J1_ii = prove_store("J1_ii",
e0
(rw[GSYM zj_def,Addj_property,ZR_def,Fst_Snd_Pa,Add_O_n,Add_El] >> rpt strip_tac >>
 qsspecl_then [‘a’,‘b’] accept_tac Add_sym)
(form_goal
 “!a b.ZR(Addj(Pa(a,b),0j),Pa(a,b))”));


val zz_ex = prove_store("zz_ex",
e0
(qexists_tac ‘asz(0j)’ >> rw[])
(form_goal
 “?z. asz(0j) = z”));

val zz_def = zz_ex |> ex2fsym0 "0z" []
                   |> store_as "zz_def";


val Addz_zz = prove_store("Addz_zz",
e0
(strip_tac >> once_rw[z_eq_cond] >>
 qsspecl_then [‘z’] strip_assume_tac z_has_rep >> 
 arw[] >>
 assume_tac J1_ii >>
 fs[ZR_samez] >> 
 rw[GSYM zz_def] >> rw[GSYM zj_def,Addz_eqn'] >>
 rw[zj_def] >> arw[] >>
 qexistsl_tac [‘Pa(a,b)’,‘Pa(a,b)’] >> rw[])
(form_goal
 “!z. Addz(z,0z) = z”));

val Z2_ii = Addz_zz |> store_as "Z2_ii";

val Negz_ex =  prove_store("Negz_ex",
e0
(rpt strip_tac >> qexists_tac ‘asz(Negj(rep(z)))’ >> rw[])
(form_goal “!X z:X->Z.?nz. asz(Negj(rep(z))) = nz”));

val Negz_def = Negz_ex |> spec_all |> ex2fsym0 "Negz" ["z"]
                       |> gen_all |> store_as "Negz_def";


val J2_ii = prove_store("J2_ii",
e0
(rw[ZR_def,Negj_property,Fst_Snd_Pa] >>rpt strip_tac >> arw[])
(form_goal
 “!X a:X->N b a' b'. ZR(Pa(a,b),Pa(a',b')) ==> 
  ZR(Negj(Pa(a,b)),Negj(Pa(a',b')))”));


val J2_ii_z = prove_store("J2_ii_z",
e0
(rpt strip_tac >> assume_tac J2_ii >>
 rw[GSYM Negz_def] >> rw[samez_cond] >> 
 qsspecl_then [‘rep(z)’] strip_assume_tac has_components >> arw[] >>
 first_x_assum irule >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[GSYM rep_rel_all])
(form_goal
 “!a:1->N b z. z = asz(Pa(a,b)) ==>
  Negz(z) = asz(Negj(Pa(a,b)))”));


val Negz_eqn = prove_store("Negz_eqn",
e0
(rpt strip_tac >> irule J2_ii_z >> arw[])
(form_goal
 “!a:1->N b. Negz(asz(Pa(a,b))) = asz(Negj(Pa(a,b)))”));


val J1_iii = prove_store("J1_iii",
e0
(rw[Addj_property,GSYM zj_def,Negj_property,ZR_def,
    Fst_Snd_Pa,Add_El,Add_O_n] >>
 rpt strip_tac >>
 qspecl_then [‘a’,‘b’] assume_tac Add_sym >>
 first_x_assum accept_tac)
(form_goal
 “!a b. ZR(Addj(Pa(a,b),Negj(Pa(a,b))),0j)”));



val Z2_iii = prove_store("Z2_iii",
e0
(rpt strip_tac >>
 qsspecl_then [‘z’] strip_assume_tac z_has_rep >> 
 arw[] >> rw[Negz_eqn,Addz_eqn',Negj_property,Addj_property] >> rw[GSYM zz_def]  >>
 rw[GSYM ZR_samez,ZR_def,Fst_Snd_Pa,GSYM zj_def,Add_El,Add_O_n] >>
 qspecl_then [‘a’,‘b’] accept_tac Add_sym)
(form_goal
 “!z. Addz(z,Negz(z)) = 0z”));

val lej_ex = prove_store("lej_ex",
e0
(qexists_tac
 ‘Char(LE) o Pa(
  ADD o Pa(p1(N,N) o p1(N * N,N * N),
           p2(N,N) o p2(N * N,N * N)),
  ADD o Pa(p2(N,N) o p1(N * N,N * N),
           p1(N,N) o p2(N * N,N * N))
)’ >-- rpt strip_tac >>
 qsspecl_then [‘ab’] assume_tac has_components >>
 qsspecl_then [‘cd’] assume_tac has_components >>
 fs[] >> 
 rw[Pa_distr,p12_of_Pa,o_assoc] >>
 rw[Le_def1])
(form_goal
 “?lej. !ab:1->N * N cd. 
  lej o Pa(ab,cd) = TRUE <=> 
  Le(ADD o Pa(p1(N,N) o ab,p2(N,N) o cd),
     ADD o Pa(p2(N,N) o ab,p1(N,N) o cd))”));

val lej_def = ex2fsym0 "lej" [] lej_ex
                       |> store_as "lej_def";

(*
fun binop_t s t1 t2 = mk_fun s [t1,t2]

fun unop_t s t = mk_fun s [t]

val And = binop_t "And"

val Or = binop_t "Or"

val Imp = binop_t "Imp"

val Iff = binop_t "Iff"

val id = unop_t "id"

fun dest_ar s = 
    case view_sort s of
       vSrt("ar",[d,c]) => (d,c) 
     | _ => raise simple_fail "not an arr"

val dom = fst o dest_ar 
val cod = snd o dest_ar 

fun term2IL v t =
    if t = v then id (cod $ sort_of t)
    else
        case view_term t of 
            vVar(n,s) => binop_t "o" t (unop_t "To1" (cod $ sort_of v))
          | vFun(f,s,tl) => 
            Fun(f,ar_sort (cod $ sort_of v) (cod s),List.map (term2IL v) tl)
          | _ => raise simple_fail "bound variables should not be here"; 

fun form2IL v f = 
    case view_form f of 
        vConn("&",[f1,f2]) => 
        And (form2IL v f1) (form2IL v f2)
      | vConn("|",[f1,f2]) => 
        Or (form2IL v f1) (form2IL v f2)
      | vConn("==>",[f1,f2]) => 
        Imp (form2IL v f1) (form2IL v f2)
      | vPred(P,tl) =>

*)



(*

n : 1-> N  
!n.  &n < i 
Fun("&",1->Z,[n:1->N])


Fun("&",N->Z,[id(N)])

v |->  n  t |-> i
 
have a dict store the corres

LTz o Pa((& (id(N))): N ->Z,i o To1(N)) 


*)
(* m + n = n + m



a:1->Z

inc: N ->Z
 & (n) := inc o n:X->N



Fun("&",(->Z),[n:X->N]) 

Add(m,n) = Add(m,n)

say bound n . induct on n.

Eq_property_TRUE

Eq(N) o Pa(Add(m o To1(N),id(N)), Add(id(N), m o To1(N)))

here P is "=", tl is [m+n,n + m]

*)

(*
fun induct_tac th (ct,asl,w) = 
    let val ((n,s),f0) = dest_forall f
*)

 
val lej_property = prove_store("lej_property",
e0
(rw[lej_def,o_assoc,Pa_distr,p12_of_Pa,Add_def])
(form_goal
 “!a b c d. lej o Pa(Pa(a,b),Pa(c,d)) = TRUE <=> 
 Le(Add(a,d),Add(b,c))”));



val lej_refl = prove_store("lej_refl",
e0
(strip_tac >> rw[lej_def] >>
 qsspecl_then [‘p1(N,N) o ab’,‘p2(N,N) o ab’]
 assume_tac Add_sym >> arw[Add_def] >>
 rw[Le_refl])
(form_goal
 “!ab. lej o Pa(ab,ab) = TRUE”));



val lej_trans = prove_store("lej_trans",
e0
(rw[lej_def] >> rpt strip_tac >>
 qsspecl_then  [‘a1’] assume_tac has_components >>
 qsspecl_then  [‘a2’] assume_tac has_components >>
 qsspecl_then  [‘a3’] assume_tac has_components >>
 fs[] >> fs[] >> fs[p12_of_Pa,Add_def] >> 
 qsuff_tac ‘Le(Add(Add(a,b''),Add(a',b')),
               Add(Add(b,a''),Add(a',b')))’
 >-- rw[LESS_EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘Add(a,b')’,‘Add(a',b'')’,
               ‘Add(b,a')’,‘Add(b',a'')’]
 assume_tac Le_Add >> rfs[] >>
 qsuff_tac ‘Add(Add(a, b'), Add(a', b'')) = 
 Add(Add(a, b''), Add(a', b')) & 
 Add(Add(b, a'), Add(b', a'')) = 
 Add(Add(b, a''), Add(a', b'))’
 >-- (strip_tac >> fs[]) >> strip_tac >--
 (once_rw[Add_sym] >>
 qsspecl_then [‘a’,‘b''’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc] >> 
 qsspecl_then [‘Add(a',b')’,‘b''’] assume_tac Add_sym>>
 arw[] >> rw[GSYM Add_assoc] >>
 qsspecl_then [‘b'’,‘a’] assume_tac Add_sym >>
 once_arw[] >> rw[Add_assoc] >>
 qsspecl_then [‘b''’,‘a'’] assume_tac Add_sym >>
 once_arw[] >> rw[]) >>
 qsspecl_then [‘Add(b,a')’,‘Add(b',a'')’]
 assume_tac Add_sym >> arw[] >>
 qsspecl_then [‘b'’,‘a''’] assume_tac Add_sym >> arw[]>>
 qsspecl_then [‘b’,‘a''’] assume_tac Add_sym >> arw[]>>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(b', Add(b, a')) = Add(b, Add(a', b'))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘a'’,‘b'’] assume_tac Add_sym >>
 arw[] >>
 rw[Add_assoc] >> 
 qsspecl_then [‘b’,‘b'’] assume_tac Add_sym >> arw[])
(form_goal
 “!a1:1->N * N a2 a3. lej o Pa(a1,a2) = TRUE & lej o Pa(a2,a3) = TRUE ==> lej o Pa(a1,a3) = TRUE” ));


val J1_x = prove_store("J1_x",
e0
(rw[lej_def,Addj_property,p12_of_Pa] >>
 rw[Add_def] >> rpt strip_tac >>
 qsuff_tac 
 ‘Le(Add(Add(a, d), Add(e, f)), Add(Add(b, c), Add(e,f))) &
  Add(Add(a, e), Add(d, f)) = Add(Add(a, d), Add(e, f)) & 
  Add(Add(b, f), Add(c, e)) = Add(Add(b, c), Add(e, f))’
 >-- (rpt strip_tac >> arw[]) >>
 rpt strip_tac (* 3 *)
 >-- arw[LESS_EQ_MONO_ADD_EQ]
 >-- (rw[GSYM Add_assoc] >>
      qsuff_tac ‘Add(e, Add(d, f)) = Add(d, Add(e, f))’ 
      >-- (strip_tac >> arw[]) >>
      rw[Add_assoc] >>
      qsspecl_then [‘e’,‘d’] assume_tac Add_sym >> arw[]) >>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(f, Add(c, e)) = Add(c, Add(e, f))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘f’,‘Add(c,e)’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc] )
(form_goal
 “!a b c d e f. 
  lej o Pa(Pa(a,b),Pa(c,d)) = TRUE ==>
  lej o Pa(Addj(Pa(a,b),Pa(e,f)),
           Addj(Pa(c,d),Pa(e,f))) = TRUE”));



val J2_iv = prove_store("J2_iv",
e0
(once_rw[lej_def] >> once_rw[ZR_def] >>
 rw[Fst_Snd_Pa] >>
 rw[p12_of_Pa] >> once_rw[Add_def] >>
 rpt strip_tac >> 
 qsuff_tac 
 ‘(Le(Add(a, d), Add(b, c)) <=> 
  Le(Add(Add(a,d),Add(b',d')), Add(Add(b,c),Add(b',d')))) &
  (Le(Add(Add(a,d),Add(b',d')), Add(Add(b,c),Add(b',d'))) <=> 
  Le(Add(Add(a',d'),Add(b,d)), Add(Add(b',c'),Add(b,d)))) & 
  (Le(Add(Add(a',d'),Add(b,d)), Add(Add(b',c'),Add(b,d))) <=> 
 Le(Add(a',d'), Add(b',c')))’
 >-- (rpt strip_tac >> arw[]) >> rpt strip_tac (* 3 *)
 >-- rw[LESS_EQ_MONO_ADD_EQ] 
 >-- (qsuff_tac ‘Add(Add(a, d), Add(b', d')) = 
                Add(Add(a', d'), Add(b, d)) & 
                Add(Add(b, c), Add(b', d')) = 
                Add(Add(b', c'), Add(b, d))’
     >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
     >-- (qsspecl_then [‘Add(b',d')’,‘Add(a,d)’] 
          assume_tac $ GSYM Add_sym >> arw[] >>
          qsspecl_then [‘d'’,‘b'’] assume_tac $ GSYM Add_sym >> arw[] >>
          rw[Add_assoc] >>
          qsuff_tac ‘Add(Add(d', b'), a) = 
                     Add(Add(a', d'), b)’
          >-- (strip_tac >> arw[]) >>
          qsspecl_then [‘d'’,‘a'’] assume_tac $GSYM Add_sym >> arw[] >>
          rw[GSYM Add_assoc] >> 
          qsspecl_then [‘a’,‘b'’] assume_tac $GSYM Add_sym >> arw[] >>
          qsspecl_then [‘a'’,‘b’] assume_tac  Add_sym >> arw[]) >>
     qsspecl_then [‘Add(b',d')’,‘Add(b,c)’] assume_tac$GSYM Add_sym >>
     arw[] >> 
     qsspecl_then [‘c’,‘b’] assume_tac $GSYM Add_sym >> arw[] >>
     qsspecl_then [‘d’,‘b’] assume_tac $GSYM Add_sym >> arw[] >>
     rw[Add_assoc] >>
     qsuff_tac ‘Add(Add(b', d'), c) = Add(Add(b', c'), d)’ 
     >-- (strip_tac >> arw[]) >>
     rw[GSYM Add_assoc] >>
     qsspecl_then [‘c’,‘d'’] assume_tac $GSYM Add_sym >> arw[] >>
  qsspecl_then [‘c'’,‘d’] assume_tac $GSYM Add_sym >> arw[]) >>
 rw[LESS_EQ_MONO_ADD_EQ] 
 )
(form_goal “!a b c d a' b' c' d'. 
 ZR(Pa(a,b),Pa(a',b')) &
 ZR(Pa(c,d),Pa(c',d')) ==> 
(lej o Pa(Pa(a,b),Pa(c,d)) = TRUE <=>
lej o Pa(Pa(a',b'),Pa(c',d')) = TRUE)”));

val LEz_ex = prove_store("LEz_ex",
e0
(qexists_tac ‘lej o Pa(REP o p1(Z,Z),REP o p2(Z,Z))’ >>
 rw[o_assoc,Pa_distr,p12_of_Pa,rep_def])
(form_goal
 “?lez. !z1 z2. lez o Pa(z1,z2) = TRUE <=> 
 lej o Pa(rep(z1),rep(z2)) = TRUE”));

val LEz_def = LEz_ex |> ex2fsym0 "LEz" []
                     |> store_as "LEz_def";

val LEz_refl = prove_store("LEz_refl",
e0
(rw[LEz_def,lej_refl])
(form_goal
 “!z. LEz o Pa(z,z) = TRUE”));

val LEz_trans = prove_store("LEz_trans",
e0
(assume_tac lej_trans >>
 rw[LEz_def] >> rpt strip_tac >>
 qsspecl_then [‘rep(a1)’] assume_tac has_components >> 
 qsspecl_then [‘rep(a2)’] assume_tac has_components >>
 qsspecl_then [‘rep(a3)’] assume_tac has_components >>
 pop_assum_list (map_every strip_assume_tac) >>
 arw[] >> first_x_assum irule >> rfs[] >>
 qexists_tac ‘Pa(a',b')’ >> arw[])
(form_goal
 “!a1:1->Z a2 a3. LEz o Pa(a1,a2) = TRUE & LEz o Pa(a2,a3) = TRUE ==> 
 LEz o Pa(a1,a3) = TRUE”));

val LEz_asym = prove_store("LEz_asym",
e0
(rw[LEz_def] >> strip_tac >> strip_tac >>
 qsspecl_then [‘rep(a)’] assume_tac has_components >> 
 qsspecl_then [‘rep(b)’] assume_tac has_components >>
 pop_assum_list (map_every strip_assume_tac) >> arw[] >>
 rw[lej_def] >> rw[p12_of_Pa,Add_def] >> strip_tac >>
 once_rw[z_eq_cond] >>
 qexistsl_tac [‘Pa(a'',b'')’,‘Pa(a',b')’] >>
 rw[ZR_def] >> rw[Fst_Snd_Pa] >> rpt strip_tac (* 3 *)
 >-- (pop_assum_list (map_every (assume_tac o GSYM)) >>
      arw[rep_asz])
 >-- (pop_assum_list (map_every (assume_tac o GSYM)) >>
      arw[rep_asz]) >>
 irule Le_asym  >> 
 qsspecl_then [‘a''’,‘b'’] assume_tac $GSYM Add_sym >>fs[] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac $GSYM Add_sym >> fs[])
(form_goal
 “!a b. LEz o Pa(a,b) = TRUE & LEz o Pa(b,a) = TRUE ==> a = b”));



val LEz_total = prove_store("LEz_total",
e0
(rw[LEz_def,lej_def] >> rpt strip_tac >>
 qsspecl_then [‘rep(a)’] assume_tac has_components >> 
 qsspecl_then [‘rep(b)’] assume_tac has_components >>
 pop_assum_list (map_every strip_assume_tac) >> 
 arw[p12_of_Pa] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac $GSYM Add_sym >> arw[] >>
 qsspecl_then [‘a''’,‘b'’] assume_tac $GSYM Add_sym >> arw[] >>
 arw[Add_def] >> rw[Le_def1] >>
 rw[LESS_EQ_cases] )
(form_goal “!a:1->Z b. LEz o Pa(a,b) = TRUE | LEz o Pa(b,a) = TRUE”));


val Z = mk_fun "Z" []

val _ = new_pred "Lez" [("z1",ar_sort (mk_ob "X") Z),
                        ("z2",ar_sort (mk_ob "X") Z)]

val Lez_def0 = store_ax("Lez_def0",
“!X z1:X->Z z2.Lez(z1,z2) <=> LEz o Pa(z1,z2) = True(X)”);

val Lez_def = Lez_def0 |> allE (rastt "1")
                       |> rewr_rule[True1TRUE]
                       |> store_as "Lez_def";


val J2_iv' = prove_store("J2_iv'",
e0
(rpt strip_tac >> 
 qsspecl_then [‘ab’] assume_tac has_components >>
 qsspecl_then [‘ab'’] assume_tac has_components >>
 qsspecl_then [‘cd’] assume_tac has_components >>
 qsspecl_then [‘cd'’] assume_tac has_components >>
 pop_assum_list (map_every strip_assume_tac) >> rfs[] >>
 irule J2_iv >> arw[])  
(form_goal
 “!ab cd ab' cd'. ZR(ab,ab') & ZR(cd,cd') ==> 
 (lej o Pa(ab,cd) = TRUE <=> lej o Pa(ab',cd') = TRUE)”));





val Z2_x = prove_store("Z2_x",
e0
(rw[Lez_def,Addz_eqn',Addj_property,LEz_def] >>
 rpt strip_tac >>
 qsuff_tac 
 ‘lej o Pa(Pa(a, b),Pa(c, d)) = TRUE ==> 
  lej o Pa (Pa(Add(a, e), Add(b, f)),
            Pa(Add(c, e), Add(d, f))) = TRUE’ >--
 (rpt strip_tac >>
 qby_tac ‘lej o Pa(Pa(a, b), Pa(c, d)) = TRUE’
 >-- (irule $ iffLR J2_iv' >>
      qexistsl_tac 
      [‘rep(asz(Pa(a, b)))’,‘rep(asz(Pa(c, d)))’]>>
      arw[] >> rw[GSYM rep_rel_all]) >>
 first_x_assum drule >> 
 irule $ iffLR J2_iv' >>
 qexistsl_tac
 [‘Pa(Add(a, e), Add(b, f))’,‘Pa(Add(c, e), Add(d, f))’] >>
 arw[] >> once_rw[ZR_sym] >> rw[GSYM rep_rel_all]) >>
 pop_assum (K all_tac) >>
 rw[lej_property] >> rpt strip_tac >>
 qsspecl_then [‘Add(d,f)’,‘Add(a,e)’] assume_tac $ GSYM Add_sym >>
 arw[] >> rw[Add_assoc] >> rw[LESS_EQ_MONO_ADD_EQ] >>
 once_rw[Add_sym] >> rw[Add_assoc] >>
 rw[LESS_EQ_MONO_ADD_EQ] >> 
 qsspecl_then [‘c’,‘b’] assume_tac$ GSYM Add_sym >> fs[]
 )
(form_goal “!a:1->N b c d e f.Lez(asz(Pa(a,b)),asz(Pa(c,d))) ==>
            Lez(Addz(asz(Pa(a,b)),asz(Pa(e,f))),
                Addz(asz(Pa(c,d)),asz(Pa(e,f))))”));



val oj_ex = prove_store("oj_ex",
e0
(qexists_tac ‘Pa(Suc(O),O)’ >> rw[])
(form_goal
 “?oj.Pa(Suc(O),O) = oj”));

val oj_def = oj_ex |> ex2fsym0 "1j" []
                   |> store_as "oj_def";

val Mulj_property = prove_store("Mulj_property",
e0
(rpt strip_tac >>
 rw[GSYM Mulj_def,GSYM MULj_def] >>
 once_rw[GSYM Mul_def] >> once_rw[GSYM Add_def] >>
 rw[o_assoc,Pa_distr,p12_of_Pa])
(form_goal
 “!a:1->N b c d.
 Mulj(Pa(a,b),Pa(c,d)) = 
 Pa(Add(Mul(a,c),Mul(b,d)), Add(Mul(a,d),Mul(b,c)))”));

val J1_v = prove_store("J1_v",
e0
(rpt strip_tac >> rw[ZR_def,Mulj_property] >>
 rw[Fst_Snd_Pa] >> rw[LEFT_DISTR] >>
 rw[RIGHT_DISTR] >> 
 rw[GSYM Add_assoc] >>
 qsspecl_then 
 [‘Mul(Mul(a, c), f)’,
  ‘Add(Mul(Mul(b, d), f),
                 Add(Mul(Mul(a, d), e),
                  Add(Mul(Mul(b, c), e),
                   Add(Mul(a, Mul(c, e)),
                    Add(Mul(a, Mul(d, f)),
                     Add(Mul(b, Mul(c, f)), Mul(b, Mul(d, e))))))))’]
 assume_tac Add_sym >> arw[] >>
 qsspecl_then 
 [‘Mul(Mul(b, d), f)’,
  ‘Add(Mul(Mul(a, d), e),
                  Add(Mul(Mul(b, c), e),
                   Add(Mul(a, Mul(c, e)),
                    Add(Mul(a, Mul(d, f)),
                     Add(Mul(b, Mul(c, f)), Mul(b, Mul(d, e)))))))’]
 assume_tac Add_sym >> arw[] >> rw[GSYM Add_assoc] >>
 qsspecl_then 
 [‘Mul(Mul(a, d), e)’,
  ‘Add(Mul(Mul(b, c), e),
                 Add(Mul(a, Mul(c, e)),
                  Add(Mul(a, Mul(d, f)),
                   Add(Mul(b, Mul(c, f)),
                    Add(Mul(b, Mul(d, e)),
                     Add(Mul(Mul(b, d), f), Mul(Mul(a, c), f)))))))’]
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >>
 qsspecl_then 
 [‘Mul(Mul(b, c), e)’,
  ‘ Add(Mul(a, Mul(c, e)),
                 Add(Mul(a, Mul(d, f)),
                  Add(Mul(b, Mul(c, f)),
                   Add(Mul(b, Mul(d, e)),
                    Add(Mul(Mul(b, d), f),
                     Add(Mul(Mul(a, c), f), Mul(Mul(a, d), e)))))))’]
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(Mul(b, d), e),
                 Add(Mul(Mul(a, d), f),
                  Add(Mul(Mul(b, c), f),
                   Add(Mul(a, Mul(c, f)),
                    Add(Mul(a, Mul(d, e)),
                     Add(Mul(b, Mul(c, e)), Mul(b, Mul(d, f)))))))) = 
 Add(Mul(a, Mul(d, f)),
                 Add(Mul(b, Mul(c, f)),
                  Add(Mul(b, Mul(d, e)),
                   Add(Mul(Mul(b, d), f),
                    Add(Mul(Mul(a, c), f),
                     Add(Mul(Mul(a, d), e), Mul(Mul(b, c), e)))))))’
 >-- (strip_tac >> arw[] >> rw[GSYM Mul_assoc]) >>
 qsspecl_then
 [‘Mul(Mul(b, d), e)’,
  ‘Add(Mul(Mul(a, d), f),
                 Add(Mul(Mul(b, c), f),
                  Add(Mul(a, Mul(c, f)),
                   Add(Mul(a, Mul(d, e)),
                    Add(Mul(b, Mul(c, e)), Mul(b, Mul(d, f)))))))’]
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Mul_assoc] >> rw[GSYM Add_assoc] >> 
 qsuff_tac
 ‘Add(Mul(b, Mul(c, f)),
                 Add(Mul(a, Mul(c, f)),
                  Add(Mul(a, Mul(d, e)),
                   Add(Mul(b, Mul(c, e)),
                    Add(Mul(b, Mul(d, f)), Mul(b, Mul(d, e))))))) = 
 Add(Mul(b, Mul(c, f)),
                 Add(Mul(b, Mul(d, e)),
                  Add(Mul(b, Mul(d, f)),
                   Add(Mul(a, Mul(c, f)),
                    Add(Mul(a, Mul(d, e)), Mul(b, Mul(c, e)))))))’
 >-- (strip_tac >> arw[]) >>
 qsuff_tac ‘Add(Mul(a, Mul(c, f)),
                 Add(Mul(a, Mul(d, e)),
                  Add(Mul(b, Mul(c, e)),
                   Add(Mul(b, Mul(d, f)), Mul(b, Mul(d, e)))))) = 
 Add(Mul(b, Mul(d, e)),
                 Add(Mul(b, Mul(d, f)),
                  Add(Mul(a, Mul(c, f)),
                   Add(Mul(a, Mul(d, e)), Mul(b, Mul(c, e))))))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then 
 [‘Mul(b, Mul(d, e))’,
  ‘Add(Mul(b, Mul(d, f)),
                 Add(Mul(a, Mul(c, f)),
                  Add(Mul(a, Mul(d, e)), Mul(b, Mul(c, e)))))’]
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >>
 qsspecl_then [‘Mul(b, Mul(d, f))’,
 ‘Add(Mul(a, Mul(c, f)),
                 Add(Mul(a, Mul(d, e)),
                  Add(Mul(b, Mul(c, e)), Mul(b, Mul(d, e)))))’]
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >>
 qsspecl_then [‘Mul(b, Mul(d, f))’,‘Mul(b, Mul(d, e))’]
 assume_tac Add_sym >> arw[]
 )
(form_goal “!a:1->N b c d e f. ZR(Mulj(Mulj(Pa(a,b),Pa(c,d)),Pa(e,f)), 
                             Mulj(Pa(a,b),Mulj(Pa(c,d),Pa(e,f))))”));

val J2_iii = prove_store("J2_iii",
e0
(rw[ZR_def,Mulj_property] >>
 rw[Fst_Snd_Pa] >> rpt strip_tac >>
 rw[] >>
 abbrev_tac 
 “Add(Mul(p:1->N,c),Add(Mul(q,c),Add(Mul(p,d),Mul(q,d)))) = l” >>
 qsuff_tac 
 ‘Add(Add(Add(Mul(a, c), Mul(b, d)), Add(Mul(p, s), Mul(q, r))),l) = 
  Add(Add(Add(Mul(a, d), Mul(b, c)), Add(Mul(p, r), Mul(q, s))),l)’ 
 >-- rw[EQ_MONO_ADD_EQ] >>
 qsuff_tac
 ‘Add(Add(Add(Mul(a, c), Mul(b, d)), Add(Mul(p, s), Mul(q, r))), l) = 
  Add(Mul(Add(a,q),c),
      Add(Mul(Add(b,p),d),
          Add(Mul(p,Add(c,s)),Mul(q,Add(d,r))))) & 
 Add(Add(Add(Mul(a, d), Mul(b, c)), Add(Mul(p, r), Mul(q, s))), l) = 
  Add(Mul(Add(b,p),c),
      Add(Mul(Add(a,q),d),
          Add(Mul(p,Add(d,r)),Mul(q,Add(c,s))))) &
  Add(Mul(Add(a,q),c),
      Add(Mul(Add(b,p),d),
          Add(Mul(p,Add(c,s)),Mul(q,Add(d,r))))) = 
  Add(Mul(Add(b,p),c),
      Add(Mul(Add(a,q),d),
          Add(Mul(p,Add(d,r)),Mul(q,Add(c,s)))))’
 >-- (strip_tac >> arw[]) >>
 rpt strip_tac
 >-- (pop_assum mp_tac >>
     pop_assum_list (map_every (K all_tac)) >>
     strip_tac >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[GSYM Add_assoc,RIGHT_DISTR,LEFT_DISTR] >>
     qsuff_tac
     ‘Add(Mul(b, d),
                 Add(Mul(p, s),
                  Add(Mul(q, r),
                   Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d))))))) = 
     Add(Mul(q, c),
                 Add(Mul(b, d),
                  Add(Mul(p, d),
                   Add(Mul(p, c), Add(Mul(p, s), Add(Mul(q, d), Mul(q, r)))))))’
     >-- (strip_tac >> arw[]) >>
     qsspecl_then 
     [‘Mul(q,c)’,
     ‘Add(Mul(b, d),
                 Add(Mul(p, d),
                  Add(Mul(p, c), Add(Mul(p, s), Add(Mul(q, d), Mul(q, r))))))’] assume_tac Add_sym >>
     arw[GSYM Add_assoc] >>
     qsuff_tac
     ‘Add(Mul(p, s),
                 Add(Mul(q, r),
                  Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))))) = 
      Add(Mul(p, d),
                 Add(Mul(p, c),
                  Add(Mul(p, s), Add(Mul(q, d), Add(Mul(q, r), Mul(q, c))))))’
     >-- (strip_tac >> arw[]) >>
     qsspecl_then [‘Mul(p,d)’,
     ‘Add(Mul(p, c),
      Add(Mul(p, s), Add(Mul(q, d), Add(Mul(q, r), Mul(q, c)))))’] assume_tac Add_sym >> arw[] >>
     rw[GSYM Add_assoc] >>
     qsspecl_then 
     [‘Mul(p,c)’,
      ‘Add(Mul(p, s),
                 Add(Mul(q, d), Add(Mul(q, r), Add(Mul(q, c), Mul(p, d)))))’] assume_tac Add_sym >>
     arw[GSYM Add_assoc] >>
     qsuff_tac 
     ‘Add(Mul(q, r),
                 Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d))))) = 
      Add(Mul(q, d),
                 Add(Mul(q, r), Add(Mul(q, c), Add(Mul(p, d), Mul(p, c)))))’
     >-- (strip_tac >> arw[]) >>
     qsspecl_then [‘Mul(q,d)’,
     ‘Add(Mul(q, r), Add(Mul(q, c), Add(Mul(p, d), Mul(p, c))))’] assume_tac Add_sym >> arw[GSYM Add_assoc] >>
     qsuff_tac
     ‘Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))) = Add(Mul(q, c), Add(Mul(p, d), Add(Mul(p, c), Mul(q, d))))’ >-- (strip_tac >> arw[]) >>
     qsspecl_then [‘Mul(p, c)’,‘Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))’] assume_tac Add_sym >> 
     arw[GSYM Add_assoc] >>
     qsspecl_then [‘Mul(q,d)’,‘Mul(p,c)’]
     assume_tac Add_sym >> arw[]) 
>-- (
pop_assum (mp_tac o GSYM) >> 
pop_assum_list (map_every (K all_tac)) >>
strip_tac >> arw[] >>
pop_assum (K all_tac) >>
rw[GSYM Add_assoc,LEFT_DISTR,RIGHT_DISTR] >> 
qsspecl_then [‘Mul(a,d)’,
‘Add(Mul(b, c),
                 Add(Mul(p, r),
                  Add(Mul(q, s),
                   Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))))))’] assume_tac Add_sym >>
arw[GSYM Add_assoc] >>
qsuff_tac
‘Add(Mul(p, r),
                 Add(Mul(q, s),
                  Add(Mul(p, c),
                   Add(Mul(q, c), Add(Mul(p, d), Add(Mul(q, d), Mul(a, d))))))) = 
 Add(Mul(p, c),
                 Add(Mul(a, d),
                  Add(Mul(q, d),
                   Add(Mul(p, d), Add(Mul(p, r), Add(Mul(q, c), Mul(q, s)))))))’
>-- (strip_tac >> arw[]) >>
qsspecl_then [‘Mul(p, r)’,
‘Add(Mul(q, s),
                 Add(Mul(p, c),
                  Add(Mul(q, c), Add(Mul(p, d), Add(Mul(q, d), Mul(a, d))))))’] assume_tac Add_sym >>
arw[GSYM Add_assoc] >>
qsspecl_then [‘Mul(q, s)’,
‘Add(Mul(p, c),
                 Add(Mul(q, c),
                  Add(Mul(p, d), Add(Mul(q, d), Add(Mul(a, d), Mul(p, r))))))’] assume_tac Add_sym >>
arw[GSYM Add_assoc] >>
qsuff_tac
‘Add(Mul(q, c),
                 Add(Mul(p, d),
                  Add(Mul(q, d), Add(Mul(a, d), Add(Mul(p, r), Mul(q, s)))))) =
 Add(Mul(a, d),
                 Add(Mul(q, d),
                  Add(Mul(p, d), Add(Mul(p, r), Add(Mul(q, c), Mul(q, s))))))’
>-- (strip_tac >> arw[]) >>
rw[Add_assoc] >> 
qsspecl_then
[‘Add(Add(Add(Add(Mul(a, d), Mul(q, d)), Mul(p, d)),
                  Mul(p, r)), Mul(q, c))’,‘Mul(q,s)’]
assume_tac Add_sym >> arw[] >>
rw[Add_assoc] >>
qsspecl_then 
[‘Add(Add(Add(Add(Mul(q, s), Mul(a, d)), Mul(q, d)),
                  Mul(p, d)), Mul(p, r))’,‘Mul(q,c)’]
assume_tac Add_sym >> arw[] >>
rw[GSYM Add_assoc] >>
qsuff_tac
 ‘Add(Mul(p, d),
                 Add(Mul(q, d), Add(Mul(a, d), Add(Mul(p, r), Mul(q, s))))) = 
 Add(Mul(q, s),
                 Add(Mul(a, d), Add(Mul(q, d), Add(Mul(p, d), Mul(p, r)))))’
>-- (strip_tac >> arw[]) >>
rw[Add_assoc] >>
qsspecl_then
[‘Add(Add(Add(Mul(p, d), Mul(q, d)), Mul(a, d)), Mul(p, r))’,‘Mul(q,s)’] assume_tac Add_sym >> arw[GSYM Add_assoc] >>
qsuff_tac
‘Add(Mul(p, d), Add(Mul(q, d), Add(Mul(a, d), Mul(p, r))))=
Add(Mul(a, d), Add(Mul(q, d), Add(Mul(p, d), Mul(p, r))))’
>-- (strip_tac >> arw[]) >>
qsspecl_then
[‘Mul(p, d)’,
 ‘Add(Mul(q, d), Add(Mul(a, d), Mul(p, r)))’]
assume_tac Add_sym >>
arw[GSYM Add_assoc] >>
qsspecl_then
[‘Mul(q, d)’,
 ‘Add(Mul(a, d), Add(Mul(p, r), Mul(p, d)))’]
assume_tac Add_sym >>
arw[GSYM Add_assoc] >>
qsuff_tac
‘Add(Mul(p, r), Add(Mul(p, d), Mul(q, d))) = 
 Add(Mul(q, d), Add(Mul(p, d), Mul(p, r)))’
>-- (strip_tac >> arw[]) >>
qsspecl_then
[‘Mul(p, r)’,‘Add(Mul(p, d), Mul(q, d))’]
assume_tac Add_sym >> arw[Add_assoc] >> 
qsspecl_then [‘Mul(p,d)’,‘Mul(q,d)’] assume_tac Add_sym >>
arw[]
 )>>
 arw[])
(form_goal
“!a:1->N b p q c d r s. ZR(Pa(a,b),Pa(p,q)) & 
ZR(Pa(c,d),Pa(r,s)) ==> 
 ZR(Mulj(Pa(a,b),Pa(c,d)),Mulj(Pa(p,q),Pa(r,s)))”));

val J2_iii' = prove_store("J2_iii'",
e0
(rpt strip_tac >>
 qsspecl_then [‘ab’] strip_assume_tac has_components >>
 qsspecl_then [‘pq’] strip_assume_tac has_components >>
 qsspecl_then [‘cd’] strip_assume_tac has_components >>
 qsspecl_then [‘rs’] strip_assume_tac has_components >> fs[] >>
 irule J2_iii >> arw[])
(form_goal
 “!ab:1->N * N pq cd rs. ZR(ab,pq) & ZR(cd,rs) ==>
 ZR(Mulj(ab,cd),Mulj(pq,rs))”));




val MULz_ex = prove_store("MULz_ex",
e0
(qexists_tac ‘toZ o MULj o Pa(REP o p1(Z,Z),REP o p2(Z,Z))’ >>
 rw[])
(form_goal
 “?mulz. toZ o MULj o Pa(REP o p1(Z,Z),REP o p2(Z,Z)) = mulz”));



val MULz_def = MULz_ex |> ex2fsym0 "MULz" []
                       |> store_as "MULz_def";




val Mulz_ex = prove_store("Mulz_ex",
e0
(rpt strip_tac >> qexists_tac ‘MULz o Pa(z1,z2)’ >> rw[])
(form_goal
 “!X z1:X->Z z2. ?z12. MULz o Pa(z1,z2) = z12”));

val Mulz_def = Mulz_ex |> spec_all |> ex2fsym0 "Mulz" ["z1","z2"]
                       |> gen_all |> store_as "Mulz_def";


val Mulz_eqn = prove_store("Mulz_eqn",
e0
(assume_tac J2_iii >>
 rpt strip_tac >>
 rw[GSYM Mulz_def,GSYM MULz_def] >>
 rw[asz_def,rep_def,Mulj_def,Pa_distr,p12_of_Pa,o_assoc] >>
 once_rw[samez_cond] >>
 qsspecl_then [‘rep(asz(Pa(a, b)))’] strip_assume_tac has_components >>
 qsspecl_then [‘rep(asz(Pa(c, d)))’] strip_assume_tac has_components >>
 arw[] >>
 first_x_assum irule >>
 pop_assum_list (map_every (assume_tac o GSYM)) >> arw[] >>
 rw[GSYM rep_rel_all])
(form_goal
“!a:1->N b c d. Mulz(asz(Pa(a,b)),asz(Pa(c,d))) = 
 asz(Mulj(Pa(a,b),Pa(c,d)))”));

val Z2_v = prove_store("Z2_v",
e0
(rpt strip_tac >> rw[Mulz_eqn] >> 
 rw[GSYM Mulz_def] >> rw[GSYM MULz_def] >>
 rw[Mulj_def,rep_def,asz_def,o_assoc,Pa_distr,p12_of_Pa] >>
 assume_tac J1_v >>
 rw[samez_cond] >> once_rw[ZR_cond] >>
 qexistsl_tac 
[‘Mulj(Mulj(Pa(a,b),Pa(c,d)),Pa(e,f))’,
 ‘Mulj(Pa(a,b),Mulj(Pa(c,d),Pa(e,f)))’] >> arw[] >> strip_tac (* 2 *)
 >--(assume_tac J2_iii >> 
 qsspecl_then [‘rep(asz(Mulj(Pa(a, b), Pa(c, d))))’]
 strip_assume_tac has_components >>
 qsspecl_then [‘rep(asz(Pa(e, f)))’] 
 strip_assume_tac has_components >> arw[] >>
 qsspecl_then [‘Mulj(Pa(a, b), Pa(c, d))’] 
 strip_assume_tac has_components >> arw[] >>
 first_x_assum irule >>
 pop_assum_list (map_every (assume_tac o GSYM)) >>
 arw[GSYM rep_rel_all]) >>
 assume_tac J2_iii >>
 qsspecl_then [‘rep(asz(Pa(a, b)))’]
 strip_assume_tac has_components >>
 qsspecl_then [‘rep(asz(Mulj(Pa(c, d), Pa(e, f))))’]
 strip_assume_tac has_components >> 
 qsspecl_then [‘Mulj(Pa(c, d), Pa(e, f))’]
 strip_assume_tac has_components >>
 arw[] >> first_x_assum irule >> 
 pop_assum_list (map_every (assume_tac o GSYM)) >> arw[GSYM rep_rel_all]
 )
(form_goal
 “!a:1->N b c d e f.Mulz(Mulz(asz(Pa(a,b)),asz(Pa(c,d))),asz(Pa(e,f))) = 
 Mulz(asz(Pa(a,b)),Mulz(asz(Pa(c,d)),asz(Pa(e,f))))”));


val J1_vi = prove_store("J1_vi",
e0
(rw[ZR_def] >> rpt strip_tac >>
 rw[Mulj_property] >> rw[Addj_property] >>
 rw[Fst_Snd_Pa] >> rw[Mulj_property] >> rw[Fst_Snd_Pa] >>
 rw[RIGHT_DISTR,LEFT_DISTR,GSYM Add_assoc] >> 
 qsspecl_then 
 [‘Mul(a, c)’,
  ‘Add(Mul(a, e),
                 Add(Mul(b, d),
                  Add(Mul(b, f),
                   Add(Mul(a, d), Add(Mul(b, c), Add(Mul(a, f), Mul(b, e)))))))’] assume_tac Add_sym >> arw[GSYM Add_assoc] >>
 qsspecl_then 
 [‘Mul(a, e)’,
  ‘Add(Mul(b, d),
                 Add(Mul(b, f),
                  Add(Mul(a, d),
                   Add(Mul(b, c), Add(Mul(a, f), Add(Mul(b, e), Mul(a, c)))))))’] assume_tac Add_sym >> arw[GSYM Add_assoc] >>
 qsspecl_then
 [‘Mul(b, d)’,
  ‘Add(Mul(b, f),
                 Add(Mul(a, d),
                  Add(Mul(b, c),
                   Add(Mul(a, f), Add(Mul(b, e), Add(Mul(a, c), Mul(a, e)))))))’] assume_tac Add_sym >> arw[GSYM Add_assoc] >>
 qsspecl_then
 [‘Mul(b, f)’,
  ‘Add(Mul(a, d),
                 Add(Mul(b, c),
                  Add(Mul(a, f),
                   Add(Mul(b, e), Add(Mul(a, c), Add(Mul(a, e), Mul(b, d)))))))’] assume_tac Add_sym >> arw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(b, c),
                 Add(Mul(a, f),
                  Add(Mul(b, e),
                   Add(Mul(a, c), Add(Mul(a, e), Add(Mul(b, d), Mul(b, f))))))) = 
 Add(Mul(a, f),
                 Add(Mul(b, c),
                  Add(Mul(b, e),
                   Add(Mul(a, c), Add(Mul(b, d), Add(Mul(a, e), Mul(b, f)))))))’ >-- (strip_tac >> arw[]) >>
 qsspecl_then
 [‘Mul(b, c)’,
 ‘Add(Mul(a, f),
                 Add(Mul(b, e),
                  Add(Mul(a, c), Add(Mul(a, e), Add(Mul(b, d), Mul(b, f))))))’] assume_tac Add_sym >> arw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(b, e),
                 Add(Mul(a, c),
                  Add(Mul(a, e), Add(Mul(b, d), Add(Mul(b, f), Mul(b, c)))))) = Add(Mul(b, c),
                 Add(Mul(b, e),
                  Add(Mul(a, c), Add(Mul(b, d), Add(Mul(a, e), Mul(b, f))))))’ >-- (strip_tac >> arw[]) >>
 qsspecl_then 
 [‘Mul(b, c)’,
  ‘Add(Mul(b, e),
                 Add(Mul(a, c), Add(Mul(b, d), Add(Mul(a, e), Mul(b, f)))))’] assume_tac Add_sym >> arw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(a, e), Add(Mul(b, d), Add(Mul(b, f), Mul(b, c)))) = 
  Add(Mul(b, d), Add(Mul(a, e), Add(Mul(b, f), Mul(b, c))))’
 >-- (strip_tac >> arw[]) >>
 rw[Add_assoc] >>
 qsspecl_then
 [‘Mul(a, e)’,‘Mul(b, d)’] assume_tac Add_sym >>
 arw[]
 (*tedious...*))
(form_goal
 “!a:1->N b c d e f.
ZR(Mulj(Pa(a, b), Addj(Pa(c, d), Pa(e, f))),
              Addj(Mulj(Pa(a, b), Pa(c, d)), Mulj(Pa(a, b), Pa(e, f))))”));




val Z2_vi = prove_store("Z2_vi",
e0
(rpt strip_tac >> rw[Mulz_eqn] >>
 rw[Addz_eqn'] >> 
rw[GSYM Mulz_def] >> rw[GSYM MULz_def] >>
 rw[Mulj_def,rep_def,asz_def,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[GSYM Addz_def] >> rw[GSYM ADDz_def] >>
 rw[Addj_def,rep_def,asz_def,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[samez_cond] >> once_rw[ZR_cond] >>
 qexistsl_tac [‘Mulj(Pa(a,b),Addj(Pa(c,d),Pa(e,f)))’,
               ‘Addj(Mulj(Pa(a,b),Pa(c,d)),
                     Mulj(Pa(a,b),Pa(e,f)))’] >>
 rpt strip_tac (* 3 *)
 >-- (irule J2_iii' >> rw[GSYM rep_rel_all]) 
 >-- (irule J2_i' >> rw[GSYM rep_rel_all]) >>
 rw[J1_vi]
 )
(form_goal
 “!a:1->N b c d e f. 
  Mulz(asz(Pa(a,b)),Addz(asz(Pa(c,d)),asz(Pa(e,f)))) = 
  Addz(Mulz(asz(Pa(a,b)),asz(Pa(c,d))),
       Mulz(asz(Pa(a,b)),asz(Pa(e,f))))”));




val J1_vii = prove_store("J1_vii",
e0
(rw[ZR_def] >> rpt strip_tac >>
 rw[GSYM oj_def,Mulj_property] >> rw[Fst_Snd_Pa] >>
 rw[Mul_clauses',Add_O,Add_O2] >>
 qsspecl_then [‘a’,‘b’] accept_tac Add_sym)
(form_goal
 “!a:1->N b.ZR(Mulj(Pa(a, b),1j),Pa(a,b))”));

val Z2_vii = prove_store("Z2_vii",
e0
(rpt strip_tac >> rw[GSYM Mulz_def,GSYM MULz_def,o_assoc,p12_of_Pa,Pa_distr] >> rw[Mulj_def,rep_def,asz_def] >>
 rw[samez_cond] >> once_rw[ZR_cond] >>
 qexistsl_tac [‘Mulj(Pa(a,b),1j)’,‘Pa(a,b)’] >>
 rw[ZR_refl,J1_vii] >> 
 irule J2_iii' >> rw[GSYM rep_rel_all])
(form_goal “!a b. Mulz(asz(Pa(a,b)),asz(1j)) = asz(Pa(a,b))”));

val J1_viii = prove_store("J1_vii",
e0
(rw[ZR_def] >> rpt strip_tac >>
 rw[Mulj_property] >> rw[Fst_Snd_Pa] >>
 qsspecl_then [‘a’,‘c’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘b’,‘d’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘a’,‘d’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘b’,‘c’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘Add(Mul(c, a), Mul(d, b))’,‘Add(Mul(d, a), Mul(c, b))’]
 assume_tac $ GSYM Add_sym >> arw[] >>
 qsspecl_then [‘Mul(d,a)’,‘Mul(c,b)’] assume_tac Add_sym >>
 arw[])
(form_goal
 “!a:1->N b c d.ZR(Mulj(Pa(a, b),Pa(c,d)),Mulj(Pa(c,d),Pa(a,b)))”));

val Z2_viii = prove_store("Z2_viii",
e0
(rpt strip_tac >> rw[GSYM Mulz_def,GSYM MULz_def,o_assoc,p12_of_Pa,
Pa_distr] >>
 rw[rep_def,asz_def,Mulj_def] >> rw[samez_cond] >>
 once_rw[ZR_cond] >>
 qexistsl_tac [‘Mulj(Pa(a, b),Pa(c,d))’,‘Mulj(Pa(c,d),Pa(a,b))’]
 >> rw[J1_viii] >> strip_tac >> irule J2_iii' >>
 rw[GSYM rep_rel_all] )
(form_goal
 “!a:1->N b c d.Mulz(asz(Pa(a,b)),asz(Pa(c,d))) = 
                Mulz(asz(Pa(c,d)),asz(Pa(a,b)))”));

val Le_MONO = LESS_EQ_MONO |> rewr_rule[GSYM Le_def1,Suc_def]
                           |> store_as "Le_MONO";

val Le_O = ZERO_LESS_EQ |> rewr_rule[GSYM Le_def1]
                        |> store_as "Le_O";


val Sub_Suc1 = prove_store("Sub_Suc1",
e0
(qby_tac
 ‘?P. !a. (!b. Le(b,a) ==> Sub(Suc(a),b) = Suc(Sub(a,b))) <=>
      P o a = TRUE’ 
 >-- (qexists_tac ‘ALL(Imp(Char(LE),Eq(N) o Pa(SUB o Pa(SUC o p2(N,N),p1(N,N)), SUC o SUB o Swap(N,N))))’ >>
      rw[ALL_property] >> rpt strip_tac >>
      rw[GSYM Imp_def,IMP_def,o_assoc,Pa_distr,p12_of_Pa,Swap_Pa,
          Eq_property_TRUE] >> rw[GSYM Le_def1,Sub_def,Suc_def] ) >>
 pop_assum strip_assume_tac >> arw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Le_O_iff,Sub_of_O] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> arw[Sub_O]) >>
 strip_tac >> strip_tac >> rw[Suc_def] >>
 qby_tac
 ‘?P1. !b. (Le(b, Suc(n)) ==> Sub(Suc(Suc(n)), b) = Suc(Sub(Suc(n), b))) <=> P1 o b = TRUE’ 
 >-- (qexists_tac ‘Imp(Char(LE) o Pa(id(N),Suc(n) o To1(N)),
                       EQ(Sub(Suc(Suc(n)) o To1(N),id(N)),Suc(Sub(Suc(n) o To1(N),id(N)))))’ >> strip_tac >>
      rw[GSYM Suc_def,GSYM Sub_def,GSYM Imp_def,IMP_def,
         o_assoc,Pa_distr,p12_of_Pa,GSYM EQ_def,
         Eq_property_TRUE] >>
      once_rw[one_to_one_id] >> rw[idL,idR] >> 
      rw[GSYM Le_def1]) >>
 pop_assum strip_assume_tac >>
 arw[IP_el] >> pop_assum (assume_tac o GSYM) >>
 arw[] >> rw[Le_O,Sub_O] >> strip_tac >>
 rw[Suc_def] >> arw[] >>
 rw[Le_MONO] >> rw[Sub_Suc] >> rpt strip_tac >>
 qby_tac ‘Le(n',Suc(n))’ 
 >-- (irule Le_trans >> qexists_tac ‘n’ >> arw[] >>
     assume_tac Lt_Suc >> fs[Lt_def]) >>
 first_x_assum drule >> arw[] >>
 last_x_assum drule >> arw[] >> rw[Pre_Suc])
(form_goal
 “!a:1->N b. Le(b,a) ==> Sub(Suc(a),b) = Suc(Sub(a,b))”));


val SUB_ADD = prove_store("SUB_ADD",
e0
(qby_tac
 ‘?P. !m. (!n. Le(n,m) ==> Add(Sub(m,n),n) = m) <=> P o m = TRUE’  
 >-- (qexists_tac ‘ALL(Imp(Char(LE),EQ(Add(SUB o Swap(N,N),p1(N,N)),p2(N,N))))’ >>strip_tac >>
     rw[ALL_property,GSYM Imp_def,IMP_def,p12_of_Pa,GSYM Add_def,o_assoc,
       Pa_distr,GSYM EQ_def,Eq_property_TRUE,Swap_Pa,GSYM Le_def1,
       GSYM Sub_def] ) >>
 pop_assum strip_assume_tac >> arw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Sub_of_O,Add_O2,Le_O_iff] >> strip_tac >>
 strip_tac >> rw[Suc_def] >>
 qby_tac
 ‘?P1. !n'.(Le(n', Suc(n)) ==> Add(Sub(Suc(n), n'), n') = Suc(n)) <=>
  P1 o n' = TRUE’ >-- 
 (qexists_tac ‘Imp(Char(LE) o Pa(id(N),Suc(n) o To1(N)),
       EQ(Add(Sub(Suc(n) o To1(N),id(N)),id(N)),Suc(n) o To1(N)))’ >>
 strip_tac >>
  rw[GSYM Imp_def,IMP_def,p12_of_Pa,GSYM Add_def,o_assoc,
       Pa_distr,GSYM EQ_def,Eq_property_TRUE,Swap_Pa,GSYM Le_def1,
       GSYM Sub_def] >>
  once_rw[one_to_one_id] >> rw[idL,idR]) >>
 pop_assum strip_assume_tac >> arw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 rw[Sub_O,Add_Suc1,Add_O] >> strip_tac >> arw[] >>
 rw[Suc_def] >> rw[Sub_mono_eq] >> rw[Add_Suc] >> 
 rw[Suc_eq_eq] >> rw[Le_MONO] >> 
 rpt strip_tac >> 
 qby_tac ‘Le(n',Suc(n))’ 
 >-- (irule Le_trans >> qexists_tac ‘n’ >> arw[] >>
     assume_tac Lt_Suc >> fs[Lt_def]) >>
 first_x_assum drule >> rev_drule Sub_Suc1 >> fs[] >> 
 first_x_assum irule >> arw[])
(form_goal “!m:1->N n. Le(n,m) ==> Add(Sub(m,n),n) = m”));


val ADD_EQ_SUB = prove_store("ADD_EQ_SUB",
e0
(strip_tac >>
 qby_tac ‘?P.!n.(!p. Le(n,p) ==> (Add(m,n) = p <=> m = Sub(p,n))) <=> P o n = TRUE’ >-- 
 (qexists_tac ‘ALL(Imp(Char(LE) o Swap(N,N),
                   Iff(EQ(Add(m o To1(N * N),p2(N,N)),p1(N,N)),
                       EQ(m o To1(N * N),SUB))))’ >>
 strip_tac >>
 rw[ALL_property,GSYM Imp_def,IMP_def,GSYM Iff_def,IFF_def,p12_of_Pa,GSYM Add_def,o_assoc,
       Pa_distr,GSYM EQ_def,Eq_property_TRUE,Swap_Pa,GSYM Le_def1,
       GSYM Sub_def] >>
 once_rw[one_to_one_id] >> rw[idL,idR]) >>
 pop_assum strip_assume_tac >>
 arw[IP_el,Suc_def] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Le_O_iff,Add_O,Sub_O] >> strip_tac >> strip_tac >>
 qby_tac ‘?P1. !p.(Le(Suc(n), p) ==>
               (Add(m, Suc(n)) = p <=> m = Sub(p, Suc(n)))) <=> P1 o p = TRUE’ >--
 (qexists_tac ‘Imp(Char(LE) o Pa(Suc(n) o To1(N),id(N)),
 Iff(EQ(Add(m,Suc(n)) o To1(N),id(N)),
     EQ(m o To1(N),Sub(id(N),Suc(n) o To1(N)))))’ >>
  strip_tac >>
 rw[GSYM Imp_def,IMP_def,GSYM Iff_def,IFF_def,p12_of_Pa,GSYM Add_def,o_assoc,
       Pa_distr,GSYM EQ_def,Eq_property_TRUE,Swap_Pa,GSYM Le_def1,
       GSYM Sub_def] >>
 once_rw[one_to_one_id] >> rw[idL,idR] )  >> 
 pop_assum strip_assume_tac >>
 arw[IP_el,Suc_def] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Le_def,Sub_O,Suc_NONZERO] >> strip_tac >> arw[] >>
 rw[Add_Suc,Suc_eq_eq,Le_MONO,Sub_mono_eq] >>rpt strip_tac >>
 first_x_assum drule >> arw[])
(form_goal
 “!m:1->N n p. Le(n,p) ==> (Add(m,n) = p <=> m = Sub(p,n))”));
 
val NOT_SUC_LESS_EQ_O = prove_store("NOT_SUC_LESS_EQ_O",
e0
(rw[Le_def,Sub_O,Suc_NONZERO])
(form_goal
 “!n. ~(Le(Suc(n),O))”));


val NOT_SUC_LT_O = prove_store("NOT_SUC_LT_O",
e0
(rw[Lt_def,NOT_SUC_LESS_EQ_O])
(form_goal
 “!n. ~(Lt(Suc(n),O))”));

val Lt_MONO = LESS_MONO_EQ |> rewr_rule[GSYM Lt_def1,Suc_def]
                           |> store_as "Lt_MONO";

val NOT_LESS = prove_store("NOT_LESS",
e0
(qby_tac
 ‘?P. !m. (!n. ~(Lt(m,n)) <=> Le(n,m)) <=> P o m = TRUE’ 
 >-- (qexists_tac ‘ALL(Iff(Not(Char(LT) o Swap(N,N)),Char(LE)))’
     >> strip_tac >>
     rw[ALL_property,GSYM Iff_def,IFF_def,p12_of_Pa,o_assoc,
       GSYM Not_def,NEG_def,
       Pa_distr,Swap_Pa,GSYM Le_def1,
       GSYM Lt_def1,TRUE_xor_FALSE]
     )>> pop_assum strip_assume_tac >>
 arw[IP_el] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Suc_def] >> rw[Le_O_iff] >> strip_tac (* 2 *)
 >-- (strip_tac >> dimp_tac >> strip_tac >>
     ccontra_tac >> fs[O_xor_SUC,Suc_def] >> fs[Lt_def,GSYM Suc_NONZERO]>>
     fs[Le_def,Sub_Suc,Sub_of_O,Pre_O] >> rfs[]) >>
 strip_tac >> strip_tac >>
 qby_tac ‘?P1.!n'. (~Lt(Suc(n), n') <=> Le(n', Suc(n))) <=> 
 P1 o n' = TRUE’ >--
 (qexists_tac ‘Iff(Not(Char(LT) o Pa(Suc(n) o To1(N),id(N))),Char(LE) o Pa(id(N),Suc(n) o To1(N)))’ >> strip_tac >>
  rw[GSYM Iff_def,IFF_def,p12_of_Pa,o_assoc,
       GSYM Not_def,NEG_def,
       Pa_distr,GSYM Le_def1,
       GSYM Lt_def1,TRUE_xor_FALSE]>>
 once_rw[one_to_one_id] >> rw[idL,idR] ) >>
 pop_assum strip_assume_tac >> arw[IP_el] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rw[NOT_SUC_LT_O,Le_O] >>
 rw[Suc_def] >> strip_tac >> arw[] >>
 rw[Le_MONO,Lt_MONO] >> arw[])
(form_goal “!m:1->N n. ~(Lt(m,n)) <=> Le(n,m)”));

val RIGHT_SUB_DISTR = prove_store("RIGHT_SUB_DISTR",
e0
(rpt strip_tac >>
 qsspecl_then [‘Mul(Sub(m,n),p)’,‘Mul(n,p)’,‘Mul(m,p)’]
 assume_tac ADD_EQ_SUB >> 
 cases_on “Le(n:1->N,m)” >--
 (drule Le_MONO_Mul' >> fs[] >>
 fs[GSYM RIGHT_DISTR] >> drule SUB_ADD >> fs[]) >>
 fs[GSYM NOT_LESS] >> fs[Lt_def] >>
 fs[Le_def,Mul_clauses'] >> flip_tac >> rw[GSYM Le_def] >>
 irule Le_MONO_Mul' >> arw[Le_def])
(form_goal “!m:1->N n p. Mul(Sub(m,n),p) = Sub(Mul(m,p),Mul(n,p))”));

val LEFT_SUB_DISTR = prove_store("LEFT_SUB_DISTR",
e0
(rpt strip_tac >> once_rw[Mul_sym] >>
 rw[RIGHT_SUB_DISTR])
(form_goal “!m:1->N n p. Mul(p,Sub(m,n)) = Sub(Mul(p,m),Mul(p,n))”));

(*Le_MONO_Mul' Le_MONO_Mul2*)
val J1_xi = prove_store("J1_xi",
e0
(rw[lej_property,GSYM zj_def,Add_O2] >> rpt strip_tac >>
 rw[Mulj_property,lej_property] >> 
 rw[Add_assoc] >> once_rw[Add_sym] >>
 rw[GSYM Add_assoc] >> rw[GSYM RIGHT_DISTR] >>
 rw[Add_assoc] >> rw[GSYM RIGHT_DISTR] >> 
 drule Le_MONO_Mul'  >>
 first_x_assum (qsspecl_then [‘Sub(Add(b,c),Add(a,d))’] assume_tac) >>
 fs[LEFT_SUB_DISTR] >>
 qby_tac
 ‘Le(Mul(f, Add(a, d)),Mul(f, Add(b, c)))’
 >-- (once_rw[Mul_sym] >> irule Le_MONO_Mul' >> arw[]) >>
 drule SUB_ADD >> 
 qsspecl_then [‘Sub(Mul(f, Add(b, c)), Mul(f, Add(a, d)))’,
               ‘Sub(Mul(e, Add(b, c)), Mul(e, Add(a, d)))’,
               ‘Mul(f, Add(a, d))’] 
 drule $ iffRL LESS_EQ_MONO_ADD_EQ >> rfs[] >>
 pop_assum mp_tac >> once_rw[Add_sym] >> strip_tac >>
 qsspecl_then 
 [‘Mul(f, Add(c, b))’,
  ‘Add(Mul(f, Add(a, d)),
               Sub(Mul(e, Add(b, c)), Mul(e, Add(a, d))))’,
  ‘Mul(e,Add(a,d))’] drule $ iffRL LESS_EQ_MONO_ADD_EQ >>
 fs[GSYM Add_assoc] >> 
 rev_drule Le_MONO_Mul' >>
 first_x_assum $ qspecl_then [‘e’] assume_tac >>
 pop_assum mp_tac >> once_rw[Mul_sym] >> strip_tac >>
 drule SUB_ADD >> fs[] >> once_rw[Add_sym] >> 
 qpick_x_assum
 ‘Le(Add(Mul(f, Add(c, b)), Mul(e, Add(a, d))),
              Add(Mul(f, Add(a, d)), Mul(e, Add(b, c))))’
 mp_tac >> pop_assum_list (map_every (K all_tac)) >>
 strip_tac >>
 qsspecl_then [‘b’,‘c’] assume_tac Add_sym >> arw[] >>
 qsspecl_then [‘d’,‘a’] assume_tac Add_sym >> arw[] >>
 fs[] >> 
 qsspecl_then [‘Mul(e, Add(a, d))’,‘Mul(f, Add(c, b))’]
 assume_tac Add_sym >> fs[])
(form_goal “!a b c d e f. 
lej o Pa(Pa(a,b),Pa(c,d)) = TRUE & 
lej o Pa(0j,Pa(e,f)) = TRUE ==> 
 lej o Pa(Mulj(Pa(a,b),Pa(e,f)),Mulj(Pa(c,d),Pa(e,f))) = TRUE”));



val Z2_xi = prove_store("Z2_xi",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>  
 strip_tac >> strip_tac >>
 rw[Lez_def] >> rw[LEz_def] >>
 rpt strip_tac >>
 qby_tac ‘lej o Pa(Pa(a,b),Pa(c,d)) = TRUE’
 >-- (irule $ iffLR J2_iv' >>
      qexistsl_tac [‘rep(asz(Pa(a, b)))’,‘rep(asz(Pa(c, d)))’] >>
     arw[] >> rw[GSYM rep_rel_all]) >>
 qby_tac ‘lej o Pa(0j,Pa(e,f)) = TRUE’
 >-- (fs[GSYM zj_def] >> irule $ iffLR J2_iv' >>
        qexistsl_tac [‘rep(asz(Pa(O, O)))’,‘rep(asz(Pa(e, f)))’] >>
        arw[] >> rw[GSYM rep_rel_all]) >>
 rw[GSYM Mulz_def,GSYM MULz_def,Pa_distr,p12_of_Pa,o_assoc] >> 
 rw[asz_def,rep_def,Mulj_def] >>
 irule $ iffLR J2_iv' >> 
 qexistsl_tac [‘Mulj(Pa(a,b),Pa(e,f))’,‘Mulj(Pa(c,d),Pa(e,f))’] >> 
 strip_tac (* 2 *)
 >-- (irule J1_xi >> arw[]) >> strip_tac (* 2 *)
 >-- (once_rw[ZR_cond] >>
     qexistsl_tac [‘Mulj(Pa(a, b), Pa(e, f))’,
                   ‘Mulj(rep(asz(Pa(a, b))), rep(asz(Pa(e, f))))’]>>
     rw[ZR_refl,GSYM rep_rel_all] >> 
     irule J2_iii' >> once_rw[ZR_sym] >>rw[GSYM rep_rel_all]) >>
once_rw[ZR_cond] >>
qexistsl_tac [‘Mulj(Pa(c, d), Pa(e, f))’,
              ‘Mulj(rep(asz(Pa(c, d))), rep(asz(Pa(e, f))))’]>>
rw[ZR_refl,GSYM rep_rel_all] >> 
irule J2_iii' >> once_rw[ZR_sym] >>rw[GSYM rep_rel_all]
)
(form_goal
 “!a b c d e f.
  Lez(asz(Pa(a,b)),asz(Pa(c,d))) & Lez(asz(0j),asz(Pa(e,f))) ==>
  Lez(Mulz(asz(Pa(a,b)),asz(Pa(e,f))),Mulz(asz(Pa(c,d)),asz(Pa(e,f))))”));



(*
val lej_ex = prove_store("lej_ex",
e0
()
(form_goal
 “?lej. !a:1-> N b c d. 
  lej o Pa(Pa(a,b),Pa(c,d)) = TRUE <=> 
  Le(Add(a,d),Add(b,c))”));
*)


(*
rastt "Ev(X,2) o (f :1-> X * Pow(X))"



should be same 
rastt "Ev(X,2) o f: 1-> X * Exp(X,2)"

otherwise cannot unify 

so the subst from Pow(X) into Exp(X,2) must be done before unification

two dictionaries 

Exp(X,2) <> Pow(X)

("Pow",([("X",ob)],Exp(X,2) as a ast))


then use an inst_ast version of inst_term 

*)

(*

fun subst_ast a1 a2 ast = 
case ast of 
    aId(a) => if aId(a) = a1 then a2 else ast
   | aApp(str,astl) => 
     if ast = a1 then a2 else
     aApp(str,List.map (subst_ast a1 a2) astl)
   | aInfix(ast1,str,ast2) =>
    aInfix(subst_ast a1 a2 ast1,str,subst_ast a1 a2 ast2)
   | aBinder(str,ns,b) =>
     aBinder(str,subst_ast a1 a2 ns,subst_ast a1 a2 b)


val abbrevs0 = [("Exp",["X",ob_sort])]

*)


(*cannot be like fsyms psyms dict, should it be a dictionary at all?

thought about using something like ("Exp",([old arguments],[new_arguments]), and strings as key, but then the pp need another dictionary, seems weird.)
*)


(*fun subst_abbr ast = 

the obvious thing is to write a code that search if there is any occurrence of each abbreved term and replace them.

but then need to look through the dictionary and find out each occurence of any abbreved term.

Any better way to write this?


*)





