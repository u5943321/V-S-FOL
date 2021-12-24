
(*singleton*)
val Sing_ex = prove_store("Sing_ex",
e0
(strip_tac >> qexists_tac ‘Tp(Char(Diag(A)))’ >>
 rw[])
(form_goal “!A. ?Sing. Tp(Char(Diag(A))) = Sing”));

val Sing_def = Sing_ex |> spec_all 
                       |> ex2fsym0 "Sing" ["A"]
                       |> store_as "Sing_def";



(*sigma*)
val Sig_ex = prove_store("Sig_ex",
e0
(strip_tac >> qexists_tac ‘Char(Sing(A))’ >>
 rw[])
(form_goal “!A. ?Sig. Char(Sing(A)) = Sig”));

val Sig_def = Sig_ex |> spec_all 
                       |> ex2fsym0 "Sig" ["A"]
                       |> store_as "Sig_def";


val pred_ext' = prove_store("pred_ext'",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 irule FUN_EXT >> strip_tac >> 
 once_rw[GSYM pred_ext] >> arw[])
(form_goal
 “!X p1:X->1+1 p2. 
  (!x. p1 o x = TRUE <=> p2  o x = TRUE) <=> p1 = p2”));

val Sing_Mono = prove_store("Sing_Mono",
e0
(strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qby_tac ‘Mem(B) o Pa(p1(B,B),Sing(B) o p2(B,B))
          = Eq(B)’
 >-- rw[GSYM Mem_def,GSYM Sing_def,GSYM Eq_def,
        Ev_of_Tp] >> 
 qby_tac ‘Eq(B) o Pa(p1(B,X),g o p2(B,X)) = 
          Eq(B) o Pa(p1(B,X),h o p2(B,X))’
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[o_assoc,Pa_distr,p12_of_Pa] >>
     arw[GSYM o_assoc]) >>
 irule FUN_EXT >> strip_tac >>
 qsuff_tac ‘!a'. g o a = a' <=> h o a = a'’ >--
 (rpt strip_tac >> 
 first_x_assum (qspecl_then [‘g o a’] assume_tac) >>
 fs[]) >>
 strip_tac >> 
 pop_assum mp_tac >>
 once_rw[GSYM pred_ext'] >> 
 strip_tac >>
 first_x_assum 
  (qspecl_then [‘Pa(a',a)’] assume_tac) >>
 fs[o_assoc,Pa_distr,p12_of_Pa,Eq_property_TRUE] >>
 dflip_tac >> arw[])
(form_goal “!B. Mono(Sing(B))”));



val Mem_Sing = prove_store("Mem_Sing",
e0
(rw[GSYM Mem_def,GSYM Sing_def] >>
 rw[Ev_of_Tp_el] >> rw[Char_Diag,GSYM TRUE_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!B b0:1->B b. Mem(B) o Pa(b,Sing(B) o b0) = TRUE<=>
 b0 = b ”));

val Rel_U_fac = prove_store("Rel_U_fac",
e0
(rpt strip_tac>> irule prop_2_half2' >>
 rw[Sing_Mono] >> rpt strip_tac >>
 first_x_assum (qsspecl_then [‘xb’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘b’ >> 
 once_rw[IN_EXT] >>
 rw[IN_def,True1TRUE] >>
 rw[Mem_Sing] >> 
 rw[GSYM Mem_def] >>
 last_x_assum (assume_tac o GSYM) >> arw[] >>
 rw[Ev_of_Tp_el] >>
 strip_tac >> dimp_tac >> strip_tac >--
 (pop_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum drule >> arw[])
(form_goal
 “!A B R:B * A -> 1+1.
    (!a:1->A.?!b:1->B. R o Pa(b,a) = TRUE) ==>
    ?f:A->B. Sing(B) o f = Tp(R)”));


val Rel2Ar = prove_store("Rel2Ar",
e0
(rpt strip_tac >> drule Rel_U_fac >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘h’ >>
 rpt strip_tac >> 
 qby_tac
 ‘Mem(B) o Pa(b,Sing(B) o h o a) = Mem(B) o Pa(b,Tp(R) o a)’
 >-- arw[GSYM o_assoc] >>
 fs[GSYM Mem_def,GSYM Sing_def,Ev_of_Tp_el] >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Char_Diag,GSYM TRUE_def] >> rflip_tac >> rw[]
 )
(form_goal
 “!A B R:B * A -> 1+1. 
   (!a:1->A.?!b:1->B. R o Pa(b,a) = TRUE) ==>
   (?f:A->B. !a b. f o a = b <=> R o Pa(b,a) = TRUE)”));


val Rel2Ar' = prove_store("Rel2Ar'",
e0
(rpt strip_tac >> 
 assume_tac Rel2Ar >>
 qby_tac
 ‘?R'. !a b. R' o Pa(b,a) = TRUE <=> 
  R o Pa(a,b) = TRUE’
 >-- (qexists_tac ‘R o Swap(B,A)’ >>
     rw[o_assoc,Swap_Pa]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘!a:1->A. ?!b.R' o Pa(b,a) = TRUE’ 
 >-- (strip_tac >>uex_tac >>
     last_x_assum 
     (qspecl_then [‘a’] (strip_assume_tac o uex_expand)) >>
     qexists_tac ‘b’ >> arw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >>
 fs[])
(form_goal
 “!A B R:A * B -> 1+1. 
   (!a:1->A.?!b:1->B. R o Pa(a,b) = TRUE) ==>
   (?f:A->B. !a b. f o a = b <=> R o Pa(a,b) = TRUE)”));










(*

(*pred v*)
val Pv_ex = prove_store("Pv_ex",
e0
(rpt strip_tac >>
 qexists_tac ‘
  Tp(Mem(C * B) o 
      Pa(Pa(p31(C,B,Exp(C * B,1+1)),
            p32(C,B,Exp(C * B,1+1))),
         p33(C,B,Exp(C * B,1+1)))
      ) ’ >> rw[])
(form_goal
 “!B C. 
  ?v. 
  Tp(Mem(C * B) o 
      Pa(Pa(p31(C,B,Exp(C * B,1+1)),
            p32(C,B,Exp(C * B,1+1))),
         p33(C,B,Exp(C * B,1+1)))
      ) = v”));

val Pv_def =  Pv_ex |> spec_all 
                    |> ex2fsym0 "Pv" ["B","C"]
                    |> store_as "Pv_def";

(*pred u*)
val Pu_ex = prove_store("Pu_ex",
e0
(rpt strip_tac >>
 qexists_tac ‘Tp(Sig(C) o
  Tp(Mem(C * B) o 
      Pa(Pa(p31(C,B,Exp(C * B,1+1)),
            p32(C,B,Exp(C * B,1+1))),
         p33(C,B,Exp(C * B,1+1)))
      ) )’ >> rw[])
(form_goal
 “!B C. 
  ?u. Tp(Sig(C) o
  Tp(Mem(C * B) o 
      Pa(Pa(p31(C,B,Exp(C * B,1+1)),
            p32(C,B,Exp(C * B,1+1))),
         p33(C,B,Exp(C * B,1+1)))
      )) = u”));

val Pu_def =  Pu_ex |> spec_all 
                    |> ex2fsym0 "Pu" ["B","C"]
                    |> store_as "Pu_def";



(*hat true*)
val Ht_ex = prove_store("Ht_ex",
e0
(rpt strip_tac >>
 qexists_tac ‘Tp1(True(B))’ >> rw[])
(form_goal
 “!B.?ht. Tp1(True(B)) = ht ”));


val Ht_def =  Ht_ex |> spec_all 
                    |> ex2fsym0 "Ht" ["B"]
                    |> store_as "Ht_def";


(*arrow m as graph*)
val Gm_ex = prove_store("Gm_ex",
e0
(rpt strip_tac >>
 qsspecl_then [‘Pu(B,C)’,‘Ht(B)’]
 assume_tac Pb_ex >>
 pop_assum mp_tac >>
 once_rw[To1_def] >> strip_tac >>
 qexistsl_tac [‘P’,‘p’] >> arw[])
(form_goal
 “!B C. ?BC m. isPb(Pu(B,C),Ht(B),m,To1(BC))”));


val Gm_def = Gm_ex |> spec_all 
                   |> ex2fsym0 "Axp" ["B","C"]
                   |> ex2fsym0 "Gm" ["B","C"]
                   |> gen_all
                   |> store_as "Gm_def";


val SGL_p166 = prove_store("SGL_p166",
e0
()
(form_goal
 “!B C. ?ae:B * Axp(B,C) -> C”));
*)
