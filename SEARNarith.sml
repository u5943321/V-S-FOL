

local
val lemma = 
 fVar_Inst 
[("P",([("A",mem_sort$ Pow $ Cross N (mk_set "X"))],
“IN(Pair(O,a:mem(X)),A) &
 (!n x.IN(Pair(n,x),A) ==> IN(Pair(Eval(SUC,n),Eval(f,x)),A))”))] 
(IN_def_P_expand |> qspecl [‘Pow(N * X)’]) 
val As_def = lemma |> ex2fsym0 "As" ["a","f"] |> conjE1 
                   |> gen_all |> GSYM
val U_ex_lemma = fVar_Inst 
[("P",([("nx",mem_sort $ Cross N (mk_set "X"))],
“IN(nx,Eval(BI(N * X),As(a0,f)))”))]
(Thm_2_4 |> qspecl [‘N * X’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all BI_property)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all As_def) |> gen_all
val rel_ex_lemma = 
fVar_Inst 
[("P",([("n",mem_sort N),("x",mem_sort (mk_set "X"))],
“?r.Eval(u0:U-> N * X,r) = Pair(n,x)”))]
(AX1 |> qspecl [‘N’,‘X’]) |> uex_expand
val imp_ind_l = 
fVar_Inst 
[("P",([("n",mem_sort N)],
“!x.Holds(R:N->X,n,x) ==> Holds(R,Eval(SUC,n),Eval(f,x))”))]
N_ind_P
val O_case_u_l = 
fVar_Inst 
[("P",([("nx",mem_sort $ Cross N (mk_set "X"))],
“Holds(R,Eval(p1(N,X),nx),Eval(p2(N,X),nx)) & 
 ~(Eval(p1(N,X),nx) = O & Eval(p2(N,X),nx) = x)”))] 
(IN_def_P_expand |> qspecl [‘(N * X)’]) 
val ex_R_ss = 
fVar_Inst 
[("P",([("mr",mem_sort $ Cross N (mk_set "X"))],
“Holds(R,Eval(p1(N,X),mr),Eval(p2(N,X),mr)) &
 !n. Eval(p1(N,X),mr) = Eval(SUC,n) ==>
 ?r0.Holds(R,n,r0) & Eval(p2(N,X),mr) = Eval(f:X->X,r0)”))] 
(IN_def_P_expand |> qspecl [‘(N * X)’]) 
val u_R_ss1 = 
fVar_Inst 
[("P",([("mr",mem_sort $ Cross N (mk_set "X"))],
“Holds(R,Eval(p1(N,X),mr),Eval(p2(N,X),mr)) &
 (!x'.Holds(R,Eval(p1(N,X),mr),x') ==> x' = Eval(p2(N,X),mr))”))] 
(IN_def_P_expand |> qspecl [‘(N * X)’]) 
val ex_ind_l = 
fVar_Inst 
[("P",([("n",mem_sort N)],
“?x.Holds(R:N->X,n,x)”))]
N_ind_P
in
val Nind_ex = prove_store("Nind_ex",
e0
(rpt strip_tac >> 
 qspecl_then [‘X’,‘a’,‘f’] (x_choosel_then ["U","u0"] 
 strip_assume_tac) U_ex_lemma >>
 strip_assume_tac rel_ex_lemma >> pop_assum (K all_tac) >>
 (*qexists_tac ‘R’ >> *)
 qby_tac 
 ‘!n x. Holds(R,n,x) <=>
  !ss. IN(Pair(O,a),ss) &
       (!n x. IN(Pair(n,x),ss) ==>
              IN(Pair(Eval(SUC,n),Eval(f,x)),ss)) ==>
        IN(Pair(n,x),ss)’
 >-- (arw[] >> rpt strip_tac >>
 fconv_tac 
 (rand_fconv no_conv 
 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "mem"))) >> rw[]) >>
 pop_assum mp_tac >> pop_assum (K all_tac) >> 
 pop_assum (K all_tac) >> strip_tac >>
 qby_tac 
 ‘Holds(R,O,a)’ >-- (arw[] >> rpt strip_tac) >>
 qby_tac
 ‘!n x. Holds(R,n,x) ==> Holds(R,Eval(SUC,n),Eval(f,x))’
 >-- (match_mp_tac imp_ind_l (* irule bug *)>> strip_tac (* 2 *)
     (*0 case*)
     >-- (rpt strip_tac >>
         qsuff_tac ‘Holds(R, O, x') ==>
         Holds(R, Eval(SUC, O), Eval(f, x'))’ 
         >-- (rpt strip_tac >> first_assum drule >> arw[]) >>
         arw[] >> rpt strip_tac >> first_assum irule >>
         last_assum $ irule o iffLR >> arw[]) >>
     rpt strip_tac >> arw[] >> 
     rpt strip_tac >> first_assum irule >>
     qpick_x_assum ‘Holds(R, Eval(SUC, n'), x')’ mp_tac >> 
     arw[] >> rpt strip_tac >> first_assum irule >> arw[]) >>
 qby_tac ‘!x. Holds(R,O,x) ==> x = a’
 >-- (rpt strip_tac >> ccontra_tac >>
      qsuff_tac ‘?ss. IN(Pair(O,a),ss) & 
      (!n x.IN(Pair(n,x),ss) ==> IN(Pair(Eval(SUC,n),Eval(f,x)),ss)) &
      ~(IN(Pair(O,x),ss))’
      >-- (last_assum (drule o iffLR) >> rpt strip_tac >>
          qsuff_tac ‘IN(Pair(O, x), ss)’
          >-- arw[] >>
          first_x_assum irule >> arw[]) >>
      x_choose_then "ss" strip_assume_tac O_case_u_l >>
      pop_assum (K all_tac) >>
      qby_tac ‘~(IN(Pair(O,x),ss))’
      >-- (pop_assum (assume_tac o GSYM) >> once_arw[] >>
          rw[Pair_def]) >>
      qby_tac ‘IN(Pair(O,a),ss)’
      >-- (pop_assum (K all_tac) >> pop_assum (assume_tac o GSYM) >>
           once_arw[] >> rw[Pair_def] >> arw[] >>
           flip_tac >> first_x_assum accept_tac) >>
      qexists_tac ‘ss’ >> arw[] >>
      pop_assum (K all_tac) >> pop_assum (K all_tac) >>
      pop_assum (assume_tac o GSYM) >> strip_tac >> strip_tac >> 
      once_arw[] >> rw[Pair_def] >> rpt strip_tac >-- 
      (first_x_assum irule >> arw[]) >>
      rw[SUC_NONZERO]) >>
 qby_tac ‘!ss.IN(Pair(O,a),ss) &
      (!n x.IN(Pair(n,x),ss) ==> IN(Pair(Eval(SUC,n),Eval(f,x)),ss)) ==>
      !n x. Holds(R,n,x) ==> IN(Pair(n,x),ss)’
 >-- (once_arw[] >> rpt strip_tac >> first_x_assum irule >>
     arw[]) >>
 x_choose_then "ss" strip_assume_tac ex_R_ss >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >>
 qby_tac ‘!n x. Holds(R,n,x) ==> IN(Pair(n,x),ss)’
 >-- (first_x_assum match_mp_tac >> once_arw[] >>
      rw[Pair_def] >> strip_tac (* 2 *)
      >-- (strip_tac >-- first_x_assum accept_tac >>
           flip_tac >> rw[SUC_NONZERO]) >>
      rpt strip_tac (*2  *)
      >-- (first_x_assum irule >> first_x_assum accept_tac) >>
      qexists_tac ‘x'’ >> rw[] >>
      fs[SUC_eq_eq]) >>
 pop_assum mp_tac >>
 last_x_assum mp_tac >> last_x_assum mp_tac >> 
 last_x_assum (assume_tac o GSYM) >> once_arw[] >>
 rw[Pair_def] >> rpt strip_tac >>
 qby_tac
 ‘!n x. Holds(R,Eval(SUC,n),x) ==> 
  ?x0. Holds(R,n,x0) & x = Eval(f,x0)’
 >-- (rpt strip_tac >> first_x_assum drule >>
     pop_assum strip_assume_tac >> 
     first_x_assum (qspecl_then [‘n’] assume_tac) >> fs[] >>
     qexists_tac ‘r0’ >> arw[]) >>
 x_choose_then "ss1" strip_assume_tac u_R_ss1 >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >>
 qby_tac 
 ‘!n x. Holds(R,n,x) ==> IN(Pair(n,x),ss1)’
 >-- (first_x_assum match_mp_tac >> once_arw[] >>
      rw[Pair_def] >> strip_tac (* 2 *)
      >-- (strip_tac (*2*)>> first_x_assum accept_tac) >>
      rpt strip_tac (* 2 *)
      >-- (first_x_assum irule >> first_x_assum accept_tac) >>
      first_assum (qspecl_then [‘n'’,‘x''’] assume_tac) >>
      first_x_assum drule >> pop_assum strip_assume_tac >> 
      once_arw[] >>
      qsuff_tac ‘x0 = x'’
      >-- (strip_tac >> arw[]) >>
      first_x_assum irule >> first_x_assum accept_tac) >>
 pop_assum mp_tac >> once_arw[] >> rw[Pair_def] >>
 rpt strip_tac >> 
 qby_tac
 ‘!n x.Holds(R,n,x) ==>
  !x'. Holds(R,n,x') ==> x' = x’
 >-- (rpt strip_tac >> first_assum drule >>
      first_x_assum drule >> pop_assum strip_assume_tac >>
      flip_tac >> first_x_assum irule >>
      first_x_assum accept_tac) >>
 qby_tac
 ‘!n.?x. Holds(R,n,x)’
 >-- (irule ex_ind_l >> rpt strip_tac >--
     (last_x_assum drule >> qexists_tac ‘Eval(f,x)’ >> arw[]) >>
     qexists_tac ‘a’ >> arw[]) >>
 qby_tac
 ‘isFun(R)’
 >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac >>
      first_x_assum drule >> first_x_assum irule >> arw[]) >>
 qexists_tac ‘R’ >> arw[] >>
 drule $ GSYM Eval_def >> flip_tac >> once_arw[] >>
 strip_tac >-- first_x_assum accept_tac >>
 strip_tac >>
 drule Holds_Eval >> 
 first_x_assum (qspecl_then [‘n’] assume_tac) >> 
 last_x_assum irule >> first_x_assum accept_tac
 )
(form_goal
 “!X a:mem(X) f:X->X. isFun(f) ==> 
 ?u:N->X. isFun(u) & Eval(u,O) = a & 
 !n:mem(N).Eval(u,Eval(SUC,n)) = Eval(f,Eval(u,n))”));
end



local 
val ind_l = 
fVar_Inst 
[("P",([("n",mem_sort N)],
“Eval(u1:N->X,n) = Eval(u2,n)”))]
N_ind_P
in
val Nind_unique = prove_store("Nind_unique",
e0
(rpt strip_tac >> 
 irule $ iffRL FUN_EXT >> 
 arw[] >> irule ind_l >> arw[] >> rpt strip_tac >> arw[])
(form_goal
 “!X a:mem(X) f:X->X. isFun(f) ==>
  (!u1:N->X u2. (isFun(u1) & Eval(u1,O) = a & 
               (!n:mem(N).Eval(u1,Eval(SUC,n)) = Eval(f,Eval(u1,n))) & 
               isFun(u2) & Eval(u2,O) = a & 
               (!n:mem(N).Eval(u2,Eval(SUC,n)) = Eval(f,Eval(u2,n))))==>
  u1 = u2)”));
end


val Nind_uex = prove_store("Nind_uex",
e0
(rpt strip_tac >> uex_tac >>
 drule Nind_ex >> pop_assum strip_assume_tac >>
 qexists_tac ‘u’ >> arw[] >> rpt strip_tac >>
 irule Nind_unique >> 
 arw[] >> strip_tac 
 >-- (qexists_tac ‘f’ >> arw[]) >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!X a:mem(X) f:X->X. isFun(f) ==>
 ?!u:N->X. isFun(u) & Eval(u,O) = a & 
 !n:mem(N).Eval(u,Eval(SUC,n)) = Eval(f,Eval(u,n))”));



val Nind_def = Nind_uex |> spec_all |> undisch
                        |> uex_expand
                        |> ex2fsym0 "Nind" ["a","f"]
                        |> qgen ‘a’
                        |> disch_all
                        |> gen_all
                        |> store_as "Nind_def";

val Nind_property = Nind_def |> spec_all |> undisch |> spec_all
                        |> conjE1 |> qgen ‘a’
                        |> disch_all |> gen_all
                        |> store_as "Nind_property";

val Nind_Fun = Nind_property |> strip_all_and_imp |> conjE1
                             |> gen_all |> disch_all |> gen_all
                             |> store_as "Nind_Fun";


val Nind_eqns = Nind_property |> strip_all_and_imp |> conjE2
                             |> gen_all |> disch_all |> gen_all
                             |> store_as "Nind_Fun";

val SUC_Fun = SUC_isFun; 

val Eval_o_eq0 = prove_store("Eval_o_eq",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘Eval(g1, Eval(f1, a)) = Eval(g1 o f1, a) &
  Eval(g2, Eval(f2, a)) = Eval(g2 o f2, a)’
 >-- (strip_tac >> arw[]) >> strip_tac >> irule o_Eval >>
 arw[])
(form_goal
 “!A B f1:A->B C f2:A->C D g1:B->D g2:C->D.
  isFun(f1) ==> isFun(f2) ==> isFun(g1) ==> isFun(g2) ==>
  !a.Eval(g1,Eval(f1,a)) = Eval(g2,Eval(f2,a)) <=> 
     Eval(g1 o f1,a) = Eval(g2 o f2,a)”));

val Eval_o_eq = Eval_o_eq0 |> strip_all_and_imp |> gen_all
                           |> disch “isFun(g2:C->D)”
                           |> gen_all
                           |> disch “isFun(g1:B->D)”
                           |> gen_all
                           |> disch “isFun(f2:A->C)”
                           |> gen_all
                           |> disch “isFun(f1:A->B)”
                           |> gen_all
                           |> store_as "Eval_o_eq";

val Eval_eq_o = GSYM Eval_o_eq |> store_as "Eval_eq_o";

local
val l = 
(fVar_Inst [("P",([("d",mem_sort ONE),("x",mem_sort $ mk_set ("A"))],
“d = dot & x = a:mem(A)”))] (AX1 |> qspecl [‘1’,‘A’])) 
|> uex_expand
in
val El_ex = prove_store("El_ex",
e0
(rpt strip_tac >> strip_assume_tac l >>
 qexists_tac ‘R’ >> 
 qby_tac ‘isFun(R)’ >-- (rw[Fun_expand] >> arw[] >>
 rpt strip_tac >-- (qexists_tac ‘a’ >> rw[dot_def]) >> arw[]) >>
 arw[] >> drule $ GSYM Eval_def >> flip_tac >> arw[])
(form_goal
 “!A a:mem(A).?el:1->A.isFun(el) & Eval(el,dot) = a”))
end


val El_def = El_ex |> spec_all |> ex2fsym0 "El" ["a"]
                   |> gen_all
                   |> store_as "El_def";


val Eval_El = prove_store("Eval_El",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘a’] strip_assume_tac El_def >> 
 rw[dot_def] >> arw[]
 )
(form_goal
 “!A a:mem(A) x. Eval(El(a),x) = a”));

val El_Fun = El_def |> spec_all |> conjE1 |> gen_all
                    |> store_as "El_Fun";


val Nind_alt = prove_store("Nind_O",
e0
(rpt strip_tac >--
 (drule Nind_def >> arw[]) >-- (drule Nind_def >> arw[]) 
 >-- (drule Nind_def >> irule $ iffRL FUN_EXT >> 
     first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
     qby_tac ‘isFun(Nind(a,f) o SUC) & isFun(f o Nind(a, f))’
     >-- (strip_tac >> irule o_Fun >> arw[SUC_isFun]) >>
     arw[] >> strip_tac >> irule $ iffRL Eval_eq_o >>
     arw[SUC_Fun])
 (*irule does not work without strip*) >>
 drule Nind_def >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 first_x_assum irule >> arw[] >> 
 strip_tac >> irule $ iffLR Eval_eq_o >>
 arw[SUC_Fun]
 )
(form_goal
 “!X  f:X->X. isFun(f) ==>
 !a:mem(X).isFun(Nind(a,f)) & Eval(Nind(a,f),O) = a & 
 Nind(a,f) o SUC = f o Nind(a,f) &
 (!u. (isFun(u) & Eval(u,O) = a & u o SUC = f o u) ==> u = Nind(a,f))”));


val is_Nind = Nind_alt |> strip_all_and_imp
                       |> conjE2
                       |> conjE2
                       |> conjE2 |> gen_all
                       |> disch_all |> gen_all
                       |> store_as "is_Nind";

val El_eq_eq = prove_store("El_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (qby_tac ‘isFun(El(a)) & isFun(El(b))’
     >-- rw[El_Fun] >> 
     drule FUN_EXT >> fs[] >> 
     last_x_assum (qspecl_then [‘dot’] assume_tac) >>
     fs[El_def]) >> 
 arw[])
(form_goal
 “!A a:mem(A) b. El(a) = El(b) <=> a = b”));




val Eval_o_El = prove_store("Eval_o_El",
e0
(rpt strip_tac >> flip_tac >> irule $ iffRL Eval_o_l >>
 arw[El_Fun] >> rw[El_def])
(form_goal
 “!A B f:A->B.isFun(f) ==>
  !a. Eval(f,a) = Eval(f o El(a),dot)”));

val Nind_El = prove_store("Nind_el",
e0
(strip_tac >> strip_tac >> strip_tac >>
 drule Nind_def >> strip_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 arw[] >> rpt strip_tac (* 3 *)
 >-- irule $ iffRL FUN_EXT >> rpt strip_tac (* 3 *)
     >-- (irule $ iffRL Eval_o_l >> arw[Eval_El,El_Fun])
     >-- (irule o_Fun >> arw[El_Fun] (* arw bug that does not use El_Fun *)
         >> rw[El_Fun]) >>
     rw[El_Fun]
 >-- (irule $ iffRL FUN_EXT >> rpt strip_tac (*3*)
     >-- (irule $ iffLR Eval_o_eq >> 
          arw[SUC_Fun]) 
     >-- (irule o_Fun >> arw[SUC_Fun]) >>
     irule o_Fun >> arw[]) >>
 first_x_assum irule >> arw[] >> rpt strip_tac (* 2 *)
 >-- (irule $ iffRL Eval_o_eq >> arw[] >> rw[SUC_Fun]) >>
 drule Eval_o_El >> arw[] >> rw[El_def])
(form_goal
 “!X  f:X->X. isFun(f) ==>
 !a:mem(X).isFun(Nind(a,f)) & Nind(a,f) o El(O) = El(a) & 
 Nind(a,f) o SUC = f o Nind(a,f) &
 (!u. (isFun(u) & u o El(O) = El(a) & u o SUC = f o u) ==> u = Nind(a,f))”));



val Eval_El_mem = prove_store("Eval_El_mem",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (irule $iffRL FUN_EXT >> rpt strip_tac (* 3 *)
     >-- (rw[Eval_El] >> irule $iffRL Eval_o_l >>
         arw[Eval_El,El_Fun]) 
     >-- (irule o_Fun >> arw[El_Fun]) >>
     rw[El_Fun]) >>
 qby_tac ‘Eval(f o El(a),dot) = Eval(El(b),dot)’ 
 >-- arw[] >>
 pop_assum mp_tac >> rw[Eval_El] >> strip_tac >>
 qsuff_tac ‘Eval(f o El(a), dot) = Eval(f,a)’ 
 >-- (strip_tac >> arw[] >> fs[]) >>
 irule $ iffRL Eval_o_l >>
 arw[El_def])
(form_goal
 “!A B f:A->B. isFun(f) ==> !a b. Eval(f,a) = b <=>
 f o El(a) = El(b)”));



val comm_with_SUC_id0 = prove_store("comm_with_SUC_id0",
e0
(qspecl_then [‘N’,‘SUC’] strip_assume_tac Nind_def >>
 assume_tac SUC_isFun >> first_x_assum drule >>
 first_x_assum (qspecl_then [‘O’] strip_assume_tac) >> 
 rpt strip_tac >>
 qsuff_tac ‘f = Nind(O,SUC) & id(N) = Nind(O,SUC)’
 >-- (strip_tac >> arw[]) >> 
 strip_tac >> first_x_assum irule
 >-- (arw[] >> strip_tac >> 
      qby_tac 
      ‘Eval(f, Eval(SUC, n)) = Eval(f o SUC, n) & 
       Eval(SUC, Eval(f, n)) = Eval(SUC o f, n)’
      >-- (strip_tac >> irule o_Eval >> arw[]) >>
      arw[]) >>
 rw[Eval_id,id_Fun]
 )
(form_goal
 “!f:N->N. isFun(f) ==> Eval(f,O) = O & f o SUC = SUC o f ==> f = id(N)”));


val comm_with_SUC_id = prove_store("comm_with_SUC_id",
e0
(strip_tac >> strip_tac >> 
 drule comm_with_SUC_id0 >> drule Eval_El_mem >>
 fs[])
(form_goal
 “!f:N->N. isFun(f) ==> f o El(O) = El(O) & f o SUC = SUC o f ==> f = id(N)”));


val Pa_distr = prove_store("Pa_distr",
e0
(rpt strip_tac >> irule is_Pa >> 
 qspecl_then [‘A’,‘X’,‘a1’,‘B’,‘a2’] strip_assume_tac p12_of_Pa >>
 rfs[] >> rw[GSYM o_assoc] >> arw[] >> 
 qspecl_then [‘A’,‘X’,‘a1’,‘B’,‘a2’] strip_assume_tac Pa_Fun >>
 rfs[] >> rpt strip_tac >>
 irule o_Fun >> arw[])
(form_goal
“!A X a1:X ->A . isFun(a1) ==> !B a2:X->B.isFun(a2) ==>
  !X0 x:X0->X.isFun(x) ==> Pa(a1,a2) o x = 
Pa(a1 o x,a2 o x) ”));


val Pa_distr' = Pa_distr |> strip_all_and_imp |> conj_all_assum
                         |> disch_all
                         |> gen_all
                         |> store_as "Pa_distr'"; 




val p1_Fun = p12_Fun |> spec_all |> conjE1 |> gen_all
                       |> store_as "p1_Fun";



val p2_Fun = p12_Fun |> spec_all |> conjE2 |> gen_all
                       |> store_as "p2_Fun";


val Pa_eq_eq = prove_store("Pa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘p1(A,B) o Pa(f1, g1) = p1(A,B) o Pa(f2, g2) &
          p2(A,B) o Pa(f1, g1) = p2(A,B) o Pa(f2, g2)’
 >-- arw[] >>
 qsspecl_then [‘f1’,‘g1’] assume_tac p12_of_Pa >> 
 qsspecl_then [‘f2’,‘g2’] assume_tac p12_of_Pa >> 
 rfs[])
(form_goal
 “!A X f1:X->A.isFun(f1) ==> !f2:X->A.isFun(f2) ==>
  !B g1:X->B. isFun(g1) ==> !g2:X->B. isFun(g2) ==> 
  (Pa(f1,g1) = Pa(f2,g2) <=> f1 = f2 & g1 = g2)”));



val Pa_eq_eq' = prove_store("Pa_eq_eq'",
e0
(rpt strip_tac >> irule Pa_eq_eq >> arw[])
(form_goal
 “!A X f1:X->A f2 B g1:X->B g2.isFun(f1) & isFun(f2) & isFun(g1) & isFun(g2) ==> 
  (Pa(f1,g1) = Pa(f2,g2) <=> f1 = f2 & g1 = g2)”));


val Thm1_case1_comm_condition_left = prove_store(
"Thm1_case1_comm_condition_left",
e0
(rpt strip_tac >> qspecl_then [‘N’] assume_tac id_Fun >>
 drule Pa_distr >> first_x_assum rev_drule >>
 qspecl_then [‘N’,‘O’] assume_tac El_Fun >>
 first_x_assum drule >> arw[idL] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (drule Pa_eq_eq >> 
     qby_tac ‘isFun(f o El(O))’ 
     >-- (irule o_Fun >> arw[El_Fun]) >>
     first_x_assum drule >> 
     first_x_assum drule >> first_x_assum rev_drule >>
     fs[]) >>
 arw[])
(form_goal
 “!B f:N->B. isFun(f) ==> !g:1->B. isFun(g) ==>
 (Pa(id(N),f) o El(O) = Pa(El(O),g) <=> f o El(O) = g)”));


val Thm1_case1_comm_condition_right = prove_store(
"Thm1_case1_comm_condition_right",
e0
(rpt strip_tac >> 
 qsspecl_then [‘SUC o p1(N,B)’,‘h’,‘Pa(id(N),f)’] assume_tac Pa_distr'>>
 qsspecl_then [‘id(N)’,‘f’,‘SUC’] assume_tac Pa_distr' >>
 rfs[] >> 
 assume_tac SUC_Fun >> 
 qspecl_then [‘N’] assume_tac id_Fun >>
 qspecl_then [‘N’,‘B’] assume_tac p1_Fun >>
 qsspecl_then [‘id(N)’,‘f’] assume_tac Pa_Fun >>
 qsspecl_then [‘p1(N,B)’,‘SUC’] assume_tac o_Fun >>
 fs[] >> rfs[] >> fs[] >> rw[o_assoc,idL,idR] >>
 qsspecl_then [‘id(N)’,‘f’] assume_tac p1_of_Pa >> rfs[] >>
 rw[idR] >>
 qsspecl_then [‘SUC’,‘SUC’,‘h o Pa(id(N),f)’,‘f o SUC’] assume_tac Pa_eq_eq' >> 
 qsspecl_then [‘SUC’,‘f’] assume_tac o_Fun >>
 qsspecl_then [‘Pa(id(N),f)’,‘h’] assume_tac o_Fun >>
 fs[] >> rfs[] >> fs[])
(form_goal
 “!B f:N->B. isFun(f) ==> !h:N * B ->B.isFun(h) ==>
 (Pa(SUC o p1(N,B),h) o Pa(id(N),f) = Pa(id(N),f) o SUC <=>
 h o Pa(id(N),f) = f o SUC)”));

val Thm1_case1_comm_condition = prove_store(
"Thm1_case1_comm_condition",
e0
(rpt strip_tac >>  
 drule Thm1_case1_comm_condition_left >> first_x_assum drule >>
 drule Thm1_case1_comm_condition_right >> first_x_assum drule >>
 arw[] >> dimp_tac >> strip_tac >> arw[])
(form_goal
 “!B f0:N->B g:1->B h:N * B -> B.
  isFun(f0) & isFun(g) & isFun(h) ==> (f0 o El(O) = g & f0 o SUC = h o Pa(id(N),f0) <=>
 Pa(id(N),f0) o El(O) = Pa(El(O),g) &
 Pa(SUC o p1(N,B),h) o Pa(id(N),f0) = Pa(id(N),f0) o SUC)”));



val Dot_ex = prove_store("Dot_ex",
e0
(rpt strip_tac >> fs[Fun_expand] >>
 first_x_assum (qspecl_then [‘dot’] strip_assume_tac) >>
 last_x_assum (qspecl_then [‘dot’] strip_assume_tac) >>
 rw[dot_def] >> qexists_tac ‘b’ >> arw[] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal
 “!A f:1->A.isFun(f) ==> ?a. !d.Holds(f,d,a) &
   (!a0 d. Holds(f,d,a0) ==> a0 = a)”)); 

val Dot_def = Dot_ex |> spec_all |> ex2fsym "Dot" ["f"] 
                     |> gen_all |> store_as "Dot_def";


val Holds_El = prove_store("Holds_El",
e0
(rpt strip_tac >>  
 qspecl_then [‘A’,‘a’] strip_assume_tac El_def >>
 drule Eval_def >> arw[] >> flip_tac >> arw[dot_def])
(form_goal
 “!A a:mem(A) d. Holds(El(a),d,a)”));

 
val Dot_of_El = prove_store("Dot_of_El",
e0
(rpt strip_tac >> qspecl_then [‘A’,‘a’] assume_tac El_Fun >> 
 drule Dot_def >> first_x_assum (qspecl_then [‘dot’] strip_assume_tac) >>
 flip_tac >> first_x_assum irule >> qexists_tac ‘dot’ >>
 rw[Holds_El])
(form_goal
 “!A a:mem(A).Dot(El(a)) = a”));


val El_of_Dot = prove_store("El_of_Dot",
e0
(rpt strip_tac >> irule $ iffRL FUN_EXT >> rw[dot_def] >> rw[El_def] >>
 arw[] >> drule Dot_def >> 
 first_x_assum (qspecl_then [‘dot’] strip_assume_tac) >>
 strip_tac >> flip_tac >> first_x_assum irule >>
 qexists_tac ‘dot’ >> drule Holds_Eval >> arw[])
(form_goal
 “!X f:1->X. isFun(f) ==> El(Dot(f)) = f”));



val to_P_component = prove_store("to_P_component",
e0
(rpt strip_tac >> irule is_Pa >> arw[] >> strip_tac >> irule o_Fun >>
 arw[] >> rw[p12_Fun])
(form_goal
 “!A B X f:X->A * B. isFun(f) ==> f = Pa(p1(A,B) o f,p2(A,B) o f)”));

val is_Nind = Nind_El |> spec_all |> undisch |>spec_all |> conjE2
                      |> conjE2 |> conjE2
                      |> disch_all |> gen_all
                      |> store_as "is_Nind";




val Thm1_case_1 = prove_store("Thm1_case_1",
e0
(rpt strip_tac >> uex_tac >> 
 abbrev_tac “Nind(Dot(Pa(El(O),g:1->B)),Pa(SUC o p1(N,B),h:N * B->B)) = f'” >>
 abbrev_tac “p2(N,B) o f':N->N * B = f” >>
 qspecl_then [‘N’,‘O’] assume_tac El_Fun >>
 qsspecl_then [‘El(O)’,‘g’] assume_tac Pa_Fun >> rfs[] >>
 drule Dot_def >>
 first_x_assum (qspecl_then [‘dot’] strip_assume_tac) >>
 qspecl_then [‘N’,‘B’] strip_assume_tac p12_Fun >>
 assume_tac SUC_Fun >>
 qsspecl_then [‘p1(N,B)’,‘SUC’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘SUC o p1(N,B)’,‘h’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘Pa(SUC o p1(N,B),h)’] assume_tac Nind_El >>
 rfs[] >>
 first_x_assum (qspecl_then [‘Dot(Pa(El(O),g))’] strip_assume_tac) >>
 qby_tac ‘isFun(f')’ 
 >-- (qpick_x_assum ‘Nind(Dot(Pa(El(O), g)), Pa(SUC o p1(N, B), h)) = f'’
      (assume_tac o GSYM)  >> arw[]) >> 
 qsspecl_then [‘f'’,‘p1(N,B)’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘f'’,‘p2(N,B)’] assume_tac o_Fun >> rfs[] >> 
 qby_tac ‘p1(N,B) o f' = id(N)’ >--
 (irule comm_with_SUC_id >> arw[o_assoc] >>  
  qsspecl_then [‘Pa(El(O),g)’] assume_tac El_of_Dot >> rfs[] >>
  rw[GSYM o_assoc] >> 
  qsspecl_then [‘SUC o p1(N,B)’,‘h’] assume_tac p1_of_Pa >> rfs[] >>
  irule p1_of_Pa >> arw[]) >>
  qby_tac ‘f' = Pa(id(N),f)’ >-- 
 (qsspecl_then [‘f'’] assume_tac to_P_component >>
  first_x_assum drule >> once_arw[] >> pop_assum (K all_tac) >> arw[]) >>
 qexists_tac ‘f’ >>
 qby_tac ‘f o El(O) = g & f o SUC = h o Pa(id(N), f)’
 >-- (qpick_x_assum ‘p2(N, B) o f' = f’ (assume_tac o GSYM)>>
      once_arw[] >> pop_assum (K all_tac) >> rw[o_assoc] >> once_arw[] >>
      rw[GSYM o_assoc] >> 
      qsspecl_then [‘Pa(El(O),g)’] assume_tac El_of_Dot >> 
      first_x_assum drule >> arw[] >> 
      qsspecl_then [‘El(O)’,‘g’] assume_tac p2_of_Pa >> rfs[] >>
      qsspecl_then [‘SUC o p1(N,B)’,‘h’] assume_tac p2_of_Pa >> rfs[] >>
      qsspecl_then [‘id(N)’,‘f’] assume_tac p2_of_Pa >> rfs[] >>
      qspecl_then [‘N’] assume_tac id_Fun >> fs[]) >>
 once_arw[] >> rw[] >>  
 rpt strip_tac >>  
 qsuff_tac ‘Pa(id(N), f'') = Pa(id(N), f)’ 
 >-- (strip_tac >> 
      qsspecl_then [‘id(N)’,‘id(N)’,‘f''’,‘f’] assume_tac Pa_eq_eq' >>
      qspecl_then [‘N’] assume_tac id_Fun >>
      fs[] >> rfs[]) >>
 qsuff_tac ‘Pa(id(N), f'') = f'’ >-- arw[] >>
 qsuff_tac ‘Pa(id(N), f'') = 
  Nind(Dot(Pa(El(O), g)), Pa(SUC o p1(N, B), h))’ >-- arw[] >>
 irule is_Nind >>  
 qsspecl_then [‘id(N)’,‘f''’] assume_tac Pa_Fun >> 
 qspecl_then [‘N’] assume_tac id_Fun >> rfs[] >> fs[] >> 
 qsspecl_then [‘Pa(El(O),g)’] assume_tac El_of_Dot >> rfs[] >>
 qsspecl_then [‘id(N)’,‘f''’,‘SUC’] assume_tac Pa_distr' >> rfs[] >>
 rw[idL] >> 
 qsspecl_then [‘SUC o p1(N,B)’,‘h’,‘Pa(id(N),f'')’] assume_tac
 Pa_distr' >> rfs[] >> rw[o_assoc] >>
 qsspecl_then [‘id(N)’,‘f''’] assume_tac p1_of_Pa >> rfs[] >>
 rw[idR] >>
 qsspecl_then [‘id(N)’,‘f''’,‘El(O)’] assume_tac Pa_distr' >>
 rfs[] >> rw[idL])
(form_goal
 “!B g:1->B h:N * B -> B. isFun(g) & isFun(h) ==>  ?!f:N->B. isFun(f) & f o El(O) = g & f o SUC = h o Pa(id(N),f)”));





val Tp1_ex = prove_store("Tp1_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(f o p1(A,1))’ >> rw[])
(form_goal
“!A B f:A->B.?tpf:1->Exp(A,B).Tp(f o p1(A,1)) = tpf”));

val Tp1_def = Tp1_ex |> spec_all |> ex2fsym0 "Tp1" ["f"]
                     |> gen_all
                     |> store_as "Tp1_def";


val Ev_of_Tp = prove_store("Ev_of_Tp",
e0
(rpt strip_tac >> drule Tp_def >> arw[])
(form_goal
 “!A B X f:A * X ->B. isFun(f) ==>
  Ev(A,B) o Pa(p1(A,X),Tp(f) o p2(A,X)) = f”));


val Tp_eq = prove_store("Tp_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (drule $ GSYM Ev_of_Tp >> rev_drule $ GSYM Ev_of_Tp >> once_arw[] >>
      pop_assum (K all_tac) >> pop_assum (K all_tac) >> arw[]) >> arw[])
(form_goal
 “!A B X f:A * X ->B g:A * X ->B.isFun(f) ==> isFun(g) ==> (Tp(f) = Tp(g) <=> f = g)”));


val is_Tp = Tp_def |> strip_all_and_imp |> conjE2
                   |> disch_all |> gen_all
                   |> store_as "is_Tp";



val Ev_eq_eq = prove_store("Ev_eq_eq",
e0
(rpt strip_tac >> 
 qsuff_tac ‘f = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X))) & 
  g = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X)))’
 >-- (rpt strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >>
 irule is_Tp >> arw[] >> irule o_Fun >> rw[Ev_Fun] >>
 irule Pa_Fun >> rw[p12_Fun] >> irule o_Fun >> arw[p12_Fun])
(form_goal
 “!A B X f g. isFun(f) & isFun(g) ==> (Ev(A,B) o Pa(p1(A,X),f o p2(A,X)) = 
              Ev(A,B) o Pa(p1(A,X),g o p2(A,X)) ==> f = g)”));


val to_P_eq = prove_store("to_P_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f = Pa(p1(A,B) o g,p2(A,B) o g) &
            g = Pa(p1(A,B) o g,p2(A,B) o g)’ >--
 (strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Pa >> arw[] >> strip_tac >> irule o_Fun >> arw[p12_Fun]) >>
 drule to_P_component >> first_x_assum accept_tac)
(form_goal
 “!A B X f:X->A * B g:X->A * B. isFun(f) & isFun(g) ==> p1(A,B) o f = p1(A,B) o g &
 p2(A,B) o f = p2(A,B) o g ==> f = g”));

val Tp_Fun = Tp_def |> strip_all_and_imp |> conjE1 |> conjE1
                    |> disch_all |> gen_all
                    |> store_as "Tp_Fun";


val Tp1_Fun = prove_store("Tp1_Fun",
e0
(rpt strip_tac >> rw[GSYM Tp1_def] >> irule Tp_Fun >>
 irule o_Fun >> arw[p12_Fun])
(form_goal
 “!A B f:A->B. isFun(f) ==> isFun(Tp1(f))”));



val Pa_o_split = prove_store("Pa_o_split",
e0
(rpt strip_tac >> irule to_P_eq >>
 qspecl_then [‘A’,‘B’] strip_assume_tac p12_Fun >>
 qspecl_then [‘A’,‘X’] strip_assume_tac p12_Fun >>
 qsspecl_then [‘p2(A,X)’,‘g’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p2(A,B)’,‘f’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘f o p2(A,B)’,‘g’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A,B)’,‘g o f o p2(A,B)’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘p1(A,X)’,‘g o p2(A,X)’] assume_tac Pa_Fun >> rfs[] >> 
 qsspecl_then [‘p1(A,B)’,‘f o p2(A,B)’] assume_tac Pa_Fun >> rfs[] >>  
 qsspecl_then [‘Pa(p1(A, B), f o p2(A, B))’,‘Pa(p1(A, X), (g o p2(A, X)))’] assume_tac o_Fun >> rfs[] >>
 fs[GSYM o_assoc] >>
 qsspecl_then [‘p1(A,B)’,‘(g o f) o p2(A,B)’] assume_tac p12_of_Pa >>
 rfs[] >> 
 qsspecl_then [‘p1(A,X)’,‘g o p2(A,X)’] assume_tac p12_of_Pa >> rfs[] >>
 fs[o_assoc] >>
 qsspecl_then [‘p1(A,B)’,‘f o p2(A,B)’] assume_tac p12_of_Pa >> rfs[])
(form_goal
 “!B X f:B->X Y g:X->Y. isFun(f) & isFun(g) ==> !A.Pa(p1(A,B),g:X->Y o f o p2(A,B)) = 
  Pa(p1(A,X), g o p2(A,X)) o Pa(p1(A,B),f o p2(A,B))”));


val Thm1_comm_eq_left = prove_store(
"Thm1_comm_eq_left",
e0
(rpt strip_tac >> 
 qsspecl_then [‘O’] assume_tac El_Fun >>
 qspecl_then [‘A’,‘1’] strip_assume_tac p12_Fun >>
 qsspecl_then [‘p2(A,1)’,‘El(O)’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A,1)’,‘El(O) o p2(A,1)’] assume_tac Pa_Fun >> rfs[]>>
 qsspecl_then [‘g’] assume_tac Tp1_Fun >> rfs[] >>
 qsspecl_then [‘f’] assume_tac Tp_Fun >> rfs[] >>
 qspecl_then [‘A’,‘N’] assume_tac p12_Fun >> rfs[] >>
 qsspecl_then [‘p2(A,N)’,‘Tp(f)’] assume_tac o_Fun >> rfs[] >> 
 qsspecl_then [‘p1(A,1)’,‘g’] assume_tac o_Fun >> rfs[]  >>
 qby_tac ‘Pa(p1(A,1), Tp(f) o El(O) o p2(A,1)) = 
 Pa(p1(A,N),Tp(f) o p2(A,N)) o Pa(p1(A,1),El(O) o p2(A,1))’
 >-- (irule Pa_o_split  >> arw[]) >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qsuff_tac ‘f o Pa(p1(A, 1), El(O) o p2(A, 1)) = 
                 Ev(A,B) o Pa(p1(A,1),(Tp(f) o El(O)) o p2(A,1)) &
             g o p1(A, 1) = 
                 Ev(A,B) o Pa(p1(A,1),Tp1(g) o p2(A,1))’
     >-- (strip_tac >> fs[]) >> strip_tac (* 2 *)
     >-- (arw[o_assoc] >> 
         qsspecl_then [‘f’] assume_tac Ev_of_Tp >> rfs[GSYM o_assoc]) >>
     rw[GSYM Tp1_def] >>
     qsspecl_then [‘g o p1(A,1)’] assume_tac Ev_of_Tp >> rfs[]) >>
 rw[GSYM Tp1_def] >> irule is_Tp >>
 arw[o_assoc] >> rw[GSYM o_assoc] >>
 qsspecl_then [‘f’] assume_tac Ev_of_Tp >> rfs[] >>
 irule o_Fun >> arw[])
(form_goal
 “!A B f: A * N ->B g:A->B. isFun(f) & isFun(g) ==>
  (Tp(f) o El(O) = Tp1(g) <=> f o Pa(p1(A,1),El(O) o p2(A,1)) = g o p1(A,1))”));



val Pa_p1_p2 = prove_store("Pa_p1_p2",
e0
(rpt strip_tac >>
 fconv_tac (rewr_fconv (eq_sym "rel")) >>
 irule is_Pa >> rw[idR,p12_Fun,id_Fun])
(form_goal
 “!A B. Pa(p1(A,B),p2(A,B)) = id(A * B)”));




val Thm1_comm_eq_right = prove_store("Thm1_comm_eq_right",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘N * Exp(A,B)’] assume_tac p12_Fun >>
 qspecl_then [‘A * N’] assume_tac id_Fun >>
 assume_tac SUC_Fun >>
 qspecl_then [‘A’,‘N’] assume_tac p12_Fun >>
 qspecl_then [‘N’,‘Exp(A,B)’] assume_tac p12_Fun >>
 qspecl_then [‘A’,‘B’] assume_tac Ev_Fun >>
 qsspecl_then [‘f’] assume_tac Tp_Fun >> rfs[] >>
 qsspecl_then [‘p2(A,N)’,‘SUC’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A,N)’,‘SUC o p2(A,N)’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘id(A * N)’,‘f’] assume_tac Pa_Fun >> rfs[] >>
 qspecl_then [‘N’] assume_tac id_Fun >> 
 qsspecl_then [‘id(N)’,‘Tp(f)’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘Pa(id(A * N),f)’,‘h’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘Pa(p1(A, N), SUC o p2(A, N))’,‘f’] assume_tac o_Fun >>
 rfs[] >> 
 qsspecl_then [‘SUC’,‘Tp(f)’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p2(A, N * Exp(A, B))’,‘p2(N, Exp(A, B))’] 
 assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A, N * Exp(A, B))’,‘p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B))’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘Pa(p1(A, N * Exp(A, B)), p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B)))’,‘Ev(A,B)’] assume_tac o_Fun >>
 rfs[] >> 
 qsspecl_then [‘p2(A, N * Exp(A, B))’,‘p1(N, Exp(A, B))’]
 assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A, N * Exp(A, B))’,‘p1(N, Exp(A, B)) o p2(A, N * Exp(A, B))’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘Pa(p1(A, N * Exp(A, B)), p1(N, Exp(A, B)) o p2(A, N * Exp(A, B)))’,‘Ev(A, B) o
                Pa(p1(A, N * Exp(A, B)), p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B)))’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘l’,‘h’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘h o l’] assume_tac Tp_Fun >> rfs[] >>
 qsspecl_then [‘Pa(id(N), Tp(f))’,‘Tp(h o l)’] assume_tac o_Fun >> rfs[] >>
 qsuff_tac
 ‘Tp(h o l) o Pa(id(N),Tp(f)) = Tp(h o Pa(id(A * N),f)) & 
  Tp(f o Pa(p1(A,N), SUC o p2(A,N))) = Tp(f) o SUC’
 >-- (strip_tac >> dimp_tac >> strip_tac (* 2 *)
      >-- arw[] >>
      irule $ iffLR Tp_eq >> arw[] >>
      qpick_x_assum
      ‘Tp((h o l)) o Pa(id(N), Tp(f)) =
       Tp(h o Pa(id(A * N), f))’
      (assume_tac o GSYM) >> arw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Tp >> 
  qby_tac
  ‘Pa(p1(A, N), (Tp((h o l)) o Pa(id(N), Tp(f))) o p2(A, N))=
   Pa(p1(A,N * Exp(A,B)), Tp(h o l) o p2(A,N * Exp(A,B))) o 
   Pa(p1(A,N),Pa(id(N),Tp(f)) o p2(A,N))’ >-- 
  (rw[o_assoc] >> irule Pa_o_split >> arw[]) >>
  once_arw[] >> rw[GSYM o_assoc] >>
  qsspecl_then [‘h o l’] assume_tac Ev_of_Tp >> rfs[] >>
  rw[o_assoc] >> 
  qsspecl_then [‘p2(A,N)’,‘Pa(id(N), Tp(f))’] assume_tac o_Fun >> rfs[] >>
  qsspecl_then [‘p1(A,N)’,‘Pa(id(N), Tp(f)) o p2(A, N)’] 
  assume_tac Pa_Fun >> rfs[] >>
  qsspecl_then [‘Pa(p1(A, N), Pa(id(N), Tp(f)) o p2(A, N))’,‘l’] 
  assume_tac o_Fun >> rfs[] >>
  qsuff_tac
  ‘l o Pa(p1(A, N), Pa(id(N), Tp(f)) o p2(A, N)) = 
   Pa(id(A * N), f)’ >--
  (strip_tac >> arw[]) >>
  irule to_P_eq >> arw[] >> 
  qsspecl_then [‘id(A * N)’,‘f’] assume_tac p12_of_Pa >> rfs[] >>
  qpick_x_assum
  ‘Pa(Pa(p1(A, N * Exp(A, B)), p1(N, Exp(A, B)) o p2(A, N * Exp(A, B))),
                Ev(A, B) o
                Pa(p1(A, N * Exp(A, B)), p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B)))) = l’
  (assume_tac o GSYM) >> arw[] >>
  rw[GSYM o_assoc] >>
  qsspecl_then [‘Pa(p1(A, N * Exp(A, B)), p1(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B)))’,‘Ev(A, B) o
                Pa(p1(A, N * Exp(A, B)), p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B)))’] assume_tac p12_of_Pa >>
  rfs[] >>
  qsspecl_then [‘p1(A, N * Exp(A, B))’,‘p1(N, Exp(A, B)) o
                p2(A, N * Exp(A, B))’,‘Pa(p1(A, N), Pa(id(N), Tp(f)) o p2(A, N))’] assume_tac Pa_distr' >> rfs[] >>
  qsspecl_then [‘p1(A, N)’,‘Pa(id(N), Tp(f)) o p2(A, N)’]
  assume_tac p12_of_Pa >> rfs[] >>
  fs[o_assoc] >>
  rw[GSYM o_assoc] >>
  qsspecl_then [‘id(N)’,‘Tp(f)’] assume_tac p12_of_Pa >> rfs[] >>
  rw[idL,Pa_p1_p2] >>
  fs[o_assoc] >>
  qsspecl_then [‘p1(A, N * Exp(A, B))’,‘p2(N, Exp(A, B)) o
                p2(A, N * Exp(A, B))’,‘Pa(p1(A, N), Pa(id(N), Tp(f)) o p2(A, N))’] assume_tac Pa_distr' >>
  rfs[] >>fs[o_assoc] >> fs[GSYM o_assoc] >> 
  qsspecl_then [‘f’] assume_tac Ev_of_Tp >> rfs[]) >>
 (*flip tac does not work here*) 
 fconv_tac (rewr_fconv (eq_sym "rel"))  >> irule is_Tp >> arw[] >> 
 qby_tac
 ‘Pa(p1(A, N), (Tp(f) o SUC) o p2(A, N)) = 
  Pa(p1(A, N), Tp(f) o p2(A,N)) o Pa(p1(A,N),SUC o p2(A,N))’
 >-- (rw[o_assoc] >> irule Pa_o_split >> arw[]) >>
 arw[GSYM o_assoc] >> 
 qsspecl_then [‘f’] assume_tac Ev_of_Tp >> rfs[]
 )
(form_goal
 “!A B f:A * N ->B h: (A * N) * B ->B. isFun(f) & isFun(h) ==> !l . 
Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l
 ==>
 (h o Pa(id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N)) <=>
 Tp(h o l) o Pa(id(N),Tp(f)) = Tp(f) o SUC)”));


val Thm1_comm_eq_condition = prove_store(
"Thm1_comm_eq_condition",
e0
(rpt strip_tac >> 
 qsspecl_then [‘f’,‘h’] assume_tac Thm1_comm_eq_right >> rfs[] >>
 first_x_assum drule >> 
 qsspecl_then [‘f’,‘g’] (assume_tac o GSYM) Thm1_comm_eq_left >> rfs[])
(form_goal
 “!A B f: A * N ->B g:A->B h: (A * N) * B -> B. isFun(f) & isFun(h) & isFun(g) ==>
 !l.
 Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l ==>
 (f o Pa(p1(A,1),El(O) o p2(A,1)) = g o p1(A,1) & 
  h o Pa(id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N)) <=>
  Tp(f) o El(O) = Tp1(g) & Tp(h o l) o Pa(id(N),Tp(f)) = Tp(f) o SUC)
  ”));



val Thm1 = prove_store("Thm1",
e0
(rpt strip_tac >>
 abbrev_tac “Tp(g:A->B o p1(A,1)) = g'” >>
 abbrev_tac “Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l” >>
 abbrev_tac “Tp(h:(A * N) * B->B o l:A * N * Exp(A,B) -> (A * N) * B) = h'” >>
 qspecl_then [‘Exp(A,B)’,‘g'’,‘h'’] assume_tac Thm1_case_1 >> 
 qspecl_then [‘A’,‘1’] assume_tac p12_Fun >>
 qspecl_then [‘A’,‘N * Exp(A,B)’] assume_tac p12_Fun >>
 qspecl_then [‘A * N’] assume_tac id_Fun >>
 assume_tac SUC_Fun >>
 qspecl_then [‘A’,‘N’] assume_tac p12_Fun >>
 qspecl_then [‘N’,‘Exp(A,B)’] assume_tac p12_Fun >>
 qspecl_then [‘A’,‘B’] assume_tac Ev_Fun >>
 qsspecl_then [‘p2(A,N)’,‘SUC’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A,N)’,‘SUC o p2(A,N)’] assume_tac Pa_Fun >> rfs[] >>
 qspecl_then [‘N’] assume_tac id_Fun >> 
 qsspecl_then [‘p2(A, N * Exp(A, B))’,‘p2(N, Exp(A, B))’] 
 assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A, N * Exp(A, B))’,‘p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B))’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘Pa(p1(A, N * Exp(A, B)), p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B)))’,‘Ev(A,B)’] assume_tac o_Fun >>
 rfs[] >> 
 qsspecl_then [‘p2(A, N * Exp(A, B))’,‘p1(N, Exp(A, B))’]
 assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A, N * Exp(A, B))’,‘p1(N, Exp(A, B)) o p2(A, N * Exp(A, B))’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘Pa(p1(A, N * Exp(A, B)), p1(N, Exp(A, B)) o p2(A, N * Exp(A, B)))’,‘Ev(A, B) o
                Pa(p1(A, N * Exp(A, B)), p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B)))’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘l’,‘h’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘h o l’] assume_tac Tp_Fun >> rfs[] >> 
 qsspecl_then [‘p1(A,1)’,‘g’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘g o p1(A,1)’] assume_tac Tp_Fun >> rfs[] >>
 fs[] >>
 qpick_x_assum
 ‘?!f:N-> Exp(A,B).
   isFun(f) & f o El(O) = g' & f o SUC = h' o Pa(id(N), f)’
 (assume_tac o uex_expand) >>
 pop_assum (x_choose_then "fb" strip_assume_tac) >>
 qabbrev_tac ‘Ev(A,B) o Pa(p1(A,N),fb o p2(A,N)) = f’ >>
 qsspecl_then [‘p2(A,N)’,‘fb’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(A,N)’,‘fb o p2(A,N)’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘Pa(p1(A, N), fb o p2(A, N))’,‘Ev(A, B)’] 
 assume_tac o_Fun >> rfs[] >> 
 qsspecl_then [‘f’] assume_tac Tp_Fun >> rfs[] >>
 qsspecl_then [‘id(N)’,‘Tp(f)’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘h o l’] assume_tac Tp_Fun >> rfs[] >>
 qby_tac ‘Tp(f) = fb’ >--
 (fconv_tac (rewr_fconv (eq_sym "rel")) >> irule is_Tp >> arw[]) >>
 qexists_tac ‘f’ >> strip_tac >>
 assume_tac Thm1_comm_eq_condition >>
 qsuff_tac
 ‘(isFun(f0) & 
  Tp(f0) o El(O) = Tp1(g) &
                   Tp(h o l) o Pa(id(N), Tp(f0)) = Tp(f0) o SUC) <=>
  f0 = f’ 
 >-- (strip_tac >> dimp_tac >> disch_tac >--
     (first_x_assum (qsspecl_then [‘f0’,‘g’,‘h’] assume_tac) >>
     qby_tac ‘isFun(f0) & isFun(h) & isFun(g)’ >-- arw[] >>
     first_x_assum drule >> first_x_assum drule >>
     rfs[] >> first_x_assum (irule o iffLR) >> arw[]) >>
     arw[] >> 
     first_x_assum (qsspecl_then [‘f’,‘g’,‘h’] assume_tac) >>
     qby_tac ‘isFun(f) & isFun(h) & isFun(g)’ >-- fs[] >>
     first_x_assum drule >> first_x_assum drule >> arw[] >>
     arw[GSYM Tp1_def]) >>  
 qby_tac
 ‘Tp(f) o El(O) = Tp1(g) & 
  Tp((h o l)) o Pa(id(N), Tp(f)) = Tp(f) o SUC’
 >-- arw[GSYM Tp1_def] >>
 arw[] >> dimp_tac >> strip_tac
 >-- (irule $ iffLR Tp_eq >> arw[] >>
     first_x_assum irule >> pop_assum (assume_tac o GSYM) >> arw[] >>
     qpick_x_assum ‘Tp(f0) o El(O) = Tp1(g)’ (assume_tac o GSYM) >>
     arw[] >> fs[GSYM Tp1_def] >>
     irule Tp_Fun >> arw[]) >>
 arw[] >> fs[GSYM Tp1_def])
(form_goal
 “!A B g:A->B h:(A * N) * B ->B. isFun(g) & isFun(h) ==> 
 ?f:A * N ->B. !f0.(isFun(f0) &
   f0 o Pa(p1(A,1),El(O) o p2(A,1)) = g o p1(A,1) & 
  h o Pa(id(A * N),f0) = f0 o Pa(p1(A,N), SUC o p2(A,N))) <=> f0 = f”));

val PRE_ex = 
 Thm1_case_1 |> specl (List.map rastt ["N","El(O)","p1(N,N)"])
             |> undisch
             |> uex_expand |> disch_all
             |> rewr_rule[p1_Fun,p1_Fun,El_Fun]
             |> store_as "PRE_ex";

val PRE_def0 = PRE_ex |> ex2fsym0 "PRE" []
                     |> store_as "PRE_def0";



val PRE_def = prove_store("PRE_def",
e0
(assume_tac PRE_def0 >> 
 qspecl_then [‘N’] assume_tac id_Fun>>
 qsspecl_then [‘id(N)’,‘PRE’] assume_tac Pa_Fun >> rfs[] >> 
 irule p1_of_Pa >> arw[]
 )
(form_goal
 “isFun(PRE) &
        PRE o El(O) = El(O) & PRE o SUC = id(N) &
 !f:N->N.
  isFun(f) &
  f o El(O) = El(O) & f o SUC = p1(N, N) o Pa(id(N), f) ==> f = PRE”));

val PRE_Fun = PRE_def |> conjE1 |> store_as "PRE_Fun";

val Pre_ex = prove_store("Pre_ex",
e0
(strip_tac >> qexists_tac ‘Eval(PRE,n)’ >> rw[])
(form_goal
 “!n. ?pn. Eval(PRE,n) = pn”));

val Pre_def = Pre_ex |> spec_all |> ex2fsym0 "Pre" ["n"]
                     |> store_as "Pre_def";

val Suc_ex = prove_store("Suc_ex",
e0
(strip_tac >> qexists_tac ‘Eval(SUC,n)’ >> rw[])
(form_goal
 “!n.?sn. Eval(SUC,n) = sn”));

val Suc_def = Suc_ex |> spec_all |> ex2fsym0 "Suc" ["n"]


val lflip_tac = fconv_tac (land_fconv no_conv (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))))

(*lflip does not work...*)

val O_xor_Suc = prove_store("O_xor_Suc",
e0
(rw[O_xor_SUC,GSYM Suc_def] >> strip_tac >> dimp_tac >> strip_tac >>
 qexists_tac ‘pn’ >> arw[])
(form_goal
 “!n. ~(n = O) <=> ?pn. n = Suc(pn)”));

val Suc_eq_eq = prove_store("Suc_eq_eq",
e0
(assume_tac SUC_eq_eq >> fs[Suc_def])
(form_goal
 “!m n.Suc(m) = Suc(n) <=> m = n”));

val Pre_eqn = prove_store("PRE_eqn",
e0
(strip_assume_tac PRE_def >> pop_assum (K all_tac) >>
 qby_tac
 ‘Eval(PRE o El(O),dot) = Eval(El(O),dot)’ 
 >-- arw[] >> fs[El_def] >>
 qsspecl_then [‘El(O)’,‘PRE’,‘dot’] assume_tac $ GSYM o_Eval >>
 qsspecl_then [‘O’] assume_tac El_Fun >>
 assume_tac PRE_Fun >> fs[] >> fs[El_def] >> arw[GSYM Pre_def] >>
 strip_tac >>
 qby_tac ‘Eval(PRE o SUC,n) = Eval(id(N),n)’ 
 >-- arw[] >>
 qsspecl_then [‘SUC’,‘PRE’,‘n’] assume_tac o_Eval >>
 assume_tac SUC_Fun >> fs[] >> rfs[] >>
 fs[GSYM Suc_def,Eval_id])
(form_goal
 “Pre(O) = O & !n. Pre(Suc(n)) = n”));


local 
val l = proved_th $
e0
(irule o_Fun >> rw[SUC_Fun,p2_Fun])
(form_goal
 “isFun(SUC o p2(N * N,N))”)
in
val ADD_ex = 
 Thm1 |> sspecl (List.map rastt ["id(N)","SUC o p2(N * N,N)"])
      |> rewr_rule[id_Fun,l]
      |> store_as "ADD_ex";
end
        

val ADD_def0 = ADD_ex |> ex2fsym0 "ADD" []
                      |> store_as "ADD_def0";

val is_To1 = To1_def |> spec_all |> conjE2 |> gen_all
                     |> store_as "is_To1";

val To1_Fun = To1_def |> spec_all |> conjE1 |> gen_all
                     |> store_as "To1_Fun";

val ADD_property = prove_store("ADD_property",
e0
(assume_tac ADD_def0 >> 
 first_x_assum $ qspecl_then [‘ADD’] assume_tac >> fs[idL] >>
 qby_tac ‘p2(N,1) = To1(N * 1)’
 >-- (qspecl_then [‘N’,‘1’] assume_tac p12_Fun >> fs[] >>
     drule is_To1 >> arw[]) >>
 fs[o_assoc] >> 
 qby_tac
 ‘ADD o Pa(p1(N, 1), El(O) o To1(N * 1)) o Pa(id(N),To1(N)) = p1(N, 1) o Pa(id(N),To1(N))’
 >-- arw[GSYM o_assoc] >>
 qsspecl_then [‘id(N)’,‘To1(N)’] assume_tac p1_of_Pa >>
 fs[id_Fun,To1_Fun] >>
 qsspecl_then [‘p1(N,1)’,‘El(O) o To1(N * 1)’,‘Pa(id(N),To1(N))’]
 assume_tac $ Pa_distr' >>
 qspecl_then [‘N’] assume_tac id_Fun >>
 qspecl_then [‘N’] assume_tac To1_Fun >>
 qsspecl_then [‘id(N)’,‘To1(N)’] assume_tac Pa_Fun >> rfs[] >>
 qspecl_then [‘N * 1’] assume_tac To1_Fun>>
 qsspecl_then [‘O’] assume_tac El_Fun >>
 qsspecl_then [‘To1(N * 1)’,‘El(O)’] assume_tac o_Fun >> rfs[] >>
 qspecl_then [‘N’,‘1’] assume_tac p12_Fun >> fs[] >>
 fs[o_assoc] >>
 qsspecl_then [‘To1(N * 1) o Pa(id(N), To1(N))’] assume_tac is_To1 >>
 qby_tac ‘isFun(To1(N * 1) o Pa(id(N), To1(N)))’
 >-- (irule o_Fun >> rw[To1_Fun] >> irule Pa_Fun >> rw[To1_Fun,id_Fun])>>
 fs[])
(form_goal
 “isFun(ADD) & 
  ADD o Pa(id(N),El(O) o To1(N)) = id(N) & 
 ADD o Pa(p1(N,N),SUC o p2(N,N)) = SUC o p2(N * N,N) o Pa(id(N * N),ADD)”));


val ADD_Fun = ADD_property |> conjE1 |> store_as "ADD_Fun";

val ADD_El0 = ADD_property |> conjE2 |> store_as "ADD_El0";

val ADD_El = prove_store("ADD_El",
e0
(assume_tac ADD_property >> arw[] >>
 qsspecl_then [‘id(N * N)’,‘ADD’] assume_tac p2_of_Pa >>
 fs[id_Fun,ADD_Fun])
(form_goal
 “ADD o Pa(id(N),El(O) o To1(N)) = id(N) & 
  ADD o Pa(p1(N,N),SUC o p2(N,N)) = SUC o ADD”));

val Add_ex = prove_store("Add_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(ADD,Pair(m,n))’ >> rw[])
(form_goal
 “!m n. ?amn. Eval(ADD,Pair(m,n)) = amn”));

val Add_def = Add_ex |> spec_all |> ex2fsym0 "Add" ["m","n"] 
                     |> gen_all |> store_as "Add_def";

val Eval_input_eq =prove_store("Eval_input_eq",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!A B f:A->B a1 a2.a1 = a2 ==> Eval(f,a1) = Eval(f,a2)”))

val Eval_Pa_Pair = prove_store("Eval_Pa_Pair",
e0
(rpt strip_tac >>  irule Cross_eq >> rw[Pair_def] >> strip_tac >>
 irule $ iffLR Eval_o_l >> 
 qsspecl_then [‘f’,‘g’] assume_tac p12_of_Pa >> rfs[] >>
 rw[p12_Fun] >> irule Pa_Fun >> arw[])
(form_goal
 “!X A f:X->A B g:X->B. isFun(f) & isFun(g) ==>
  !x:mem(X).Eval(Pa(f,g),x) = Pair(Eval(f,x),Eval(g,x))”));

(* (∀n. 0 + n = n) ∧ ∀m n. SUC m + n = SUC (m + n)*)
val Add_O = prove_store("Add_O",
e0
(strip_tac >> fs[GSYM Add_def] >>
 assume_tac ADD_El >>
 qsuff_tac ‘Eval(ADD o Pa(id(N), El(O) o To1(N)),n) = Eval(ADD, Pair(n, O)) & Eval(id(N),n) = n’
 >-- (strip_tac >>rfs[]) >>
 rw[Eval_id] >> irule $iffRL Eval_o_l >> rw[ADD_Fun] >>
 qspecl_then [‘N’] assume_tac id_Fun >>
 qspecl_then [‘N’] assume_tac To1_Fun >>
 qsspecl_then [‘To1(N)’,‘El(O)’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘O’] assume_tac El_Fun >> fs[] >>
 qsspecl_then [‘id(N)’,‘El(O) o To1(N)’] assume_tac Pa_Fun >> rfs[] >>
 irule Eval_input_eq >> 
 (*irule with eval_pa does not work, some sort of irule at?*)
 qsspecl_then [‘id(N)’,‘El(O) o To1(N)’] assume_tac Eval_Pa_Pair >>
 rfs[] >> fs[Eval_id] >>
 rw[Pair_eq_eq] >> irule $ iffRL Eval_o_l >> arw[] >> rw[dot_def] >>
 rw[Eval_El])
(form_goal
 “!n. Add(n,O) = n”));



(* (∀n. 0 + n = n) ∧ ∀m n. SUC m + n = SUC (m + n)*)
val Add_O = prove_store("Add_O",
e0
(strip_tac >> fs[GSYM Add_def] >>
 assume_tac ADD_El >>
 qsuff_tac ‘Eval(ADD o Pa(id(N), El(O) o To1(N)),n) = Eval(ADD, Pair(n, O)) & Eval(id(N),n) = n’
 >-- (strip_tac >>rfs[]) >>
 rw[Eval_id] >> irule $iffRL Eval_o_l >> rw[ADD_Fun] >>
 qspecl_then [‘N’] assume_tac id_Fun >>
 qspecl_then [‘N’] assume_tac To1_Fun >>
 qsspecl_then [‘To1(N)’,‘El(O)’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘O’] assume_tac El_Fun >> fs[] >>
 qsspecl_then [‘id(N)’,‘El(O) o To1(N)’] assume_tac Pa_Fun >> rfs[] >>
 irule Eval_input_eq >> 
 (*irule with eval_pa does not work, some sort of irule at?*)
 qsspecl_then [‘id(N)’,‘El(O) o To1(N)’] assume_tac Eval_Pa_Pair >>
 rfs[] >> fs[Eval_id] >>
 rw[Pair_eq_eq] >> irule $ iffRL Eval_o_l >> arw[] >> rw[dot_def] >>
 rw[Eval_El])
(form_goal
 “!n. Add(n,O) = n”));


val Add_Suc = prove_store("Add_Suc",
e0
(rpt strip_tac >> assume_tac ADD_El >> fs[] >> last_x_assum (K all_tac) >>
 rw[GSYM Add_def,GSYM Suc_def] >>
 flip_tac >> irule $ iffLR Eval_o_l >> pop_assum (assume_tac o GSYM) >>
 arw[] >> rw[ADD_Fun,SUC_Fun] >> irule $ iffRL Eval_o_l >> 
 rw[ADD_Fun] >>
 qspecl_then [‘N’,‘N’] assume_tac p12_Fun >>
 qsspecl_then [‘p2(N,N)’,‘SUC’] assume_tac o_Fun >> rfs[] >>
 assume_tac SUC_Fun >> fs[] >>
 qsspecl_then [‘p1(N,N)’,‘SUC o p2(N,N)’] assume_tac Pa_Fun >>
 rfs[] >> irule Eval_input_eq >> 
 qsspecl_then [‘p1(N,N)’,‘SUC o p2(N,N)’] assume_tac Eval_Pa_Pair >>
 rfs[] >> rw[Pair_def] >> rw[Pair_eq_eq] >> 
 irule $ iffRL Eval_o_l >> arw[] >> irule Eval_input_eq >>
 rw[Pair_def])
(form_goal
 “(!m n.Add(m,Suc(n)) = Suc(Add(m,n)))”));

val Pre_O = conjE1 Pre_eqn |> store_as "Pre_O";

val Pre_Suc = conjE2 Pre_eqn |> store_as "Pre_Suc";

local
val l = proved_th $
e0
(irule o_Fun >> rw[PRE_def,p2_Fun])
(form_goal
 “isFun(PRE o p2(N * N,N))”)
in
val SUB_def0 = Thm1 |> specl
(List.map rastt ["N","N","id(N)","PRE o p2(N * N,N)"])
|> rewr_rule[id_Fun,l,idL] |> ex2fsym0 "SUB" [] |> store_as "SUB_def0"
end

val SUB_def0' = SUB_def0 |> specl [rastt "SUB"] |> rewr_rule[]

val SUB_Fun = SUB_def0' |> conjE1 |> store_as "SUB_Fun";




val o_eq_r = prove_store("o_eq_r",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!A B f1:A->B f2:A->B. f1 = f2 ==>
  !C g:B->C. g o f1 = g o f2”));


val SUB_El = prove_store("SUB_El",
e0
(strip_assume_tac SUB_def0' >> 
 qby_tac
 ‘SUB o Pa(p1(N, 1), El(O) o p2(N, 1)) o Pa(id(N),To1(N)) = p1(N, 1) o Pa(id(N),To1(N))’
 >-- arw[GSYM o_assoc] >>
 qspecl_then [‘N’] assume_tac id_Fun >>
 qspecl_then [‘N’] assume_tac To1_Fun >>
 qsspecl_then [‘id(N)’,‘To1(N)’] assume_tac Pa_Fun >> rfs[] >>
 qsspecl_then [‘id(N)’,‘To1(N)’] assume_tac p1_of_Pa >> rfs[] >>
 fs[] >> 
 qsspecl_then [‘O’] assume_tac El_Fun >>
 qspecl_then [‘N’,‘1’] assume_tac p12_Fun >>
 qsspecl_then [‘p2(N,1)’,‘El(O)’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(N,1)’,‘El(O) o p2(N,1)’,‘Pa(id(N),To1(N))’] assume_tac
 Pa_distr' >> rfs[] >> fs[] >> fs[o_assoc] >>
 qsspecl_then [‘id(N)’,‘To1(N)’] assume_tac p2_of_Pa >> rfs[] >> fs[] >> 
 qpick_x_assum 
 ‘PRE o p2(N * N, N) o Pa(id(N * N), SUB) = SUB o Pa(p1(N, N), SUC o p2(N, N))’ (assume_tac o GSYM) >>
 arw[] >> irule o_eq_r >>
 qsspecl_then [‘id(N * N)’,‘SUB’] assume_tac p2_of_Pa >> rfs[id_Fun])
(form_goal
 “SUB o Pa(id(N), El(O) o To1(N)) = id(N) &
 PRE o SUB = SUB o Pa(p1(N,N), SUC o p2(N,N))”));


val Sub_ex = prove_store("Sub_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(SUB,Pair(m,n))’ >> rw[])
(form_goal
 “!m n.?smn. Eval(SUB,Pair(m,n)) = smn”));

val Sub_def = Sub_ex |> spec_all |> ex2fsym0 "Sub" ["m","n"] 
                     |> gen_all |> store_as "Sub_def";

val Sub_O = prove_store("Sub_O",
e0
(strip_tac >> strip_assume_tac SUB_El >>
 pop_assum (K all_tac) >>
 qby_tac
 ‘Eval(SUB o Pa(id(N), El(O) o To1(N)),n) = Eval(id(N),n)’ 
 >-- arw[] >>
 fs[Eval_id] >> fs[GSYM Sub_def] >> 
 qsuff_tac
 ‘Eval(SUB o Pa(id(N), El(O) o To1(N)), n) = Eval(SUB, Pair(n, O))’ 
 >-- (strip_tac >> fs[]) >>
 irule $ iffRL Eval_o_l >> rw[SUB_Fun] >>
 qsspecl_then [‘O’] assume_tac El_Fun >> 
 qspecl_then [‘N’] assume_tac To1_Fun >> 
 qsspecl_then [‘To1(N)’,‘El(O)’] assume_tac o_Fun >> rfs[] >>
 qspecl_then [‘N’] assume_tac id_Fun >>
 qsspecl_then [‘id(N)’,‘El(O) o To1(N)’] assume_tac Pa_Fun >>
 rfs[] >> irule Eval_input_eq >>
 qsspecl_then [‘id(N)’,‘El(O) o To1(N)’] assume_tac Eval_Pa_Pair >>
 rfs[] >> rw[Pair_eq_eq] >> irule $ iffRL Eval_o_l >>
 arw[] >> rw[dot_def,El_def]
 )
(form_goal
 “!n. Sub(n,O) = n”));


val Sub_Suc = prove_store("Sub_Suc",
e0
(rpt strip_tac >> strip_assume_tac SUB_El >> last_x_assum (K all_tac) >>
 rw[GSYM Sub_def,GSYM Suc_def,GSYM Pre_def] >> 
 flip_tac >> irule $ iffLR Eval_o_l >> arw[] >>
 rw[PRE_Fun,SUB_Fun] >> 
 irule $ iffRL Eval_o_l >> rw[SUB_Fun] >>
 qspecl_then [‘N’,‘N’] assume_tac p12_Fun >>
 assume_tac SUC_Fun >>
 qsspecl_then [‘p2(N,N)’,‘SUC’] assume_tac o_Fun >> rfs[] >>
 qsspecl_then [‘p1(N,N)’,‘SUC o p2(N,N)’] assume_tac Pa_Fun >> rfs[] >>
 irule Eval_input_eq >> 
 qsspecl_then [‘p1(N,N)’,‘SUC o p2(N,N)’] assume_tac Eval_Pa_Pair >> 
 rfs[] >> rw[Pair_eq_eq] >> rw[Pair_def] >> irule $ iffRL Eval_o_l >>
 arw[] >> irule Eval_input_eq >> rw[Pair_def])
(form_goal
 “!m n. Sub(m,Suc(n)) = Pre(Sub(m,n))”));

val Pre_O_cases = prove_store("Pre_O_case",
e0
(strip_tac >> cases_on “n = O” >> arw[Pre_O] >>
 fs[O_xor_Suc] >> dimp_tac >> strip_tac (* 2 *)
 >> fs[Pre_Suc] >> fs[Suc_eq_eq])
(form_goal
 “!n. Pre(n) = O <=> (n = O | n = Suc(O))”));

val Pre_eq_O = Pre_O_cases

val _ = new_pred "Le" [("m",mem_sort N),("n",mem_sort N)]


val Le_def = store_ax("Le_def",“!m n.Le(m,n) <=> Sub(m,n) = O”);

val _ = new_pred "Lt" [("m",mem_sort N),("n",mem_sort N)]

val Lt_def = store_ax("Lt_def",“!m n.Lt(m,n) <=> (Le(m,n) & ~(m = n))”);

val SUB_EQ_00 = Le_def

val Le_O = prove_store("Le_O",
e0
(rw[Le_def,Sub_O])
(form_goal
 “!n. Le(n,O) ==> n = O”));


val Lt_Le = prove_store("Lt_Le",
e0
(once_rw[Lt_def] >> rpt strip_tac >> arw[])
(form_goal
 “!m n. Lt(m,n) ==> Le(m,n)”));

val Lt_NE = prove_store("Lt_NEQ",
e0
(rw[Lt_def] >> rpt strip_tac >> arw[])
(form_goal
 “!m n. Lt(m,n) ==> ~(m = n)”));

val Le_NE_Lt = prove_store("Le_NE_Lt",
e0
(rw[Lt_def])
(form_goal
 “!m n. Le(m,n) & ~(m = n) ==> Lt(m,n)”));

val Lt_Le_NE = Lt_def

val NOT_Lt_O = prove_store("NOT_Lt_O",
e0
(rw[Lt_def] >> rpt strip_tac  >> ccontra_tac  >> fs[] >> drule Le_O >> fs[])
(form_goal
 “!n.~(Lt(n,O))”));



local
val l = 
 fVar_Inst 
[("P",([("n",mem_sort N)],
 “Sub(Suc(m),Suc(n)) = Sub(m,n)”))] 
 N_ind_P 
in
val Sub_mono_eq = prove_store("Sub_mono_eq",
e0
(strip_tac >> irule l >> rw[Sub_O,Sub_Suc,Suc_def] >> 
 rpt strip_tac (* 2 *)
 >-- (pop_assum (assume_tac o GSYM) >> arw[]) >>
 rw[Pre_Suc])
(form_goal
 “!m n. Sub(Suc(m),Suc(n)) = Sub(m,n)”));
end

local
val l = 
 fVar_Inst 
[("P",([("c",mem_sort N)],
 “!a.Sub(Add(a,c),c) = a”))] 
 N_ind_P 
in
val Add_Sub = prove_store("Add_Sub",
e0
(rpt strip_tac >> match_mp_tac l >> rw[Suc_def,Add_Suc,Sub_mono_eq] >> 
 rw[Add_O,Sub_O])
(form_goal
 “!c a. Sub(Add(a,c),c) = a”));
end



local
val l = 
 fVar_Inst 
[("P",([("n",mem_sort N)],
 “Add(O,n) = n”))] 
 N_ind_P 
in
val Add_O2 = prove_store("Add_O2",
e0
(rpt strip_tac >> match_mp_tac l >> rw[Suc_def,Add_Suc,Add_O] >> 
 rpt strip_tac >> arw[])
(form_goal
 “!n. Add(O,n) = n”));
end

val Sub_EQ_O = prove_store("Sub_EQ_O",
e0
(rpt strip_tac >>
 qsspecl_then [‘n’,‘O’] assume_tac Add_Sub >> fs[Add_O2])
(form_goal
 “!n.Sub(n,n) = O”));

val Le_refl = prove_store("Le_refl",
e0
(rw[Le_def,Sub_EQ_O])
(form_goal
 “!n. Le(n,n)”));

val Le_O_O = Le_O;


val o_eq_l = prove_store("o_eq_l",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!B C g1:B->C g2:B->C. g1 = g2 ==>
  !A f:A->B. g1 o f = g2 o f”));

val Le_cases = prove_store("Le_cases",
e0
(rw[Lt_def] >> rpt strip_tac >> arw[] >> 
 cases_on “m:mem(N) = n” >> arw[])
(form_goal
 “!m n. Le(m,n) ==> (Lt(m,n) | m = n)”));

val Le_Sub = Le_def

(*“!p n m.((p <= n) /\ (p <= m)) ==> (((n - p) = (m - p)) = (n = m))”*)

val Suc_NONZERO = SUC_NONZERO |> rewr_rule[Suc_def]
                              |> store_as "Suc_NONZERO";

local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b c.Le(a,b) & Le(a,c) ==>(Sub(b,a) = Sub(c,a) <=> b = c)”))] 
N_ind_P
val l' = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “!c.Le(Suc(a), b) & Le(Suc(a), c) ==>
               (Sub(b, Suc(a)) = Sub(c, Suc(a)) <=> b = c)”))] 
N_ind_P |> gen_all |> specl [rastt "n:mem(N)"]
val l'' = 
 fVar_Inst 
[("P",([("c",mem_sort N)],
 “Le(Suc(n0), Eval(SUC, n1)) & Le(Suc(n0), c) ==>
               (Sub(Eval(SUC, n1), Suc(n0)) = Sub(c, Suc(n0)) <=>
                 Eval(SUC, n1) = c)”))] 
N_ind_P |> gen_all |> specl [rastt "n:mem(N)",rastt "n':mem(N)"]
in
val cancel_Sub = prove_store("cancel_Sub",
e0
(match_mp_tac l >> rw[Sub_O] >> rw[Suc_def] >> 
 strip_tac >> strip_tac >> 
 match_mp_tac l' >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> fs[Le_Sub,Sub_O,Suc_NONZERO]) >>
 strip_tac>> strip_tac >> 
 match_mp_tac l'' >> rw[Suc_def] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> fs[Le_def,Sub_O,Suc_NONZERO]) >>
 rw[Sub_mono_eq,Le_def] >> rpt strip_tac >> rw[Suc_eq_eq] >>
 first_x_assum irule >> arw[Le_def])
(form_goal
 “!a b c.Le(a,b) & Le(a,c) ==>(Sub(b,a) = Sub(c,a) <=> b = c)”));
end

local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “Sub(O,a) = O”))] 
N_ind_P
in
val Sub_of_O = prove_store("Sub_of_O",
e0
(match_mp_tac l >> rw[Sub_O,Sub_Suc,Suc_def] >> rpt strip_tac>>
 arw[Pre_O])
(form_goal
 “!n.Sub(O,n) = O”));
end

val O_LESS_EQ = prove_store("O_LESS_EQ",
e0
(rw[Le_def,Sub_of_O])
(form_goal
 “!x. Le(O,x)”));

val LESS_EQ_MONO = prove_store("LESS_EQ_MONO",
e0
(rw[Le_def,Sub_mono_eq])
(form_goal
 “!m n. Le(Suc(m),Suc(n)) <=> Le(m,n)”));


val LESS_O = prove_store("LESS_O",
e0
(rw[Lt_def,GSYM Suc_NONZERO,O_LESS_EQ])
(form_goal
 “!n. Lt(O,Suc(n))”));

val LESS_MONO_EQ = prove_store("LESS_MONO_EQ",
e0
(rw[Lt_def,LESS_EQ_MONO,Suc_eq_eq])
(form_goal
 “!m n. Lt(Suc(m),Suc(n)) <=> Lt(m,n)”));


val LE_O_iff = prove_store("LE_O_iff",
e0
(strip_tac >> dimp_tac >> strip_tac  
 >-- (drule Le_O>> arw[]) >>
 arw[Le_def,Sub_O])
(form_goal
 “!n. Le(n,O) <=> n = O”));


local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b. Lt(a,b) | Le(b,a)”))] 
N_ind_P
val l' = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “Lt(Suc(a),b) | Le(b,Suc(a))”))] 
N_ind_P |> gen_all |> specl [rastt "n:mem(N)"]
in
val LESS_cases = prove_store("LESS_cases",
e0
(rpt strip_tac >> irule l >> rw[Suc_def,O_LESS_EQ] >> strip_tac 
 >-- (strip_tac >> strip_tac >> match_mp_tac l' >>
     rw[O_LESS_EQ] >> rw[Suc_def,LESS_MONO_EQ,LESS_EQ_MONO] >> arw[]) >>
 rw[LE_O_iff] >> rw[Lt_def,O_LESS_EQ] >> strip_tac >>
 cases_on “O = b'” >> arw[])
(form_goal
 “!a b. Lt(a,b) | Le(b,a)”));
end

val LESS_EQ_cases = prove_store("LESS_EQ_cases",
e0
(assume_tac LESS_cases >> fs[Lt_def] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘m’,‘n’] strip_assume_tac) >> arw[])
(form_goal
 “!m n. Le(m,n) | Le(n,m)”));

local
val l = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “!a. Add(Suc(a),b) = Suc(Add(a,b))”))] 
N_ind_P
in
val Add_Suc1 = prove_store("Add_Suc1",
e0
(rpt strip_tac >> irule l >> strip_tac >> rw[Add_O] >>
 rpt strip_tac >> rw[Suc_def] >> rw[Add_Suc] >> arw[])
(form_goal
 “!b a. Add(Suc(a),b) = Suc(Add(a,b))”));
end


local
val l = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “!a. Add(a,b) = Add(b,a)”))] 
N_ind_P
in
val Add_sym = prove_store("Add_sym",
e0
(rpt strip_tac >> irule l >> rw[Add_O,Add_O2] >> rpt strip_tac >>
 rw[Suc_def] >> rw[Add_Suc] >> arw[] >> rw[Add_Suc1] )
(form_goal
 “!b a. Add(a,b) = Add(b,a)”));
end

val Suc_Sub = prove_store("Suc_Sub",
e0
(strip_tac >> qspecl_then [‘n’,‘Suc(O)’] assume_tac Add_Sub >> 
 fs[Add_Suc1,Add_O,Add_O2])
(form_goal “!n.Sub(Suc(n),n) = Suc(O)”));




val Sub_DIFF_1 = prove_store("Sub_DIFF_1",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule $ iffLR cancel_Sub >> qexists_tac ‘b’ >>
      assume_tac Suc_Sub >> once_arw[] >> rw[] >>
      qsuff_tac ‘~(Le(a,b)) & ~ (Le(Suc(b),b))’ 
      >-- (strip_tac >> assume_tac LESS_EQ_cases >> 
          first_assum (qspecl_then [‘a’,‘b’] assume_tac) >> fs[] >>
          first_assum (qspecl_then [‘Suc(b)’,‘b’] assume_tac) >> fs[]) >>
      rw[Le_def] >> arw[Suc_Sub] >> rw[Suc_NONZERO]) >>
 arw[] >> rw[Suc_Sub])
(form_goal
 “!a b.Sub(a,b) = Suc(O) <=> a = Suc(b)”));


val Pre_O_cases = prove_store("Pre_O_cases",
e0
(rw[GSYM Pre_def]  >> assume_tac PRE_def >> strip_tac >>
 cases_on “n = O” >-- (arw[] >>
 qsuff_tac ‘ Eval(PRE,O) = Eval(PRE o El(O),dot) &  Eval(El(O),dot) = O’
  >-- (rpt strip_tac >> arw[]) >> rw[El_def] >>
  flip_tac >> irule $ iffRL Eval_o_l >> rw[PRE_Fun,El_Fun,El_def]) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[O_xor_SUC] >> 
     qpick_x_assum ‘Eval(SUC, pn) = n’ (assume_tac o GSYM) >>
     fs[] >>
     rw[GSYM Suc_def] >> rw[SUC_eq_eq] >>
     qsuff_tac ‘Eval(PRE, Eval(SUC, pn)) = pn’ >--
     (strip_tac >> arw[] >>
     qpick_x_assum ‘Eval(PRE, Eval(SUC, pn)) = O’ (assume_tac o GSYM) >>
     arw[]) >> irule $ iffLR Eval_o_l >> arw[Eval_id,SUC_Fun,PRE_Fun]) >>
 arw[] >>
 rw[GSYM Suc_def] >> irule $ iffLR Eval_o_l >> 
 arw[Eval_id,SUC_Fun,PRE_Fun])
(form_goal
“!n. Pre(n) = O <=> (n = O | n = Suc(O))”));

val Sub_Suc_O_cases = prove_store("Sub_Suc_O_cases",
e0
(rpt strip_tac >> fs[Sub_Suc,Pre_O_cases,Sub_DIFF_1])
(form_goal
 “!a b. Sub(a,Suc(b)) = O ==> a = Suc(b) | Sub(a,b) = O”));

val Le_cases_iff = prove_store("LE_cases_iff",
e0
(rw[Lt_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[Le_refl] >>
 cases_on “a = b:mem(N)” >> arw[])
(form_goal
 “!a b. Le(a,b) <=> Lt(a,b) | a = b”));

val Sub_EQ_O1 = GSYM Le_def

val Lt_Suc_Le = prove_store("Lt_Suc_Le",
e0
(rw[Le_cases_iff] >> rw[Lt_def,Le_def,Sub_Suc,Pre_O_cases,Sub_DIFF_1] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] (* 4 *)
 >-- (cases_on “a = b:mem(N)” >> arw[]) 
 >-- (ccontra_tac >> fs[Suc_Sub] >> fs[Suc_NONZERO]) 
 >-- (disj1_tac >> rw[GSYM Le_def,Le_refl]) >>
 qspecl_then [‘Suc(b)’,‘b’] assume_tac Sub_DIFF_1 >> fs[] >>
 ccontra_tac >> pop_assum (assume_tac o GSYM) >> fs[] >>
 fs[Sub_EQ_O] >> qpick_x_assum ‘O = Suc(O)’ (assume_tac o GSYM) >>
 fs[Suc_NONZERO])
(form_goal
 “!a b. Lt(a,Suc(b)) <=> Le(a,b)”));




fun thml_eq_pairs (th:thm,(ll,rl,asml)) = 
    if is_eq (concl th) then  
        let 
            val (l,r) = dest_eq (concl th)
            val asm = ant th
        in 
            (l::ll,r::rl,asml_U [asm,asml])
        end
    else 
        raise ERR ("thml_eq_pairs.input thm is not an equality: ",
                   [],[],[concl th])


fun EQ_fVar P thml = 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in 
            mk_thm (contl_U (List.map cont thml),asml,
                 mk_dimp (mk_fvar P ll) (mk_fvar P rl))
        end

val NOT_Lt_O = prove_store("NOT_Lt_O",
e0
(rw[Lt_def] >> rpt strip_tac >> ccontra_tac >>
 pop_assum (strip_assume_tac) >> drule Le_O >> fs[])
(form_goal
 “!n. ~(Lt(n,O))”));





local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!a0. Le(a0,a) ==> P(a0)”))] 
N_ind_P
in
val strong_ind = prove_store("strong_ind",
e0
(rpt strip_tac >>
 suffices_tac
 “!a:mem(N). (!a0:mem(N). Le(a0,a) ==> P(a0))”
 >-- (strip_tac >> 
      pop_assum (qspecl_then [‘a:mem(N)’,‘a’] assume_tac) >>
      first_assum irule >> rw[Le_refl]) >>
 match_mp_tac l >> rw[Suc_def] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> drule Le_O >>  
      assume_tac $ EQ_fVar "P" [assume “a0' = O”] >>
      first_assum $ irule o iffRL >>
      first_assum irule >> rpt strip_tac >>
      pop_assum mp_tac >> rw[NOT_Lt_O]) >>
 rpt strip_tac >> drule Le_cases >> pop_assum mp_tac >>
 rw[Lt_Suc_Le] >> strip_tac
 >-- (first_assum irule >> first_assum accept_tac) >>
 assume_tac $ EQ_fVar "P" [assume “a0' = Suc(n)”] >>
 first_assum $ irule o iffRL >>
 last_x_assum irule  >> rw[Lt_Suc_Le] >> first_x_assum accept_tac)
(form_goal
 “(!a:mem(N).(!a0. Lt(a0,a) ==> P(a0)) ==> P(a)) ==> !a:mem(N). P(a)”));
end


local
val l = 
 fVar_Inst 
[("P",([("n",mem_sort N)],
 “!n0.Le(n0,n) ==> ~(P(n0:mem(N)))”))] 
N_ind_P
in
val WOP = prove_store("WOP",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac ‘!l:mem(N). P(l) ==> ?n:mem(N). P(n) & ~(Le(l,n))’
 >-- (rpt strip_tac >> ccontra_tac >>
      qsuff_tac ‘?a0:mem(N). P(a0) & !a1:mem(N). P(a1)==> Le(a0,a1)’ 
     >-- (rw[]>> first_x_assum accept_tac) >>
     qexists_tac ‘l’ >> strip_tac (* 2 *)
     >-- first_x_assum accept_tac >>
     rpt strip_tac >> ccontra_tac >>
     qby_tac ‘?n:mem(N). P(n) & ~(Le(l,n))’ 
     >-- (qexists_tac ‘a1’ >> strip_tac >> first_x_assum accept_tac) >>
     first_x_assum opposite_tac ) >>
 qsuff_tac ‘!n:mem(N). ~(P(n))’ >-- (rpt strip_tac >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >> 
 first_x_assum opposite_tac) >>
 qsuff_tac ‘!n:mem(N) n0:mem(N). Le(n0,n) ==> ~P(n0)’
 >-- (strip_tac >> rpt strip_tac >> first_x_assum irule >>
     qexists_tac ‘n’ >> rw[Le_refl]) >>
 match_mp_tac l >> rpt strip_tac (* 2 *) >--
 (drule Le_O >>
 assume_tac $ EQ_fVar "P" [assume “n0' = O”] >>
 ccontra_tac >> 
 first_x_assum $ drule o iffLR >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >> pop_assum mp_tac >> 
 rw[Le_def,Sub_of_O]) >>
 pop_assum mp_tac >> rw[Suc_def] >> strip_tac >>
 drule Le_cases >> pop_assum mp_tac >> rw[Lt_Suc_Le] >> strip_tac (* 2 *)
 >-- (first_x_assum drule >> first_x_assum accept_tac) >>
 ccontra_tac >>
 assume_tac $ EQ_fVar "P" [assume “n0' = Suc(n')”] >>
 first_x_assum $ drule o iffLR >> 
 last_x_assum drule >> pop_assum strip_assume_tac >>
 qspecl_then [‘n’,‘Suc(n')’] assume_tac LESS_cases >>
 cases_on “Lt(n,Suc(n'))” >--
 (pop_assum mp_tac >> rw[Lt_Suc_Le] >> ccontra_tac >> first_x_assum drule>>
 first_x_assum opposite_tac) >>
 pop_assum mp_tac >> pop_assum strip_assume_tac >> strip_tac 
 )
(form_goal
 “!a. P(a:mem(N)) ==> ?a0. P(a0) & !a1.P(a1) ==> Le(a0,a1)”));
end

local 
val precond = proved_th $
e0
(strip_tac >-- (irule o_Fun >> rw[To1_Fun,El_Fun]) >>
 irule o_Fun >> rw[ADD_Fun] >> irule Pa_Fun >>
 rw[p12_Fun] >> irule o_Fun >> rw[p1_Fun])
(form_goal “isFun(El(O) o To1(N)) &
      isFun(ADD o Pa(p2(N * N, N), p1(N, N) o p1(N * N, N))) ”)
in
val MUL_def0 = Thm1 |> allE $ rastt "N" 
                |> allE $ rastt "N" 
                |> allE $ rastt "El(O) o To1(N)"
                |> allE $ rastt "ADD o Pa(p2(N * N,N),p1(N, N) o p1(N * N,N))"|> C mp precond |>  ex2fsym0 "MUL" [] |> iffRL
                |> allE (rastt "MUL") |> rewr_rule[] 
                |> rewr_rule[o_assoc]
                |> store_as "MUL_def0";
end

val MUL_Fun = MUL_def0 |> conjE1 |> store_as "MUL_Fun";

val MUL_def = prove_store("MUL_def",
e0
(rw[MUL_def0] >> irule o_eq_r >>
 irule is_To1>> irule o_Fun >> rw[To1_Fun,p1_Fun])
(form_goal
 “MUL o Pa(p1(N, 1), El(O) o p2(N, 1)) = El(O) o To1(N * 1) &
      ADD o Pa(p2(N * N, N), (p1(N, N) o p1(N * N, N))) o
        Pa(id(N * N), MUL) = MUL o Pa(p1(N, N), SUC o p2(N, N))”));


val Mul_ex = prove_store("Mul_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(MUL,Pair(a,b))’ >> rw[])
(form_goal “!a b.?ab. Eval(MUL,Pair(a,b)) = ab”));

val Mul_def = Mul_ex |> spec_all |> ex2fsym0 "Mul" ["a","b"]
                     |> gen_all |> store_as "Mul_def";

val Eval_Pa2 = Eval_Pa |> sspecl [rastt "id(A)",rastt "g:B->D"]
                       |> rewr_rule[id_Fun,idL]
                       |> undisch 
                       |> gen_all |> disch_all 
                       |> gen_all
                       |> store_as "Eval_Pa2";

val Eval_p1_Pair = prove_store("Eval_p1_Pair",
e0
(rw[Fst_def,Pair_def'])
(form_goal
 “!A B a b. Eval(p1(A,B),Pair(a,b)) = a”));


val Eval_p2_Pair = prove_store("Eval_p2_Pair",
e0
(rw[Snd_def,Pair_def'])
(form_goal
 “!A B a b. Eval(p2(A,B),Pair(a,b)) = b”));

val Mul_O = prove_store("Mul_O",
e0
(strip_tac >> rw[GSYM Mul_def] >> 
 assume_tac MUL_def >>
 qby_tac
 ‘Eval(MUL, Pair(n, O)) = 
  Eval(MUL o Pa(p1(N, 1), El(O) o p2(N, 1)), 
       Pair(n,dot))’ 
 >-- (flip_tac >> irule $ iffRL Eval_o_l >> 
     rw[MUL_Fun] >> 
     qsspecl_then [‘O’] assume_tac El_Fun >>
     drule Eval_Pa2 >> arw[] >> rw[Eval_p1_Pair] >>
     strip_tac >--
     (irule Eval_input_eq >> rw[Pair_eq_eq] >>
     irule $ iffRL Eval_o_l >> rw[El_Fun,p2_Fun] >>
     rw[Eval_p2_Pair] >> rw[El_def]) >>
     irule Pa_Fun >> rw[p1_Fun] >>
     irule o_Fun >> rw[El_Fun,p2_Fun]) >>
 arw[] >> irule $ iffRL Eval_o_l >> 
 rw[dot_def,El_def,To1_Fun])
(form_goal “!n. Mul(n,O) = O”));


val Mul_Suc = prove_store("Mul_Suc",
e0
(rpt strip_tac >> rw[GSYM Mul_def,GSYM Suc_def] >>
 assume_tac MUL_def >>
 qby_tac
 ‘Eval(MUL, Pair(n, Eval(SUC, n0))) = 
  Eval(MUL o Pa(p1(N, N), SUC o p2(N, N)),Pair(n,n0))’
 >-- (flip_tac >> irule $ iffRL Eval_o_l >> rw[MUL_Fun] >>
     strip_tac >-- (irule Eval_input_eq >> 
     assume_tac SUC_Fun >> drule Eval_Pa2 >> arw[] >>
     rw[Eval_p1_Pair,Pair_eq_eq] >> irule $ iffRL Eval_o_l >>
     rw[Eval_p2_Pair,p2_Fun,SUC_Fun]) >>
     irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >> rw[SUC_Fun,p2_Fun]) >>
 arw[] >> 
 last_x_assum (assume_tac o GSYM) >> arw[] >>
 irule $ iffRL Eval_o_l >> rw[ADD_Fun] >> strip_tac 
 >-- (qspecl_then [‘N * N’,‘N’] assume_tac p2_Fun >> drule Pa_distr >>
     qby_tac ‘isFun(p1(N,N) o p1(N * N,N))’
     >-- (irule o_Fun >> rw[p1_Fun]) >>
     first_x_assum drule >> 
     qby_tac ‘isFun(Pa(id(N * N),MUL))’
     >-- (irule Pa_Fun >> rw[id_Fun,MUL_Fun]) >>
     first_x_assum drule >> arw[] >>
     rw[GSYM Add_def] >> irule Eval_input_eq >>
     qby_tac ‘isFun(id(N * N)) & isFun(MUL)’
     >-- rw[id_Fun,MUL_Fun] >> drule p2_of_Pa>> arw[] >>
     rw[o_assoc] >>
     drule p1_of_Pa >> arw[] >> rw[idR] >> 
     qby_tac ‘isFun(MUL) & isFun(p1(N,N))’ 
     >-- rw[MUL_Fun,p1_Fun] >> drule Eval_Pa_Pair >> arw[] >>
     rw[Eval_p1_Pair]) >>
 irule o_Fun >> strip_tac (* 2 *)
 >-- (irule Pa_Fun >> rw[p2_Fun] >> irule o_Fun >> rw[p1_Fun]) >>
 irule Pa_Fun >> rw[MUL_Fun,id_Fun])
(form_goal “!n n0. Mul(n,Suc(n0)) = Add(Mul(n,n0),n)”));


local
val l = 
 fVar_Inst 
[("P",([("n",mem_sort N)],
 “Mul(O,n) = O”))] 
 N_ind_P 
in
val Mul_LEFT_O = prove_store("Mul_LEFT_O",
e0
(irule l >> rw[Suc_def,Mul_O,Mul_Suc,Add_O])
(form_goal “!m. Mul(O,m) = O”));
end

local
val l = 
 fVar_Inst 
[("P",([("n",mem_sort N)],
 “Mul(Suc(O),n) = n”))] 
 N_ind_P 
in
val Mul_LEFT_1 = prove_store("Mul_LEFT_1",
e0
(irule l >> rw[Suc_def,Mul_O,Mul_Suc] >> rpt strip_tac >>
 arw[Add_Suc,Add_O])
(form_goal “!m.Mul(Suc(O),m) = m”));
end

val Mul_RIGHT_1 = prove_store("Mul_RIGHT_1",
e0
(rw[Mul_Suc,Add_O2,Mul_O])
(form_goal “!m. Mul(m,Suc(O)) = m”));

val Add_sym' = GSYM Add_sym |> store_as "Add_sym'";



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

val Add_eq_eq = prove_store("Add_eq_eq",
e0
(rpt strip_tac >> 
 qby_tac
 ‘Sub(Add(m,a),a) = Sub(Add(n,a),a)’
 >-- arw[] >>
 fs[Add_Sub])
(form_goal
 “!m n a. Add(m,a) = Add(n,a) ==> m = n”));


local
val l = 
 fVar_Inst 
[("P",([("m",mem_sort N)],
 “!a. Mul(Suc(a),m) = Add(m,Mul(a,m))”))] 
 N_ind_P 
in
val Mul_Suc1 = prove_store("Mul_Suc1",
e0
(irule l >> 
 rw[Mul_O,Add_O] >> rw[Suc_def,Mul_Suc] >> rpt strip_tac >>
 arw[] >> arw[Add_Suc] >>
 qsspecl_then [‘Suc(n')’,‘ Add(Mul(a, n'), a)’] assume_tac Add_sym' >> 
 arw[Add_Suc] >> 
 qsspecl_then [‘n'’,‘Mul(a,n')’] assume_tac Add_sym' >> arw[] >>
 rw[GSYM Add_assoc] >> 
 qsspecl_then [‘n'’,‘a’] assume_tac Add_sym' >> arw[]
 )
(form_goal
 “!m n. Mul(Suc(n),m) = Add(m,Mul(n,m))”));
end


val Mul_clauses = prove_store("Mul_clauses",
e0
(rw[Mul_O,Mul_Suc,Mul_Suc1,Mul_LEFT_1,Mul_RIGHT_1,Mul_LEFT_O] >>
 rpt strip_tac >--
 qsspecl_then [‘n’,‘Mul(m,n)’] accept_tac Add_sym' >> 
 qsspecl_then [‘Mul(m,n)’,‘m’] accept_tac Add_sym')
(form_goal “!m. (Mul(O,m) = O) & (Mul(m,O) = O) & 
                  (Mul(Suc(O),m) = m) & (Mul(m,Suc(O)) = m) &
                  !n.(Mul(Suc(m),n) = Add(Mul(m,n),n)) &
                  (Mul(m,Suc(n)) = Add(m,Mul(m,n)))”));


local
val l = 
 fVar_Inst 
[("P",([("m",mem_sort N)],
 “!n. Mul(m,n) = Mul(n,m)”))] 
 N_ind_P
in
val Mul_sym = prove_store("Mul_sym",
e0
(irule l >> rw[Mul_clauses,Suc_def] >>
 rpt strip_tac >> arw[] >>
 qsspecl_then [‘Mul(n'',n')’,‘n''’] accept_tac Add_sym')
(form_goal
 “!m n. Mul(m,n) = Mul(n,m)”));
end

val Add_clauses = prove_store("Add_clauses",
e0
(rw[Add_O,Add_O2,Add_Suc,Add_Suc1])
(form_goal “(!m. Add(O,m) = m & Add(m,O) = m) & 
            !m n.Add(Suc(m),n) = Suc(Add(m,n)) &
                 Add(m,Suc(n)) = Suc(Add(m,n))”));



local
val l = 
 fVar_Inst 
[("P",([("p",mem_sort N)],
 “Mul(Add(a,b),p) = Add(Mul(a,p),Mul(b,p))”))] 
 N_ind_P
in
val RIGHT_DISTR = prove_store("RIGHT_DISTR",
e0
(strip_tac >> strip_tac >> irule l >> rw[Mul_clauses,Add_clauses] >>
 rw[Suc_def] >> strip_tac >> arw[] >>
 rw[Mul_clauses,Add_clauses,GSYM Add_assoc] >> strip_tac >>
 arw[]>> 
 qsuff_tac ‘Add(n, Add(Mul(m, n'), Mul(n, n'))) = 
            Add(Mul(m, n'), Add(n, Mul(n, n')))’ 
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘Mul(m, n')’,‘Add(n, Mul(n, n'))’] assume_tac Add_sym' >>
 arw[] >> 
 rw[GSYM Add_assoc] >>
 qsspecl_then [‘Mul(m, n')’,‘Mul(n, n')’] assume_tac Add_sym' >> arw[]
 )
(form_goal “!m n p. Mul(Add(m,n),p) = Add(Mul(m,p),Mul(n,p))”));
end


val LEFT_DISTR = prove_store("LEFT_DISTR",
e0
(rpt strip_tac >>
 qsspecl_then [‘p’,‘Add(m,n)’] assume_tac Mul_sym >> arw[RIGHT_DISTR] >>
 qsspecl_then [‘p’,‘m’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘p’,‘n’] assume_tac Mul_sym >> arw[])
(form_goal “!m n p. Mul(p,Add(m,n)) = Add(Mul(p,m),Mul(p,n))”));


local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b p. Mul(a,Mul(b,p)) = Mul(Mul(a,b),p)”))] 
 N_ind_P
in
val Mul_assoc = prove_store("Mul_assoc",
e0
(irule  l >>
 rw[Mul_clauses,RIGHT_DISTR,Suc_def] >> rpt strip_tac >>
 arw[] >> rw[GSYM Add_assoc])
(form_goal “!m n p. Mul(m,Mul(n,p)) = Mul(Mul(m,n),p)”));
end


local 
val l1 = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”))] 
 N_ind_P 
val l2 = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “!c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”))] 
 N_ind_P |> rewr_rule[Suc_def]
val l3 = 
 fVar_Inst 
[("P",([("c",mem_sort N)],
 “Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”))] 
 N_ind_P |> rewr_rule[Suc_def]
in
val Sub_Add = prove_store("SUB_Add",
e0
(strip_tac >> match_mp_tac l1 >> rw[Sub_of_O] >> strip_tac >>
 strip_tac >> rw[Suc_def] >> strip_tac >> match_mp_tac l2 >>
 rw[Add_O2,Sub_O] >> strip_tac >> strip_tac >>
 match_mp_tac l3 >> rw[Sub_O,Add_O] >> rpt strip_tac >>
 rw[Add_Suc1] >> rw[Sub_mono_eq] >> arw[])
(form_goal “!a b c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”));
end

val Le_O_iff = prove_store("Le_O_iff",
e0
(strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (drule Le_O >> arw[]) >>
 arw[O_LESS_EQ])
(form_goal “!a. Le(a,O) <=> a = O”));

val Le_Suc = prove_store("Le_Suc",
e0
(rpt strip_tac >> drule Le_cases >> 
 pop_assum strip_assume_tac (* 2 *)
 >-- (drule $ iffLR Lt_Suc_Le >> arw[]) >>
 arw[])
(form_goal “!a b. Le(a,Suc(b)) ==> (Le(a,b) | a = Suc(b))”));

local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b.  Le(b,a) ==> ?p. Add(p,b) = a”))] 
 N_ind_P 
in
val Le_Add_ex = prove_store("Le_Add_ex",
e0
(strip_tac >> match_mp_tac l >> rw[Suc_def,Le_O_iff] >>
 rpt strip_tac (* 2 *)
 >-- (arw[] >> qexists_tac ‘O’ >> rw[Add_O]) >>
 rpt strip_tac >> drule Le_Suc >> 
 pop_assum strip_assume_tac 
 >-- (first_x_assum drule >> 
     pop_assum strip_assume_tac >>
     qexists_tac ‘Suc(p)’ >> arw[Add_Suc1]) >>
 arw[] >> qexists_tac ‘O’ >> rw[Add_O2])
(form_goal
 “!m n. Le(n,m) ==> ?p. Add(p,n) = m”));
end


val LE_def = 
fVar_Inst 
[("P",([("m",mem_sort N),("n",mem_sort N)],
 “Sub(m,n) = O”))] 
(AX1 |> qspecl [‘N’, ‘N’] |> uex_expand)
|> ex2fsym0 "LE" [] |> conjE1
|> store_as "LE_def";


val LT_def = 
fVar_Inst 
[("P",([("m",mem_sort N),("n",mem_sort N)],
 “Holds(LE,m,n) & ~(m = n)”))] 
(AX1 |> qspecl [‘N’, ‘N’] |> uex_expand)
|> ex2fsym0 "LT" [] |> conjE1
|> store_as "LT_def";

val LE_Le = prove_store("LE_Le",
e0
(rw[LE_def,Le_def])
(form_goal “!a b. Holds(LE,a,b) <=> Le(a,b)”));


val LT_Lt = prove_store("LT_Lt",
e0
(rw[LT_def,Lt_def,LE_Le])
(form_goal “!a b. Holds(LT,a,b) <=> Lt(a,b)”));

(*a <= b <=> ?c. a + c = b
  a <= 0 , the c is 0.
  a <= suc n. *)

val LE_Trans = prove_store("LE_Trans",
e0
(rw[Trans_def,LE_Le] >> rpt strip_tac >>
 rw[Le_def] >> drule Le_Add_ex >>
 pop_assum (strip_assume_tac o GSYM) >> arw[] >>
 qsspecl_then [‘a2’,‘p’] assume_tac Add_sym >> 
 once_arw[] >> rw[Sub_Add] >> fs[Le_def] >>
 rw[Sub_of_O])
(form_goal “Trans(LE)”));


local
val l = 
 fVar_Inst 
[("P",([("p",mem_sort N)],
 “Lt(a,b) <=> Lt(Add(a,p),Add(b,p))”))] 
 N_ind_P 
in
val LESS_MONO_ADD = prove_store("LESS_MONO_ADD",
e0
(strip_tac >> strip_tac >> match_mp_tac l >>
 rw[Suc_def] >> rw[Add_O,Add_Suc,LESS_MONO_EQ])
(form_goal “!m n p. Lt(m,n) <=> Lt(Add(m,p),Add(n,p))”));
end

local
val l = 
 fVar_Inst 
[("P",([("p",mem_sort N)],
 “(Add(a,p) = Add(b,p)) <=> a = b”))] 
 N_ind_P 
in
val EQ_MONO_ADD_EQ = prove_store("EQ_MONO_ADD_EQ",
e0
(strip_tac >> strip_tac >> match_mp_tac l >>
 rw[Add_O,Suc_def,Add_Suc] >> rpt strip_tac >>
 arw[Suc_eq_eq])
(form_goal “!m n p.(Add(m,p) = Add(n,p)) <=> m = n”));
end

val LESS_MONO_ADD_EQ = GSYM LESS_MONO_ADD
                            |> store_as 
                            "LESS_MONO_ADD_EQ";

val LESS_OR_EQ = prove_store("LESS_OR_EQ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >--
 (drule Le_cases >> arw[]) 
 >-- fs[Lt_def] >>
 arw[Le_def,Sub_EQ_O])
(form_goal “Le(m,n)<=> (Lt(m,n) | m = n)”));


val LESS_EQ_MONO_ADD_EQ = prove_store("LESS_EQ_MONO_ADD_EQ",
e0
(rw[LESS_OR_EQ,LESS_MONO_ADD_EQ,EQ_MONO_ADD_EQ])
(form_goal “!m n p. Le(Add(m,p),Add(n,p)) <=> Le(m,n)”));


val Le_trans = LE_Trans |> rewr_rule[Trans_def,LE_Le]



val Le_Add = prove_store("Le_Add",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(a,d)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘b’,‘a’] assume_tac Add_sym >>
 arw[] >>
 qsspecl_then [‘d’,‘a’] assume_tac Add_sym >>
 arw[] >> arw[LESS_EQ_MONO_ADD_EQ]
(*need sub of add*))
(form_goal
 “!a b c d. Le(a,c) & Le(b,d) ==> 
   Le(Add(a,b),Add(c,d))”));




val _ = new_pred "Asym" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val Asym_def = store_ax("Asym_def",“!A R:A->A. Asym(R) <=> 
!a b. Holds(R,a,b) & Holds(R,b,a) ==> a = b”)



local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “a = Suc(a)”))] 
 WOP 
in
val Suc_NEQ = prove_store("Add_Suc_NEQ",
e0
(strip_tac >> ccontra_tac >> drule l >>
 pop_assum strip_assume_tac >>
 cases_on “a0 = O” >-- fs[GSYM Suc_NONZERO] >>
 fs[O_xor_Suc] >> fs[] >>
 fs[Suc_eq_eq] >>
 first_x_assum drule >> 
 drule $ iffRL Lt_Suc_Le >> fs[Lt_def])
(form_goal “!a. ~(a = Suc(a))”));
end



val Lt_Suc = prove_store("Lt_Suc",
e0
(rw[Lt_def,Le_def,Sub_Suc,Suc_NEQ,Sub_EQ_O,Pre_O])
(form_goal “!a. Lt(a,Suc(a))”));



local
val l = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “Lt(a,Add(a,Suc(b)))”))] 
 N_ind_P 
in
val Add_Suc_Lt = prove_store("Add_Suc_NEQ",
e0
(strip_tac >> match_mp_tac l >> rw[Suc_def] >> strip_tac 
 >-- (rw[Lt_def,Le_def,Add_Suc,Add_O,Sub_Suc,Pre_O,O_xor_Suc,
        Suc_NEQ,Pre_O,Sub_EQ_O]) >>
 rpt strip_tac >> rw[Add_Suc] >> rw[Lt_Suc_Le] >>
 rw[GSYM Add_Suc] >> fs[Lt_def])
(form_goal “!a b. Lt(a,Add(a,Suc(b)))”));
end



val LT_Trans = prove_store("LT_Trans",
e0
(rw[Trans_def] >> rw[LT_Lt] >> rw[Lt_def] >>
 assume_tac Le_trans >> rpt strip_tac >--
 (first_x_assum irule >> qexists_tac ‘a2’ >> arw[]) >>
 qby_tac ‘(?p1. Add(a1,Suc(p1)) = a2) & 
          ?p2. Add(a2,Suc(p2)) = a3’ >-- 
 (drule Le_Add_ex >> rev_drule Le_Add_ex >> fs[] >>
  qby_tac ‘~(p = O)’ >-- 
  (ccontra_tac >> fs[Add_O2]) >>
  qby_tac ‘~(p' = O)’ >-- 
  (ccontra_tac >> fs[Add_O2]) >>
  fs[O_xor_Suc] >> strip_tac
 >-- (qexists_tac ‘pn'’ >> once_rw[Add_sym] >> fs[]) >>
 qexists_tac ‘pn’ >> once_rw[Add_sym] >> fs[]) >>
 pop_assum (strip_assume_tac o GSYM) >>
 fs[] >> rw[GSYM Add_assoc] >> once_rw[Add_Suc] >>
 assume_tac Add_Suc_Lt >> fs[Lt_def])
(form_goal “Trans(LT)”));

val Lt_trans = LT_Trans |> rewr_rule[LT_Lt,Trans_def]
                        |> store_as "Lt_trans";

val LE_Asym = prove_store("Le_Asym",
e0
(rw[Asym_def] >> rpt strip_tac >> fs[LE_Le] >> 
 drule Le_cases >> pop_assum strip_assume_tac >> arw[] >>
 rev_drule Le_cases >> pop_assum strip_assume_tac >> arw[] >>
 qby_tac ‘Lt(a,a)’ >-- (irule Lt_trans >>
 qexists_tac ‘b’ >> arw[]) >> fs[Lt_def])
(form_goal “Asym(LE)”));

val Le_asym = LE_Asym |> rewr_rule[LE_Le,Asym_def]
                      |> store_as "Le_Asym";



val LESS_EQ_LESS_EQ_MONO = prove_store("LESS_EQ_LESS_EQ_MONO",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(m,q)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 once_rw[Add_sym] >> arw[LESS_EQ_MONO_ADD_EQ])
(form_goal “!m n p q. (Le(m,p) & Le(n,q)) ==> Le(Add(m,n),Add(p,q))”));

local
val l = 
 fVar_Inst 
[("P",([("p",mem_sort N)],
 “Le(a,b) ==> Le(Mul(a,p),Mul(b,p))”))] 
 N_ind_P 
in
val Le_MONO_Mul = prove_store("Le_MONO_Mul",
e0
(strip_tac >> strip_tac >> match_mp_tac l >> 
 rw[Mul_O,Le_refl,Suc_def] >> strip_tac >> arw[] >>
 rw[Mul_Suc] >> rpt strip_tac >>
 first_x_assum drule >> irule LESS_EQ_LESS_EQ_MONO >> arw[])
(form_goal “!m n p. Le(m,n) ==> Le(Mul(m,p),Mul(n,p))”));
end

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
(form_goal “!m n i j. Le(m,i) & Le(n,j) ==> Le(Mul(m,n),Mul(i,j))”));


val Le_MONO = LESS_EQ_MONO |> store_as "Le_MONO";

val Le_O' = prove_store("Le_O'",
e0
(rw[Le_def,Sub_of_O])
(form_goal “!x. Le(O,x)”));

local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b.Le(b,a) ==> Sub(Suc(a),b) = Suc(Sub(a,b))”))] 
 N_ind_P 
val l' = 
 fVar_Inst 
[("P",([("b'",mem_sort N)],
 “Le(b', Suc(r)) ==>
               Sub(Suc(Suc(r)), b') = Suc(Sub(Suc(r), b'))”))] 
 N_ind_P 
in
val Sub_Suc1 = prove_store("Sub_Suc1",
e0
(match_mp_tac l >>
 rw[Le_O_iff,Sub_of_O] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> arw[Sub_O]) >>
 strip_tac >> strip_tac >> rw[Suc_def] >>
 match_mp_tac l' >>
 arw[] >> rw[Le_O,Sub_O] >> strip_tac >>
 rw[Suc_def] >> arw[] >>
 rw[Le_MONO] >> rw[Sub_Suc] >> rpt strip_tac >>
 qby_tac ‘Le(n',Suc(n))’ 
 >-- (irule Le_trans >> qexists_tac ‘n’ >> arw[] >>
     assume_tac Lt_Suc >> fs[Lt_def]) >>
 first_x_assum drule >> arw[] >>
 last_x_assum drule >> arw[] >> rw[Pre_Suc])
(form_goal
 “!a b. Le(b,a) ==> Sub(Suc(a),b) = Suc(Sub(a,b))”));
end


local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b. Le(b,a) ==> Add(Sub(a,b),b) = a”))] 
 N_ind_P 
val l' = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “Le(b, Suc(n')) ==> Add(Sub(Suc(n'), b), b) = Suc(n')”))] 
 N_ind_P 
in
val SUB_ADD = prove_store("SUB_ADD",
e0
(match_mp_tac l >> 
 rw[Sub_of_O,Add_O2,Le_O_iff] >> strip_tac >>
 strip_tac >> rw[Suc_def] >>
 match_mp_tac l' >>
 rw[Sub_O,Add_Suc1,Add_O] >> strip_tac >> arw[] >>
 rw[Suc_def] >> rw[Sub_mono_eq] >> rw[Add_Suc] >> 
 rw[Suc_eq_eq] >> rw[Le_MONO] >> 
 rpt strip_tac >> 
 qby_tac ‘Le(n,Suc(n'))’ 
 >-- (irule Le_trans >> qexists_tac ‘n'’ >> arw[] >>
     assume_tac Lt_Suc >> fs[Lt_def]) >>
 first_x_assum drule >> rev_drule Sub_Suc1 >> fs[] >> 
 first_x_assum irule >> arw[])
(form_goal “!m n. Le(n,m) ==> Add(Sub(m,n),n) = m”));
end



local
val l = 
 fVar_Inst 
[("P",([("n",mem_sort N)],
 “!p. Le(n,p) ==> (Add(m,n) = p <=> m = Sub(p,n))”))] 
 N_ind_P 
val l' = 
 fVar_Inst 
[("P",([("p'",mem_sort N)],
 “Le(Suc(n'), p') ==>
  (Add(m, Suc(n')) = p' <=> m = Sub(p', Suc(n')))”))] 
 N_ind_P 
in
val ADD_EQ_SUB = prove_store("ADD_EQ_SUB",
e0
(strip_tac >> match_mp_tac l >> 
 rw[Le_O_iff,Add_O,Sub_O,Suc_def] >> strip_tac >> strip_tac >>
 match_mp_tac l' >> rw[Suc_def] >> 
 rw[Le_def,Sub_O,Suc_NONZERO] >> strip_tac >> arw[] >>
 rw[Add_Suc,Suc_eq_eq,Le_MONO,Sub_mono_eq] >>rpt strip_tac >>
 fs[GSYM Le_def] >>
 first_x_assum drule >> arw[])
(form_goal
 “!m n p. Le(n,p) ==> (Add(m,n) = p <=> m = Sub(p,n))”));
end

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

val Lt_MONO = LESS_MONO_EQ |> store_as "Lt_MONO"; 

local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b.~Lt(a, b) <=> Le(b, a)”))] 
 N_ind_P 
val l' = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “~Lt(Suc(n'), b) <=> Le(b, Suc(n'))”))] 
 N_ind_P 
in
val NOT_LESS = prove_store("NOT_LESS",
e0
(match_mp_tac l >>
 rw[Suc_def] >> rw[Le_O_iff] >> strip_tac (* 2 *)
 >-- (strip_tac >> dimp_tac >> strip_tac >>
     ccontra_tac >> fs[O_xor_SUC,Suc_def] >> fs[Lt_def,GSYM Suc_NONZERO]>>
     fs[Le_def,Sub_Suc,Sub_of_O,Pre_O] >> rfs[] >>
     last_x_assum (assume_tac o GSYM) >> fs[Suc_NONZERO]) >>
 strip_tac >> strip_tac >>
 match_mp_tac l' >> rw[NOT_SUC_LT_O,Le_O'] >>
 rw[Suc_def] >> strip_tac >> arw[] >>
 rw[Le_MONO,Lt_MONO] >> arw[])
(form_goal “!m n. ~(Lt(m,n)) <=> Le(n,m)”));
end



val RIGHT_SUB_DISTR = prove_store("RIGHT_SUB_DISTR",
e0
(rpt strip_tac >>
 qsspecl_then [‘Mul(Sub(m,n),p)’,‘Mul(n,p)’,‘Mul(m,p)’]
 assume_tac ADD_EQ_SUB >> 
 cases_on “Le(n,m)” >--
 (drule Le_MONO_Mul' >> fs[] >>
 fs[GSYM RIGHT_DISTR] >> drule SUB_ADD >> fs[]) >>
 fs[GSYM NOT_LESS] >> fs[Lt_def] >>
 fs[Le_def,Mul_clauses] >> flip_tac >> rw[GSYM Le_def] >>
 irule Le_MONO_Mul' >> arw[Le_def])
(form_goal “!m n p. Mul(Sub(m,n),p) = Sub(Mul(m,p),Mul(n,p))”));


val LEFT_SUB_DISTR = prove_store("LEFT_SUB_DISTR",
e0
(rpt strip_tac >> once_rw[Mul_sym] >>
 rw[RIGHT_SUB_DISTR])
(form_goal “!m n p. Mul(p,Sub(m,n)) = Sub(Mul(p,m),Mul(p,n))”));


(*
define the set of lists
Eval(f:A(set of A->B functions)->B(set of A list -> B list function),a)

induction recursion

!P. P [] & (!t h.P(t) ==> P(h :: t)) ==> !l. P(l)

recursion :

!n c:'a -> 'b -> 'b. ?!f:'a list -> 'b. f [] = n & !h t. f(h :: t) = c h (f t)


map fold

Map(f:A->B): 'a list set -> 'b list set





*)

(*


val ADD_def0 = Nind_def |> specl [rastt "N"]
                        |> specl [rastt "SUC"]
                        |> C mp SUC_Fun 
                        


(*
pre0 
pre0 n = (n,pre n)

f: (n,pre n) |-> (suc n, n)


(1, pre 1 = pre 0) |-> 
*)


val PRE_def0 = Nind_def |> specl [rastt "N * N"]
                        |> specl [rastt "SUC"]
                        |> C mp SUC_Fun 
*)                        
