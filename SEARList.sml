


(*

[1,2]


{(0,1),(1,2)}


[2,1]


{(0,2),(1,1)}


N -> (A + 1)


eq_psym


a = c & b = d
---------
P(a,b) <=> P(c,d)




fun eq_Pred p  = 



?P




()

*)


(*exists a set of "sets of sets of  pairs (n,a)"
  (each member of such set is a subset of Pow(N * A), so each such set is  an element of Pow(Pow(N * A)))
  which satisfies the condition that
  {} is in the set, and ... *)

val lemma = 
fVar_Inst 
[("P",([("sets",mem_sort$ Pow $ Pow $ Cross N (mk_set "A"))],
“IN(Empty(N * A),sets:mem(Pow(Pow(N * A)))) & 
 !l. IN(l,sets) ==> !a:mem(A).IN(Ins(Pair(CARD(l),a),l),sets)”))] 
(IN_def_P_expand |> qspecl [‘Pow(Pow(N * A))’]) 

(*make Ins Pair as Cons0 *)

(*set of subsets of that contains the set of lists*)
val As_def = lemma |> ex2fsym0 "As" ["A"] |> conjE1 
                   |> gen_all |> GSYM



val List_ex_lemma = fVar_Inst 
[("P",([("ls",mem_sort $ Pow $ Cross N (mk_set "A"))],
“IN(ls,BIGINTER(As(A)))”))]
(Thm_2_4 |> qspecl [‘(Pow(N * A))’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all IN_BIGINTER)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all As_def)



(*f:A->B. is inj, then ?g:B->A. g o f = id(A).
  
have this function. 


*)

val List_LI_def = List_ex_lemma |> ex2fsym0 "List" ["A"] |>ex2fsym0 "LI" ["A"]

val LI_Inj = conjE1 List_LI_def |> gen_all |> store_as "LI_Inj";

val LI_Fun = LI_Inj |> rewr_rule[Inj_def] |> spec_all |> conjE1
                    |> gen_all |> store_as "LI_Fun";


val IN_List = List_LI_def |> conjE2 |> gen_all |> 
conv_rule $ basic_once_fconv no_conv (rewr_fconv (eq_sym "mem"))
|> GSYM


val List_ind0 = IN_List |> allE (rastt "A") |>  allE (rastt "Eval(LI(A),b)")
                       |> dimp_mp_l2r
                       (existsI ("b'",mem_sort (rastt "List(A)")) 
                                (rastt "b:mem(List(A))")
                                “Eval(LI(A), b') = Eval(LI(A), b)”
                                (refl (rastt "Eval(LI(A), b)")))
                       |> strip_all_and_imp
                       |> gen_all
                       |> disch_all
                       |> gen_all


val isList_Empty = prove_store("isList_Empty",
e0
(strip_tac >> rw[IN_List] >>
 rpt strip_tac >> arw[])
(form_goal
 “!A. ?e. Eval(LI(A),e) = Empty(N * A)”));

val Nil_def = isList_Empty |> spec_all |> ex2fsym0 "Nil" ["A"]
                           |> gen_all
                           |> store_as "Nil_def";

val isList_cons = prove_store("isList_cons",
e0
(rw[IN_List] >> rpt strip_tac >>
 first_assum irule >> last_x_assum irule >> arw[])
(form_goal
 “!A l. (?l0.Eval(LI(A),l0) = l) ==> !a.?al.Eval(LI(A),al) = Ins(Pair(CARD(l),a),l)”));

(*set of list, takes a list, gives a ser of pairs*)

val sof_ex = prove_store("sof_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(LI(A),l)’ >> rw[])
(form_goal
 “!A l. ?ss. Eval(LI(A),l) = ss”));
 
val sof_def = sof_ex |> spec_all |> ex2fsym0 "sof" ["l"]
                     |> gen_all |> store_as "sof_def"; 

val Inj_eq = Inj_def |> iffLR |> spec_all |> undisch |> conjE2
                     |> disch_all |> gen_all
                     |> store_as "Inj_eq";

local
val l = 
fVar_Inst 
[("P",([("a0l0",mem_sort $ Cross (mk_set "A") (rastt "List(A)")),
        ("l",mem_sort (rastt "List(A)"))],
“Ins(Pair(CARD(sof(Snd(a0l0))), Fst(a0l0:mem(A * List(A)))),sof(Snd(a0l0))) = sof(l)”))]
(AX1 |> qspecl [‘A * List(A)’,‘List(A)’])
|> uex_expand  
in
val Cons_ex = prove_store("Cons_ex",
e0
(strip_tac >> strip_assume_tac l >>
 pop_assum (K all_tac) >> qexists_tac ‘R’ >>
 arw[Pair_def'] >> rw[Fun_expand] >>
 arw[] >> rpt strip_tac (* 2 *)
 >-- (assume_tac isList_cons >>
     fs[sof_def] >> 
     pop_assum (qsspecl_then [‘sof(Snd(a))’] assume_tac) >>
     qby_tac
     ‘(?l0 : mem(List(A)). sof(l0) = sof(Snd(a)))’ 
     >-- (qexists_tac ‘Snd(a)’ >> rw[]) >>
     first_x_assum drule >> 
     first_x_assum (qspecl_then [‘Fst(a)’] assume_tac) >>
     pop_assum strip_assume_tac >> qexists_tac ‘al’ >> arw[]) >>
 irule Inj_eq >> 
 qexistsl_tac [‘Pow(N * A)’,‘LI(A)’] >> 
 rw[LI_Inj] >> rw[sof_def] >>
 pop_assum_list (map_every (assume_tac o GSYM)) >> arw[])
(form_goal
 “!A. ?cons:A * List(A) -> List(A).
  isFun(cons) & 
  (!a0 l0 l. Holds(cons,Pair(a0,l0),l) <=> 
  Ins(Pair(CARD(sof(l0)), a0),sof(l0)) = sof(l))”));
end

val Cons_def = Cons_ex |> spec_all |> ex2fsym0 "Cons" ["A"]
                       |> gen_all |> store_as "Cons_def";


val CONS_ex = prove_store("CONS_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(Cons(A),Pair(a0,l0))’ >> rw[])
(form_goal
 “!A a0 l0. ?l.Eval(Cons(A),Pair(a0,l0)) = l”));

val CONS_def = CONS_ex |> spec_all |> ex2fsym0 "CONS" ["a0","l0"]
                       |> gen_all |> store_as "CONS_def";

val Eval_Cons = prove_store("Eval_Cons",
e0
(rpt strip_tac >>
 assume_tac Cons_def >> 
 first_x_assum (qspecl_then [‘A’] strip_assume_tac) >>
 drule $ GSYM Eval_def >> flip_tac >>
 arw[] >> lflip_tac >> rw[])
(form_goal
 “!A a0 l0 l. Eval(Cons(A), Pair(a0,l0)) = l <=> 
  Ins(Pair(CARD(sof(l0)),a0),sof(l0)) = sof(l)”));

val Cons_eqn = prove_store("Cons_eqn",
e0
(rpt strip_tac >>
 qsspecl_then [‘a0’,‘l0’,‘Eval(Cons(A), Pair(a0,l0))’] assume_tac
 Eval_Cons >> fs[])
(form_goal
 “!A a0 l0. Ins(Pair(CARD(sof(l0)),a0),sof(l0)) = sof(Eval(Cons(A), Pair(a0,l0)))”));

val CONS_eqn = Cons_eqn |> rewr_rule[CONS_def]
                        |> store_as "CONS_eqn";

val sof_Nil = Nil_def |> rewr_rule[sof_def] |> store_as "sof_Nil";

val CONS_NOTNIL = prove_store("CONS_NOTNIL",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac ‘sof(CONS(a,l)) = sof(Nil(A))’ >-- arw[] >>
 fs[GSYM CONS_eqn,sof_Nil,Ins_NONEMPTY])
(form_goal
 “!A a l. ~(CONS(a,l) = Nil(A))”));

val sof_eq_eq = prove_store("sof_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 fs[GSYM sof_def] >> irule Inj_eq >>
 qexistsl_tac [‘Pow(N * A)’,‘LI(A)’] >> arw[LI_Inj] )
(form_goal
 “!A l1:mem(List(A)) l2.sof(l1) = sof(l2) <=> l1 = l2”));

local
val l = 
 fVar_Inst 
[("P",([("nas",mem_sort$ Pow $ Cross N (mk_set "A"))],
“?l:mem(List(A)). P(l) & sof(l) = nas”))] 
(IN_def_P_expand |> qspecl [‘Pow(N * A)’]) 
in
val List_ind = prove_store("List_ind",
e0
(assume_tac List_ind0 >>
 rpt strip_tac >>
 qby_tac
 ‘?ss. !nas. IN(nas,ss) <=> ?l:mem(List(A)). P(l) & sof(l) = nas’
 >-- (strip_assume_tac l >> pop_assum (K all_tac) >>
     qexists_tac ‘s’ >> strip_tac >> pop_assum (assume_tac o GSYM) >>
     first_x_assum (qspecl_then [‘nas’] accept_tac)) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘!b. IN(Eval(LI(A),b),ss)’
 >-- (rpt strip_tac >> 
     first_x_assum (qspecl_then [‘l’] assume_tac) >>
     first_x_assum $ drule o iffLR >>
     pop_assum strip_assume_tac >>
     pop_assum mp_tac >> once_rw[sof_def] >> once_rw[sof_eq_eq] >>
     strip_tac >> 
     assume_tac (EQ_fVar "P" [assume “l' = l:mem(List(A))”]) >>
     first_x_assum $ irule o iffLR >> 
     first_x_assum accept_tac) >>
 (*first_x_assum irule gives err wrong concl*)
 last_x_assum irule >> rpt strip_tac (* 2 *)
 >-- (first_assum $ drule o iffLR >> pop_assum strip_assume_tac >>
     last_assum drule >> 
     first_assum $ irule o iffRL >>
     qexists_tac ‘CONS(a,l'')’ >> strip_tac
     >-- first_assum (qspecl_then [‘a’] accept_tac) >>
     qsuff_tac
     ‘sof(CONS(a, l'')) = Ins(Pair(CARD(sof(l'')), a), sof(l''))’
     >-- (qpick_x_assum ‘sof(l'') = l'’ (mp_tac o GSYM) >>
         pop_assum_list (map_every (K all_tac)) >> rpt strip_tac >>
         arw[]) >>
     once_rw[CONS_eqn]  >> rw[]) >>
 first_assum $ irule o iffRL >>
 qexists_tac ‘Nil(A)’ >> strip_tac 
 >-- first_assum accept_tac >>
 once_rw[GSYM Nil_def] >> rw[sof_def]
 )
(form_goal
 “!A. P(Nil(A)) & 
      (!l:mem(List(A)). P(l) ==> !a. P(CONS(a,l))) ==>
     !l:mem(List(A)).P(l) ”));
end




local 
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“Fin(sof(l:mem(List(A))))”))] 
(List_ind |> qspecl [‘A’]) 
in
val LI_Fin = prove_store("LI_Fin",
e0
(strip_tac >> match_mp_tac l >>
 rw[sof_Nil,Fin_Empty] >> rpt strip_tac >>
 rw[GSYM CONS_eqn] >> drule Fin_Ins >> arw[])
(form_goal
 “!A l:mem(List(A)). Fin(sof(l))”));
end


local
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“!n a:mem(A). IN(Pair(n,a),sof(l)) ==> Lt(n,CARD(sof(l)))”))] 
(List_ind |> qspecl [‘A’])
in
val isList_CARD_NOTIN0 = prove_store("isList_CARD_NOTIN0",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> match_mp_tac l >>
 rpt strip_tac (* 2 *)
 >-- fs[sof_Nil,Empty_property] >>
 fs[GSYM CONS_eqn,IN_Ins] (* 2 *)
 >-- (fs[Pair_eq_eq] >> 
     qby_tac ‘~IN(Pair(CARD(sof(l')), a'),sof(l'))’ 
     >-- (ccontra_tac >> first_x_assum drule  >>
         fs[Lt_def]) >>
     qsspecl_then [‘l'’] assume_tac LI_Fin >>
     drule CARD_Ins >> first_x_assum drule >> 
     arw[] >> rw[Lt_Suc]) >>
 first_x_assum drule >> 
 cases_on “IN(Pair(CARD(sof(l')), a':mem(A)),sof(l'))” 
 >-- (drule Ins_absorb >> arw[]) >>
 qsspecl_then [‘l'’] assume_tac LI_Fin >>
 drule CARD_Ins >> first_x_assum drule >> arw[] >>
 irule Lt_trans >>
 qexists_tac ‘CARD(sof(l'))’ >> arw[Lt_Suc])
(form_goal
 “!A l n a:mem(A). IN(Pair(n,a),sof(l)) ==> Lt(n,CARD(sof(l)))”));
end


val Cons_Inj = prove_store("Cons_Inj",
e0
(strip_tac >> rw[Inj_def,Cons_def] >> 
 rpt strip_tac >>
 qsspecl_then [‘x1’]
 (x_choosel_then ["a1","l1"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘x2’] 
 (x_choosel_then ["a2","l2"] assume_tac) Pair_has_comp >>
 fs[] >> fs[CONS_def] >> 
 qby_tac
 ‘sof(CONS(a1, l1)) = sof(CONS(a2, l2))’
 >-- arw[] >>
 fs[GSYM CONS_eqn] >>
 qsuff_tac
 ‘Pair(CARD(sof(l1)), a1) = Pair(CARD(sof(l2)), a2) & 
  sof(l1) = sof(l2)’
 >-- (rw[Pair_eq_eq,sof_eq_eq] >> rpt strip_tac >> arw[]) >>
 irule Ins_eq_eq >>
 arw[] >>
 qby_tac
 ‘~IN(Pair(CARD(sof(l1)), a1), sof(l1))’
 >-- (ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def]) >>
 qby_tac
 ‘~IN(Pair(CARD(sof(l2)), a2), sof(l2))’
 >-- (ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def]) >>
 arw[] >>
 qby_tac ‘CARD(sof(l2)) = CARD(sof(l1))’ 
 >-- (drule $ GSYM Del_Ins >> rev_drule $ GSYM Del_Ins >>  
     once_arw[] >> pop_assum (K all_tac) >>
     pop_assum (K all_tac) >>
     qsspecl_then [‘l2’] assume_tac LI_Fin >>
     drule CARD_Ins >>
     first_x_assum drule >> 
     drule Fin_Ins >>
     first_x_assum (qspecl_then [‘Pair(CARD(sof(l2)), a2)’] assume_tac)>>
     drule CARD_Del >>
     first_x_assum (qspecl_then [‘Pair(CARD(sof(l2)), a2)’] assume_tac) >>
     pop_assum mp_tac >> rw[IN_Ins] >>
     strip_tac >> 
     qsuff_tac
     ‘Pre(CARD(Ins(Pair(CARD(sof(l2)), a2), sof(l2)))) = 
      CARD(Del(Ins(Pair(CARD(sof(l1)), a1), sof(l1)),
                 Pair(CARD(sof(l1)), a1)))’
     >-- (strip_tac >> arw[]) >>
     pop_assum (K all_tac) >> pop_assum (K all_tac) >>
     pop_assum (K all_tac) >> pop_assum (K all_tac) >>
     qsspecl_then [‘l1’] assume_tac LI_Fin >>
     drule CARD_Ins >> 
     first_x_assum drule >>
     drule Fin_Ins >>
     first_x_assum (qspecl_then [‘Pair(CARD(sof(l1)), a1)’] assume_tac)>>
     drule CARD_Del >>
     first_x_assum (qspecl_then [‘Pair(CARD(sof(l1)), a1)’] assume_tac) >>
     pop_assum mp_tac >> rw[IN_Ins] >>
     strip_tac >> once_arw[] >>
     qpick_x_assum
     ‘Ins(Pair(CARD(sof(l1)), a1), sof(l1)) =
               Ins(Pair(CARD(sof(l2)), a2), sof(l2))’ mp_tac >>
     pop_assum_list (map_every (K all_tac)) >>
     strip_tac >> arw[]) >>
 strip_tac (* 2 *)
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def]) >>
 arw[] >> ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def]
 )
(form_goal
 “!A. isInj(Cons(A))”));


val CONS_eq_eq = prove_store("CONS_eq_eq",
e0
(rw[GSYM CONS_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 irule $ iffLR Pair_eq_eq >>
 irule Inj_eq >>
 qexistsl_tac [‘List(A)’,‘Cons(A)’] >> arw[Cons_Inj])
(form_goal
 “!A a1:mem(A) l1 a2 l2.CONS(a1,l1) = CONS(a2,l2) <=> (a1 = a2 & l1 = l2)”));




local
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“l = Nil(A) | ?a0 l0. l = CONS(a0, l0)”))] 
(List_ind |> qspecl [‘A’])
in
val CONS_or_Nil = prove_store("CONS_or_Nil",
e0
(strip_tac >> irule l >> rw[] >>
 rpt strip_tac >--
 (rw[CONS_NOTNIL] >> qexistsl_tac [‘a’,‘l’] >> rw[]) >>
 rw[CONS_NOTNIL] >> 
 qexistsl_tac [‘a’,‘l’] >> arw[])
(form_goal
 “!A l:mem(List(A)). l = Nil(A) | ?a0 l0. l = CONS(a0,l0)”));
end

local
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“Eval(f1:List(A) ->X, l) = Eval(f2, l)”))] 
(List_ind |> qspecl [‘A’])
in
val from_List_eq = prove_store("from_List_eq",
e0
(rpt strip_tac >> irule $ iffRL FUN_EXT >> arw[] >>
 irule l >> arw[])
(form_goal
 “!A X f1:List(A) ->X f2. isFun(f1) & isFun(f2) &
 Eval(f1, Nil(A)) = Eval(f2,Nil(A)) &
 (!l. Eval(f1,l) = Eval(f2,l) ==> 
  !a. Eval(f1,CONS(a,l)) = Eval(f2,CONS(a,l))) ==> f1 = f2”));
end



val cRf_def = 
fVar_Inst 
[("P",([("ss",mem_sort$ Pow $ Cross (rastt "List(A)") (mk_set "X"))],
“IN(Pair(Nil(A),x:mem(X)),ss)& 
 !l x. IN(Pair(l,x),ss) ==> 
    !a:mem(A).IN(Pair(CONS(a,l),Eval(t,Pair(a,x))),ss)”))] 
(IN_def_P_expand |> qspecl [‘Pow(List(A) * X)’]) 
|> ex2fsym0 "cRf" ["x","t"] |> conjE1 
|> qgen ‘t’ |> qgen ‘A’
|> gen_all |> GSYM

local
val Rf0_ex = 
fVar_Inst 
[("P",([("lx",mem_sort $ Cross (rastt "List(A)") (mk_set "X"))],
“IN(lx,BIGINTER(cRf(x:mem(X),t:A * X->X)))”))]
(Thm_2_4 |> qspecl [‘List(A) * X’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all IN_BIGINTER)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all cRf_def) |> GSYM
val R = 
fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)")),("x",mem_sort (mk_set "X"))],
“?r.Eval(i:B-> List(A) * X,r) = Pair(l,x)”))]
(AX1 |> qspecl [‘List(A)’,‘X’]) |> uex_expand
val ss = fVar_Inst 
[("P",([("lx",mem_sort $ Cross (rastt "List(A)") (mk_set "X"))],
“Holds(P:List(A) ->X,Fst(lx),Snd(lx))”))] 
(IN_def_P_expand |> qspecl [‘List(A) * X’]) 
in
val Rf_ex = prove_store("Rf_ex",
e0
(rpt strip_tac >> strip_assume_tac Rf0_ex >>
 strip_assume_tac R >>
 pop_assum (K all_tac) >>
 qexists_tac ‘R’ >>
 strip_tac (* 2 *)
 >-- (arw[] >> flip_tac >> arw[] >>
     rpt strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (arw[] >> flip_tac >> arw[] >> rpt strip_tac >>
     first_assum irule >> first_assum irule >> arw[]) >>
 arw[] >> flip_tac >>
 arw[] >> rpt strip_tac >>
 strip_assume_tac ss >> pop_assum (K all_tac) >>
 first_x_assum (qspecl_then [‘s’] assume_tac) >>
 first_assum (qspecl_then [‘Pair(l,x0)’] assume_tac) >>
 fs[Pair_def'] >>
 first_assum irule >> strip_tac (* 2 *)
 >-- (strip_tac >> strip_tac >> 
     first_assum (qspecl_then [‘Pair(l',x')’] (assume_tac o GSYM)) >> 
     once_arw[] >> rw[Pair_def'] >> 
     rpt strip_tac >> first_x_assum drule >>
     qpick_x_assum
     ‘!a1. Holds(P, Fst(a1), Snd(a1)) <=> IN(a1, s)’ (assume_tac o GSYM) >>
     once_arw[] >> rw[Pair_def'] >> once_arw[]) >>
 qpick_x_assum
     ‘!a1. Holds(P, Fst(a1), Snd(a1)) <=> IN(a1, s)’ (assume_tac o GSYM) >> 
  once_arw[] >> rw[Pair_def'] >> 
 first_x_assum accept_tac
 )
(form_goal
 “!X x A t:A * X ->X. ?Rf:List(A) ->X.
 Holds(Rf,Nil(A),x) & 
 (!l x0. Holds(Rf,l,x0) ==> !a. Holds(Rf,CONS(a,l),Eval(t,Pair(a,x0)))) &
 (!P.
 (Holds(P,Nil(A),x) & 
  (!l x0. Holds(P,l,x0) ==> !a. Holds(P,CONS(a,l),Eval(t,Pair(a,x0)))))
  ==> !l x0.Holds(Rf,l,x0) ==> Holds(P,l,x0))”));
end

val Rf_def = Rf_ex |> spec_all
                   |> ex2fsym0 "Rf" ["x","t"]
                   |> qgen ‘t’ |> qgen ‘A’
                   |> gen_all |> store_as "Rf_def";

val Rf_property = conjI (Rf_def |> spec_all |> conjE1)
                        (Rf_def |> spec_all |> conjE2 |> conjE1)
                        |> qgen ‘t’ |> qgen ‘A’
                        |> gen_all |> store_as "Rf_property";

val Rf_min = Rf_def |> spec_all |> conjE2 |> conjE2
                    |> qgen ‘t’ |> qgen ‘A’
                    |> gen_all |> store_as "Rf_property";

local
val P = 
fVar_Inst 
[("P",([("l1",mem_sort (rastt "List(A)")),("x1",mem_sort (mk_set "X"))],
“Holds(Rf(x,t:A * X->X),l1,x1) & ~(l1 = Nil(A) & x1 = x0)”))]
(AX1 |> qspecl [‘List(A)’,‘X’]) |> uex_expand
in
val Rf_Nil_unique = prove_store("Rf_Nil_unique",
e0
(rpt strip_tac >> ccontra_tac >>
 qsuff_tac
 ‘?P. Holds(P,Nil(A),x) & 
     (!l x0. Holds(P,l,x0) ==>
      !a. Holds(P,CONS(a,l),Eval(t,Pair(a,x0)))) & 
     ~Holds(P,Nil(A),x0)’ 
 >-- (strip_tac >> qsspecl_then [‘x’,‘t’,‘P’] assume_tac Rf_min >>
     qsuff_tac ‘Holds(P, Nil(A), x0)’ >--arw[] >>
     first_x_assum irule >> arw[Rf_property]) >>
 qsuff_tac
 ‘?P. !l1 x1. Holds(P,l1,x1) <=> 
  Holds(Rf(x,t),l1,x1) & ~(l1 = Nil(A) & x1 = x0)’
 >-- (strip_tac >> qexists_tac ‘P’ >> arw[] >>
     rw[Rf_property] >> flip_tac >> arw[] >>
     (*do not understand why need strip*)
     strip_tac >> strip_tac >> arw[] >> 
     rw[CONS_NOTNIL] >> rpt strip_tac >>  
     qsspecl_then [‘x’,‘t’] strip_assume_tac Rf_property >>
      last_x_assum (K all_tac) >>
      first_x_assum rev_drule >> arw[]) >>
 strip_assume_tac P >> 
 qexists_tac ‘R’ >> arw[]
 )
(form_goal
 “!X x A t:A * X ->X x0. 
  Holds(Rf(x,t),Nil(A),x0) ==> x0 = x”));
end

val Rf_CONS = Rf_property |> spec_all |> conjE2
                          |> qgen ‘t’ |> qgen ‘A’
                          |> gen_all
                          |> store_as "Rf_CONS";


local
val P = 
fVar_Inst 
[("P",([("l0",mem_sort (rastt "List(A)")),("x0",mem_sort (mk_set "X"))],
“Holds(Rf(x,t:A * X ->X),l0,x0) & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Holds(Rf(x,t),l1,x1) & x0 = Eval(t,Pair(a,x1))”))]
(AX1 |> qspecl [‘List(A)’,‘X’]) |> uex_expand
in
val Rf_Cons_back = prove_store("Rf_Cons_back",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 qby_tac
 ‘?P. !l0 x0. Holds(P,l0,x0) <=>
  Holds(Rf(x,t),l0,x0) & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Holds(Rf(x,t),l1,x1) & x0 = Eval(t,Pair(a,x1))’ 
 >-- (strip_assume_tac P >> qexists_tac ‘R’ >> arw[]) >>
 pop_assum strip_assume_tac >>
  qsuff_tac
 ‘!l0 x0.Holds(Rf(x, t),l0, x0) ==> Holds(P,l0,x0)’
 >-- arw[] >>
 match_mp_tac Rf_min >>
 arw[] >> rw[GSYM CONS_NOTNIL] >> rpt strip_tac (* 3 *)
 >-- rw[Rf_property]
 >-- (drule Rf_CONS >> arw[]) >>
 qsspecl_then [‘l’] strip_assume_tac CONS_or_Nil >-- (* 2 *)
 (fs[CONS_eq_eq] >> qexists_tac ‘x0’ >> arw[]) >>
 fs[CONS_eq_eq] >> qexists_tac ‘x0’ >> arw[]
)
(form_goal
 “!X x A t:A * X ->X l0 x0. Holds(Rf(x,t),l0,x0) ==>
  Holds(Rf(x,t),l0,x0) & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Holds(Rf(x,t),l1,x1) & x0 = Eval(t,Pair(a,x1))”));
end




local
val P = 
fVar_Inst 
[("P",([("l0",mem_sort (rastt "List(A)")),("x0",mem_sort (mk_set "X"))],
“(!x'. Holds(Rf(x,t:A * X ->X),l0,x')  ==> x' = x0)”))]
(AX1 |> qspecl [‘List(A)’,‘X’]) |> uex_expand
in
val Rf_unique = prove_store("Rf_unique",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 qby_tac
 ‘?P. !l0 x0. Holds(P,l0,x0) <=>
 (!x'. Holds(Rf(x,t),l0,x')  ==> x' = x0)’
 >-- (strip_assume_tac P >> qexists_tac ‘R’ >> arw[]) >> 
 pop_assum strip_assume_tac >>
 qsuff_tac 
 ‘!l0 x0. Holds(Rf(x,t),l0,x0) ==> Holds(P,l0,x0)’ 
 >-- arw[] >>
 match_mp_tac Rf_min >> arw[] >> 
 strip_tac (* 2 *)
 >-- rw[Rf_Nil_unique] >> rpt strip_tac >>
 drule Rf_Cons_back >> 
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘a’,‘l’] assume_tac) >> fs[] >>
 first_x_assum drule >> arw[])
(form_goal
 “!X x A t:A * X ->X l0 x0. 
  Holds(Rf(x,t),l0,x0) ==>
  !x'. Holds(Rf(x,t),l0,x') ==> x' = x0”));
end

local 
val l = 
 fVar_Inst 
[("P",([("l0",mem_sort (rastt "List(A)"))],
“?!x0. Holds(Rf(x, t:A * X ->X), l0, x0)”))] 
(List_ind |> qspecl [‘A’]) 
in
val Rf_uex = prove_store("Rf_uex",
e0
(rpt strip_tac >>
 irule l >> rpt strip_tac (* 2 *)
 >-- (pop_assum (strip_assume_tac o uex_expand) >>
     drule Rf_CONS >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 uex_tac >> qexists_tac ‘Eval(t, Pair(a,x0))’ >> arw[] >> drule Rf_unique >> arw[]) >>
 uex_tac >> qexists_tac ‘x’ >> rw[Rf_property] >>
 rw[Rf_Nil_unique])
(form_goal
 “!X x A t:A * X ->X l0.?!x0. Holds(Rf(x,t),l0,x0)”));
end



val List_rec = prove_store("List_rec",
e0
(rpt strip_tac >> uex_tac >> 
 assume_tac Rf_uex >> qexists_tac ‘Rf(x,t)’ >>
 qby_tac
 ‘isFun(Rf(x,t))’
 >-- arw[Fun_def] >>
 arw[] >> 
 qby_tac
 ‘Eval(Rf(x, t), Nil(A)) = x &
               Rf(x, t) o Cons(A) = t o
                 Pa(p1(A, List(A)), Rf(x, t) o p2(A, List(A)))’
 >-- (drule $GSYM Eval_def >> flip_tac >> arw[Rf_property] >>
     irule $ iffRL FUN_EXT >>
     qby_tac ‘isFun(Rf(x, t) o Cons(A))’
     >-- (irule o_Fun >> arw[Cons_def]) >> arw[] >>
     qby_tac ‘isFun(t o Pa(p1(A, List(A)), Rf(x, t) o p2(A, List(A))))’
     >-- (irule o_Fun >> arw[] >> irule Pa_Fun >>
         rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
     arw[] >> strip_tac >>
     assume_tac Rf_CONS >>
     qsspecl_then [‘a’] (x_choosel_then ["l","x0"] assume_tac)
     Pair_has_comp >> fs[] >>
     irule $ iffRL Eval_o_l >> rw[CONS_def] >>
     arw[Cons_def] >> flip_tac >>
     irule $ iffRL Eval_o_l >>
     arw[] >> rpt strip_tac  (* 2 *)
     >-- (qby_tac
         ‘isFun(p1(A, List(A))) & 
          isFun(Rf(x, t) o p2(A, List(A)))’
         >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
         drule Eval_Pa_Pair >> arw[] >> rw[Eval_p1_Pair] >>
         qby_tac ‘isFun(p2(A, List(A))) & isFun(Rf(x,t))’
         >-- arw[p2_Fun] >>
         drule$ GSYM o_Eval' >> arw[] >> rw[Eval_p2_Pair] >>
         first_x_assum irule >> 
         irule Holds_Eval >> arw[]) >>
     irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >>
     arw[p2_Fun]) >>
 arw[] >> rpt strip_tac >>
 irule from_List_eq >>
 arw[] >> rpt strip_tac >>
 rw[GSYM CONS_def] >>
 irule $ iffLR Eval_o_l >> arw[] >> 
 rw[Cons_def] >>
 irule $ iffRL Eval_o_l >> arw[] >> 
 qby_tac
 ‘isFun(p1(A, List(A))) & isFun(f' o p2(A, List(A)))’
 >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
 drule Eval_Pa_Pair >> arw[] >> rw[Eval_p1_Pair] >>
 qby_tac ‘isFun(p2(A,List(A))) & isFun(f')’ 
 >-- arw[p2_Fun] >>
 drule $GSYM o_Eval' >> arw[] >> rw[Eval_p2_Pair] >>
 arw[] >> strip_tac (* 2 *)
 >-- (flip_tac >> irule $ iffLR Eval_o_l >> arw[Cons_def] >>
     irule $ iffRL Eval_o_l >> arw[] >>
     strip_tac (* 2 *)
     >-- (irule Eval_input_eq >> 
         qby_tac ‘isFun(p1(A, List(A))) & isFun(Rf(x,t) o p2(A, List(A)))’
         >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
         drule Eval_Pa_Pair >> arw[] >>
         rw[Eval_p1_Pair] >> rw[Pair_eq_eq] >>
         irule $ iffRL Eval_o_l >> arw[p2_Fun,Eval_p2_Pair]) >>
     irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >>
     arw[p2_Fun]) >>
 irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >>
 arw[p2_Fun])
(form_goal
 “!X x A t:A * X ->X. isFun(t) ==> 
  ?!f:List(A) -> X. isFun(f) & Eval(f,Nil(A)) = x &
      f o Cons(A) = t o Pa(p1(A,List(A)), f o p2(A,List(A)))”));

 
local 
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)")),("n",mem_sort N)],
“n = CARD(sof(l:mem(List(A))))”))] 
(AX1 |> qspecl [‘List(A)’,‘N’]) |> uex_expand 
in
val Length_ex = prove_store("Length_ex",
e0
(strip_tac >> strip_assume_tac l  >>
 qexists_tac ‘R’ >> rw[] >>
qby_tac ‘isFun(R)’ 
>-- (arw[Fun_expand] >> rpt strip_tac (* 2 *)
    >-- (qexists_tac ‘CARD(sof(a))’ >> arw[]) >>
    arw[]) >>
 arw[])
(form_goal
 “!A. ?lg:List(A) -> N. isFun(lg) &
 (!l n.Holds(lg,l,n) <=> n = CARD(sof(l)))”));
end

val Length_def = Length_ex |> spec_all |> ex2fsym0 "Length" ["A"]
|> gen_all |> store_as "Length_def";

val LENGTH_ex = prove_store("LENGTH_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(Length(A),l)’ >> rw[])
(form_goal
 “!A l:mem(List(A)).?n. Eval(Length(A),l) = n”));
 
val LENGTH_def = LENGTH_ex |> spec_all |> ex2fsym0 "LENGTH" ["l"]
                           |> gen_all
                           |> store_as "LENGTH_def";

val Eval_Length = prove_store("Eval_Length",
e0
(rpt strip_tac >> qspecl_then [‘A’] strip_assume_tac Length_def >>
 drule $ GSYM Eval_def >> flip_tac >> arw[] >>
 lflip_tac >> rw[])
(form_goal
 “!A l n. Eval(Length(A),l) = n <=> n = CARD(sof(l))”));

val LENGTH_Nil = prove_store("LENGTH_Nil",
e0
(rw[GSYM LENGTH_def,Eval_Length] >> 
 rw[sof_Nil,CARD_Empty])
(form_goal
 “!A. LENGTH(Nil(A)) = O”));

val LENGTH_CONS = prove_store("LENGTH_CONS",
e0
(rpt strip_tac >> rw[GSYM LENGTH_def,Eval_Length] >>
 rw[GSYM CONS_eqn] >>
 qby_tac ‘Eval(Length(A), l) = CARD(sof(l))’ 
 >-- rw[Eval_Length] >>
 arw[] >>
 flip_tac >> irule CARD_Ins >>
 rw[LI_Fin] >>
 ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def])
(form_goal
“!A a:mem(A) l. LENGTH(CONS(a,l)) = Suc(LENGTH(l))”));

val LENGTH_eqn = prove_store("LENGTH_eqn",
e0
(rw[GSYM LENGTH_def,Eval_Length])
(form_goal
 “!A l:mem(List(A)). LENGTH(l) = CARD(sof(l))”));



local
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“!n. Lt(n,LENGTH(l)) ==> ?!a:mem(A). IN(Pair(n,a),sof(l))”))] 
(List_ind |> qspecl [‘A’]) 
in
val El_lemma = prove_store("El_lemma",
e0
(strip_tac >> match_mp_tac l >>
 rw[LENGTH_Nil,NOT_Lt_O] >> rpt strip_tac >>
 fs[LENGTH_CONS] >> fs[Lt_Suc_Le] >>
 fs[Le_cases_iff] (* 2 *)
 >-- (first_x_assum drule >> uex_tac >>
     pop_assum (strip_assume_tac o uex_expand) >>
     qexists_tac ‘a'’ >> 
     arw[GSYM CONS_eqn,IN_Ins] >> rw[Pair_eq_eq] >> rpt strip_tac (* 2 *)
     >-- fs[GSYM LENGTH_def,GSYM Eval_Length,Lt_def] >>
     first_x_assum irule >> arw[]) >>
 uex_tac >> qexists_tac ‘a’ >>
 rw[GSYM CONS_eqn,IN_Ins] >> arw[LENGTH_eqn] >>
 rw[Pair_eq_eq] >> rpt strip_tac >> drule isList_CARD_NOTIN0 >>
 fs[Lt_def])
(form_goal
 “!A l:mem(List(A)) n. Lt(n,LENGTH(l)) ==> ?!a. IN(Pair(n,a),sof(l))”));
end

val Arb_ex = prove_store("Arb_ex",
e0
(rw[])
(form_goal
 “!A. (?a:mem(A).T) ==> (?a:mem(A).a = a) ”));

val Arb_def = Arb_ex |> spec_all |> undisch
                     |> ex2fsym0 "Arb" ["A"]
                     |> disch_all
                     |> gen_all
                     |> store_as "Arb_def";

val List_CARD_NOTIN = prove_store("List_CARD_NOTIN",
e0
(rpt strip_tac >> ccontra_tac >> drule isList_CARD_NOTIN0 >>
 fs[Lt_def])
(form_goal
 “!A l a:mem(A).~IN(Pair(CARD(sof(l)),a),sof(l))”));

(*
val Lt_xor_Le = prove_store("Lt_xor_Le",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (fs[Lt_def] >>
 cases_on “a = b:mem(N)” >-- (fs[] >> rw[Le_refl]) >>
 fs[] >> 
 qsspecl_then [‘a’,‘b’] assume_tac LESS_EQ_cases >> fs[]) >>
 
 )
(form_goal
 “!a b. ~Lt(a,b) <=> Le(b,a)”));
*) 
 
local
val l = 
 fVar_Inst 
[("P",([("n",mem_sort N)],
“~(n = O) ==> Lt(m,Add(m,n))”))] 
N_ind_P
in
val LESS_ADD_NONZERO = prove_store("LESS_ADD_NONZERO",
e0
(strip_tac >> match_mp_tac l >> rw[Suc_def] >> 
rpt strip_tac >> cases_on “n = O” 
 >-- arw[Add_Suc,Add_O,Lt_Suc] >>
 first_x_assum drule >>
 rw[Add_Suc] >> irule Lt_trans >>
 qexists_tac ‘Add(m,n)’ >> arw[Lt_Suc])
(form_goal
 “!m n. ~(n = O) ==> Lt(m,Add(m,n))”));
end

val SUB_LESS = prove_store("SUB_LESS",
e0
(rpt strip_tac >>
 drule Le_Add_ex >> pop_assum (strip_assume_tac o GSYM)>>
 arw[] >>
 rw[Add_Sub] >> 
 irule LESS_ADD_NONZERO >> fs[Lt_def] >> flip_tac >> arw[]
 )
(form_goal
 “!m n. Lt(O,n) & Le(n,m) ==> Lt(Sub(m,n),m)”));


local 
val l = 
 fVar_Inst 
[("P",([("nl",mem_sort $ Cross N (rastt "List(A)")),
        ("a",mem_sort (mk_set "A"))],
“(Le(Fst(nl),LENGTH(Snd(nl))) & IN(Pair(Sub(LENGTH(Snd(nl)),(Fst(nl))),a:mem(A)),sof(Snd(nl)))) |
 (Fst(nl) = O & a = Arb(A)) |
 (Lt(LENGTH(Snd(nl)),Fst(nl)) & a = Arb(A))”))] 
(AX1 |> qspecl [‘N * List(A)’,‘A’]) |> uex_expand 
in
val El_ex = prove_store("El_ex",
e0
(rpt strip_tac >> strip_assume_tac l >>
 pop_assum (K all_tac) >>
 qexists_tac ‘R’ >> arw[Pair_def'] >>
 qby_tac ‘isFun(R)’ 
 >-- (rw[Fun_def] >>
     strip_tac  >>
     qsspecl_then [‘x’] (x_choosel_then ["n","l"] strip_assume_tac)
     Pair_has_comp >>
     cases_on “n = O” (* 2 *)
     >-- (uex_tac >> qexists_tac ‘Arb(A)’ >>
         arw[] >> rw[Pair_def'] >>
         rw[Sub_O,LENGTH_eqn,List_CARD_NOTIN,NOT_Lt_O]) >>
     cases_on “(Lt(LENGTH(l:mem(List(A))),n))”
     >-- (uex_tac >> qexists_tac ‘Arb(A)’ >> arw[] >>
          rw[Pair_def'] >> arw[] >> rw[LENGTH_eqn] >> rpt strip_tac >>
          arw[] >> fs[LENGTH_eqn] >> 
          fs[Lt_def] >>  
          qsuff_tac ‘CARD(sof(l)) = n’ >-- arw[] >>
          irule Le_asym >> arw[]) >>
 qspecl_then [‘A’] assume_tac El_lemma >>
 uex_tac >> arw[] >> rw[Pair_def'] >>
 arw[] >> fs[NOT_LESS] >>
 qsuff_tac
 ‘?!b. IN(Pair(Sub(LENGTH(l), n), b), sof(l))’
 >-- (strip_tac >> pop_assum (assume_tac o uex_expand) >>arw[]) >>
 first_x_assum irule >> irule SUB_LESS >>
 arw[] >> fs[O_xor_Suc] >> rw[LESS_O]) >>
 arw[] >> rpt strip_tac >> 
 fs[NOT_LESS] >> 
 qsuff_tac
 ‘~ Lt(LENGTH(l), n) ’ >-- (strip_tac >> arw[]) >>
 rw[NOT_LESS] >> arw[] )
(form_goal
 “!A. ?el:N * List(A) ->A. 
  isFun(el) &
  !n l a. ~(n = O) & ~(Lt(LENGTH(l),n)) ==>
  (Holds(el,Pair(n,l),a) <=> 
  IN(Pair(Sub(LENGTH(l),n),a),sof(l)))”));
end

(*do it in induction with num instead. use N_ind and hd and tl.

*)

local
val l = 
 fVar_Inst 
[("P",([("al0",mem_sort (rastt "A * List(B)")),
        ("l",mem_sort (rastt "List(B)"))],
“CONS(Eval(f:A->B,Fst(al0)),Snd(al0)) = l”))] 
(AX1 |> qspecl [‘A * List(B)’,‘List(B)’]) |> uex_expand 
in
val Map_ex = prove_store("Map_ex",
e0
(rpt strip_tac >> strip_assume_tac l >>
 pop_assum (K all_tac) >> 
 qby_tac ‘isFun(R)’ 
 >-- (arw[Fun_expand] >> rpt strip_tac (* 2 *)
     >-- (qexists_tac ‘CONS(Eval(f, Fst(a)), Snd(a))’ >> rw[]) >>
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 qsspecl_then [‘Nil(B)’,‘R’] assume_tac List_rec >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 pop_assum (K all_tac) >>
 qexists_tac ‘f'’ >> arw[] >>
 rpt strip_tac >>
 rw[GSYM CONS_def] >> irule $ iffLR Eval_o_l >>
 arw[] >> rw[Cons_def] >> irule $ iffRL Eval_o_l >>
 arw[] >> 
 qby_tac ‘isFun(p1(A, List(A))) & isFun(f' o p2(A, List(A)))’ 
 >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
 drule Eval_Pa_Pair >> arw[] >>
 rw[Eval_p1_Pair,Eval_p2_Pair] >>
 assume_tac $ GSYM o_Eval >>
 pop_assum (qsspecl_then [‘p2(A,List(A))’,‘f'’,‘Pair(a,l)’]
 assume_tac) >> rfs[p2_Fun] >> 
 rw[Eval_p2_Pair] >>
 qpick_x_assum ‘isFun(R)’ assume_tac >>
 drule $GSYM Eval_def >> flip_tac >> arw[] >>
 rw[Pair_def'] >> rw[CONS_def] >>
 irule Pa_Fun  >> rw[p1_Fun] >>
 irule o_Fun >> arw[p2_Fun] )
(form_goal
 “!A B f:A->B. isFun(f) ==> ?map:List(A) -> List(B). 
  isFun(map) & 
  Eval(map, Nil(A)) = Nil(B) &
  !a l.Eval(map,CONS(a,l)) = CONS(Eval(f,a),Eval(map,l))”)); 
end

(*
 !A  B R:A->B. isFun(R) ==> ?f:A~>B. !a:mem(A) b:mem(B). App(f,a) = b <=> Holds(R,a,b)


!a.Holds(R,a,f(a))

R(a,b)

f(a) = b
Eval(f,a) = b

*)


val Map_def = Map_ex |> spec_all |> undisch 
                     |> ex2fsym0 "Map" ["f"]
                     |> disch_all
                     |> gen_all |> store_as "Map_def";

(*

“Holds(Card:Pow(X) -> N,xs,n) <=>
 !ss. IN(Pair(Empty(X),O),ss) & 
      (!xs n. IN(Pair(xs,n),ss) ==>
        !x. ~IN(x,xs) ==> IN(Pair(Ins(x,xs),Suc(n)),ss))==>
      IN(Pair(xs,n),ss)”



so if I do the same thing for list, which extra step should I take to get the set of lists...?
*)


(*
local  
val l = 
 fVar_Inst 
[("P",([("nl",mem_sort $Cross N (rastt "List(A)")),("a",mem_sort (mk_set "A"))],
“IN(Pair(,a),sof(Snd(nl)))”))] 
(AX1 |> qspecl [‘N * List(A)’,‘A’]) |> uex_expand 
in
val El_ex = prove_store("El_ex",
e0
()
(form_goal
 “!A l n. ? Le(n,LENGTH(l)) ==> ”));

val Map_property = prove_store("Map_property",
e0
()
(form_goal
 “!A l n f:A->B. El(n,Map(f,l)) = Eval(f,El(n,l))”));
(*
val Rf_ex = prove_store("Rf_ex",
e0
()
(form_goal
 “!X x:1->X A t:A * X ->X 
  ?Rf. 

!l0 x0.Holds(Rf,l0,x0) = TRUE ==>
  Rf(x,t) o Pa(l0,x0) = TRUE & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Rf(x,t) o Pa(l1,x1) = TRUE & x0 = t o Pa(a,x1)”));

val Rf_def  = 


*)


fun fVar_Inst1 (pair as (P,(argl:(string * sort) list,Q))) f = 
    case view_form f of
        vfVar(P0,args0) =>
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
      | vPred _ => f


(*in last meeting discussed that :
P(a:mem(A),b:mem(B))

Q(c:mem(C),d:mem(D))

should not be allowed since the sort is incorrect, but if use rw, then can just use fVar to inst form. 
*)

(*ex2fsym should check that the input thm does not contain fvars*)

fun fVar_Instl l f = 
    case l of [] => f
            | pair :: t => fVar_Inst1 pair (fVar_Instl t f)

fun fVar_Inst l th = 
    let val (ct,asl,w) = dest_thm th
        val asl' = List.map (fVar_Instl l) asl
        val w' = fVar_Instl l w
        val vs = bigunion (pair_compare String.compare sort_compare)
                          (List.map fvf (w' :: asl'))
        val newct = HOLset.union(ct,vs)
    in mk_thm (newct,asl',w')
    end


fVar_Inst [("P",([("y",mem_sort N)],“y = n:mem(N)”))] 
(N_ind_P)





*)


(*
fun vl2vset l = foldr (fn (v,ss) => HOLset.add(ss,v)) essps l

fun fVar_Inst1 (pair as (P,(argl:(string * sort) list,Q))) f = 
    let val 
        fv0 = HOLset.union(fvf f,(HOLset.union(fvf Q,vl2vset argl)))
    in
    case view_form f of
        vfVar(P0,args0) =>
(*ListPair.map ListPair.foldl*)
(*mk_inst (zip argl args0)ListPair. [] *)
        if P0 = P then
            let val venv = match_tl essps (List.map mk_var argl) args0 emptyvd 
            in inst_form (mk_menv venv emptyfvd) Q
            end
(*if the number of arguments is wrong, or the sorts is wrong, then handle the matching exn by returning f *)
        else f
      | vConn(co,fl) => mk_conn co (List.map (fVar_Inst1 pair) fl)
      | vQ(q,n,s,b) => 
        if List.exists (fn (n0,s0) => (n0 = n andalso s0 = s))  argl
        then 
            mk_quant q n s (fVar_Inst1 pair b)
        else 
            let val (n',s') = dest_var $ pvariantt fv0 (mk_var(n,s))
            in
                mk_quant q n' s' (fVar_Inst1 pair b)
            end
      | vPred _ => f
end

fun fVar_Instl l f = 
    case l of [] => f
            | pair :: t => fVar_Inst1 pair (fVar_Instl t f)

fun fVar_Inst l th = 
    let val (ct,asl,w) = dest_thm th
        val asl' = List.map (fVar_Instl l) asl
        val w' = fVar_Instl l w
        val vs = bigunion (pair_compare String.compare sort_compare)
                          (List.map fvf (w' :: asl'))
        val newct = HOLset.union(ct,vs)
    in mk_thm (newct,asl',w')
    end


fVar_Inst [("P",([("y",mem_sort N)],“y = n:mem(N)”))] 
(N_ind_P)
*)




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

val asF_def = rel2fun |> spec_all |> undisch
                      |> uex_expand |> ex2fsym0 "asF" ["R"]
                      |> disch_all |> gen_all
                      |> store_as "asF_def";

val asF_App = asF_def |> spec_all |> undisch |> conjE1
                      |> disch_all |> gen_all
                      |> store_as "asF_App";

val is_asF = asF_def |> spec_all |> undisch |> conjE2
                      |> disch_all |> gen_all
                      |> store_as "is_asF";
 
local
val l = fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
 “App(f1:A~>B,a) = b”))] 
(AX1 |> qspecl [‘A’, ‘B’] |> uex_expand)
in
val fun_ext0 = prove_store("fun_ext0",
e0
(rpt strip_tac >> 
 strip_assume_tac l >> pop_assum (K all_tac) >>
 assume_tac rel2fun >>
 first_x_assum (qsspecl_then [‘R’] assume_tac) >>
 qby_tac ‘isFun(R)’ 
 >-- (rw[Fun_expand] >> arw[] >> 
     rpt strip_tac >-- (qexists_tac ‘App(f2,a)’ >> rw[]) >>
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum drule >> 
 pop_assum (strip_assume_tac o uex_expand) >>
 qsuff_tac ‘f1 = f & f2 = f’ >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
 >> (first_x_assum irule >> arw[]))
(form_goal
 “!A B f1:A~>B f2. (!a. App(f1,a) = App(f2,a)) ==> f1 = f2”));
end

val fun_ext = prove_store("fun_ext",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 drule fun_ext0 >> arw[])
(form_goal
 “!A B f1:A~>B f2. (!a. App(f1,a) = App(f2,a)) <=> f1 = f2”));



val _ = new_fun "o1" (fun_sort (mk_set "A") (mk_set "C"),
                     [("phi",fun_sort (mk_set "B") (mk_set "C")),
                      ("psi",fun_sort (mk_set "A") (mk_set "B"))])

local
val l = fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
 “App(f:A~>B,a) = b”))] 
(AX1 |> qspecl [‘A’, ‘B’] |> uex_expand)
in
val asR_ex = prove_store("asR_ex",
e0
(rpt strip_tac >> strip_assume_tac l >>
 qexists_tac ‘R’ >> arw[])
(form_goal
 “!A B f:A~>B.?R.!a b. Holds(R,a,b) <=> App(f,a) = b”));
end

val asR_def = asR_ex |> spec_all |> ex2fsym0 "asR" ["f"]
                     |> gen_all

val asR_Fun = prove_store("asR_Fun",
e0
(rpt strip_tac >> rw[Fun_expand] >>
 rw[asR_def] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘App(f,a)’ >> rw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A~>B. isFun(asR(f))”));

val o1_ex = prove_store("o1_ex",
e0
(rpt strip_tac >>
 qexists_tac ‘asF(asR(psi) o asR(phi))’ >> 
 qsspecl_then [‘psi’] assume_tac asR_Fun >>
 qsspecl_then [‘phi’] assume_tac asR_Fun >>
 qby_tac ‘isFun(asR(psi) o asR(phi))’ 
 >-- (irule o_Fun >> arw[]) >>
 drule asF_App >> arw[])
(form_goal
 “!A B phi:A~>B C psi:B~>C. ?f:A~>C. 
 !a c. App(f,a) = c <=> Holds(asR(psi) o asR(phi),a,c)”));

val o1_def = o1_ex |> spec_all |> ex2fsym0 "o1" ["psi","phi"]
                   |> gen_all

val o_App = prove_store("o_App",
e0
(rpt strip_tac >> flip_tac >> rw[o1_def] >>
 rw[GSYM o_def] >>
 qexists_tac ‘App(f,a)’ >> rw[asR_def])
(form_goal
 “!A B f:A~>B C g:B~>C a. App(g,(App(f,a))) = App(o1(g,f),a)”));


(*Thm_2_3_5*)
val To1_fun_uex = prove_store("To1_fun_uex",
e0
(strip_tac >> uex_tac >> qexists_tac ‘asF(To1(A))’ >> rw[] >>
 strip_tac >> irule is_asF >> rw[To1_Fun] >> rw[dot_def] >>
 rpt strip_tac >> 
 qspecl_then [‘A’] assume_tac To1_Fun >>
 drule Eval_def >> arw[dot_def]
 )
(form_goal
 “!A. ?!f:A~>1. T”));

val _ = new_pred "isPr" 
                 [("pi1",fun_sort (Cross (mk_set "A") (mk_set "B")) (mk_set "A")),("pi2",fun_sort (Cross (mk_set "A") (mk_set "B")) (mk_set "B"))]

val isPr_def = store_ax("isPr_def",
“!A B pj1:A * B ~>A pj2: A * B ~>B. isPr(pj1,pj2) <=>
 !X f:X~>A g:X~>B.?!fg:X ~> A * B. o1(pj1,fg) = f &  o1(pj2,fg) = g”)

val pi1_ex = prove_store("pi1_ex",
e0
(rpt strip_tac >> qexists_tac ‘asF(p1(A,B))’ >> rw[])
(form_goal “!A B. ?pi1. asF(p1(A,B)) = pi1”));

val pi1_def = pi1_ex |> spec_all |> ex2fsym0 "pi1" ["A","B"]
                     |> gen_all |> store_as "pi1_def";

val pi2_ex = prove_store("pi2_ex",
e0
(rpt strip_tac >> qexists_tac ‘asF(p2(A,B))’ >> rw[])
(form_goal “!A B. ?pi2. asF(p2(A,B)) = pi2”));


val pi2_def = pi2_ex |> spec_all |> ex2fsym0 "pi2" ["A","B"]
                     |> gen_all |> store_as "pi2_def";

val asR_o = prove_store("o_asR",
e0
(rpt strip_tac >> irule $ iffRL R_EXT >> rpt strip_tac >>
 rw[asR_def] >> rw[o1_def])
(form_goal
 “!A B f:A~>B C g:B~> C. asR(g) o asR(f) = asR(o1(g,f))”));


val asF_asR = prove_store("asF_asR",
e0
(rpt strip_tac >> irule fun_ext0 >> 
 qsspecl_then [‘f’] assume_tac asR_Fun >>
 strip_tac >> drule asF_App >> arw[] >>
 rw[asR_def])
(form_goal
 “!A B f:A~>B. asF(asR(f)) =f”));

val asR_asF = prove_store("asR_asF",
e0
(rpt strip_tac >> irule $ iffRL R_EXT >>
 rw[asR_def] >> drule asF_App >> arw[])
(form_goal
 “!A B f:A->B. isFun(f) ==> asR(asF(f)) =f”));

val asF_o1 = prove_store("asF_o1",
e0
(rpt strip_tac >> irule fun_ext0 >> strip_tac >>
 rw[o1_def] >>
 drule asR_asF >> rev_drule asR_asF >> arw[] >>
 qby_tac ‘isFun(g o f)’ >-- (irule o_Fun >> arw[]) >>
 drule Eval_def >> arw[] >> drule asF_App >> arw[])
(form_goal
 “!A B f:A->B C g:B-> C. 
  isFun(f) & isFun(g) ==>
  o1(asF(g),asF(f)) = asF(g o f)”));


val Eval_asR = prove_store("Eval_asR",
e0
(rpt strip_tac >> flip_tac >> rw[GSYM asR_def] >>
 qsspecl_then [‘f’] assume_tac asR_Fun >>
 drule Holds_Eval >> arw[])
(form_goal
 “!A B f:A~>B a. Eval(asR(f),a) = App(f,a)”));

val asR_eq_eq = prove_store("asR_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 once_rw[GSYM asF_asR] >> arw[])
(form_goal
 “!A B f:A~>B g. asR(f) = asR(g) <=> f = g”));


val Pf_ex = prove_store("Pf_ex",
e0
(rpt strip_tac >> rw[isPr_def] >> rpt strip_tac >>
 uex_tac >> qexists_tac ‘asF(Pa(asR(f),asR(g)))’ >>
 qsspecl_then [‘f’] assume_tac asR_Fun >>
 qsspecl_then [‘g’] assume_tac asR_Fun >>
 qspecl_then [‘A’,‘B’] assume_tac p12_Fun >>
 qby_tac ‘isFun(Pa(asR(f),asR(g)))’
 >-- (irule Pa_Fun >> arw[]) >> 
 qby_tac
 ‘o1(pi1(A, B), asF(Pa(asR(f), asR(g)))) = f’
 >-- (rw[GSYM pi1_def] >> 
     qsspecl_then [‘Pa(asR(f),asR(g))’,‘p1(A,B)’] assume_tac 
     asF_o1 >> rfs[] >>
     qsspecl_then [‘asR(f)’,‘asR(g)’] assume_tac p1_of_Pa >>
     rfs[] >> rw[asF_asR]) >>
 arw[] >> 
 qby_tac
 ‘o1(pi2(A, B), asF(Pa(asR(f), asR(g)))) = g’
 >-- (rw[GSYM pi2_def] >> 
     qsspecl_then [‘Pa(asR(f),asR(g))’,‘p2(A,B)’] assume_tac 
     asF_o1 >> rfs[] >>
     qsspecl_then [‘asR(f)’,‘asR(g)’] assume_tac p2_of_Pa >>
     rfs[] >> rw[asF_asR]) >>
 arw[] >> rpt strip_tac >>
 irule $ iffLR asR_eq_eq >>
 qby_tac ‘asR(asF(Pa(asR(f), asR(g)))) = Pa(asR(f), asR(g))’ 
 >-- (irule asR_asF >> arw[]) >>
 arw[] >> irule is_Pa >> arw[] >>
 rw[asR_Fun] >> 
 qsuff_tac ‘p2(A, B) o asR(fg')  = asR(o1(pi2(A, B), fg')) &
            p1(A, B) o asR(fg')  = asR(o1(pi1(A, B), fg'))’
 >-- (strip_tac >> arw[]) >>
 arw[] >> fs[GSYM pi1_def,GSYM pi2_def] >>
 qsspecl_then [‘fg'’] assume_tac asR_Fun >>
 qsspecl_then [‘asR(fg')’,‘p1(A, B)’] assume_tac asF_o1 >>
 rfs[] >>
 qsspecl_then [‘asR(fg')’,‘p2(A, B)’] assume_tac asF_o1 >>
 rfs[] >>
 fs[asF_asR] >> 
 qpick_x_assum
 ‘asF(p1(A, B) o asR(fg')) = f’ (assume_tac o GSYM) >> arw[] >>
 qpick_x_assum 
 ‘asF(p2(A, B) o asR(fg')) = g’ (assume_tac o GSYM) >> arw[] >>
 strip_tac >> 
 irule $ GSYM asR_asF >> irule o_Fun >> arw[])
(form_goal “!A B. isPr(pi1(A,B),pi2(A,B))”));
 
val Pf_def = Pf_ex |> rewr_rule[isPr_def]
                   |> spec_all
                   |> uex_expand |> ex2fsym0 "Pf" ["f","g"] 
                   |> gen_all

val App_asF_Eval = prove_store("App_asF_Eval",
e0
(rpt strip_tac >> drule asF_def >> arw[] >>
 drule Holds_Eval >> arw[])
(form_goal
 “!A B f:A->B. isFun(f) ==> !a.App(asF(f), a) = Eval(f,a)”));


val App_Eval_asR = prove_store("App_Eval_asR",
e0
(rpt strip_tac >> rw[GSYM asR_def] >> irule Holds_Eval >>
 rw[asR_Fun])
(form_goal
 “!A B f:A~>B. !a.App(f, a) = Eval(asR(f),a)”));


val pi1_of_Pair = prove_store("pi1_of_Pair",
e0
(rpt strip_tac >> rw[GSYM pi1_def] >> qspecl_then [‘A’,‘B’] assume_tac p1_Fun >> drule App_asF_Eval >> arw[] >> rw[Eval_p1_Pair])
(form_goal
 “!A B a b. App(pi1(A,B),Pair(a,b)) = a”));

val pi2_of_Pair = prove_store("pi2_of_Pair",
e0
(rpt strip_tac >> rw[GSYM pi2_def] >> qspecl_then [‘A’,‘B’] assume_tac p2_Fun >> drule App_asF_Eval >> arw[] >> rw[Eval_p2_Pair])
(form_goal
 “!A B a b. App(pi2(A,B),Pair(a,b)) = b”));

val List_rec_mem = prove_store("List_rec_mem",
e0
(rpt strip_tac >> drule List_rec >>
 pop_assum (strip_assume_tac o uex_expand) >>
 uex_tac >> qexists_tac ‘f’ >> arw[] >> rpt strip_tac (* 2 *)
 >-- (rw[GSYM CONS_def] >>
 irule $ iffLR Eval_o_l >> arw[] >> rw[Cons_def] >>
 irule $ iffRL Eval_o_l >> arw[] >>
 qby_tac ‘isFun(p1(A,List(A))) & isFun(f o p2(A,List(A)))’ 
 >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
 drule Pa_Fun >> arw[] >> irule Eval_input_eq >>
 drule Eval_Pa_Pair >> arw[] >> rw[Eval_p1_Pair] >>
 rw[Pair_eq_eq] >> irule $ iffRL Eval_o_l >>
 arw[Eval_p2_Pair,p2_Fun]) >>
 first_x_assum irule >> arw[] >> irule $ iffRL FUN_EXT >>
 qby_tac ‘isFun(f' o Cons(A))’ >-- (irule o_Fun >> arw[Cons_def]) >>
 qby_tac ‘isFun(t o Pa(p1(A, List(A)), f' o p2(A, List(A))))’ 
 >-- (irule o_Fun >> arw[] >> irule Pa_Fun >> rw[p1_Fun] >>
      irule o_Fun >> arw[p2_Fun]) >>
 arw[] >> strip_tac >> irule $ iffRL Eval_o_l >>
 arw[Cons_def] >> 
 qsspecl_then [‘a’] 
 (x_choosel_then ["a0","l0"] assume_tac) Pair_has_comp >>
 arw[CONS_def] >> flip_tac >> irule $ iffRL Eval_o_l >>
 arw[] >>
 qby_tac ‘isFun(Pa(p1(A, List(A)), f' o p2(A, List(A))))’
 >-- (irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
 arw[] >> irule Eval_input_eq >> 
 qby_tac
 ‘isFun(p1(A,List(A))) & isFun(f' o p2(A,List(A)))’
 >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
 drule Eval_Pa_Pair >> arw[Eval_p1_Pair] >> 
 rw[Pair_eq_eq] >> irule $ iffRL Eval_o_l >> 
 arw[p2_Fun] >> rw[Eval_p2_Pair])
(form_goal
 “!X x:mem(X) A t. isFun(t) ==> ?!f. isFun(f) & 
  Eval(f,Nil(A)) = x &
  !a l. Eval(f,CONS(a,l)) = Eval(t,Pair(a,Eval(f,l)))”));


val List_rec_fun = prove_store("List_rec_fun",
e0
(rpt strip_tac >> 
 qsspecl_then [‘x’,‘asR(t)’] assume_tac List_rec_mem >>
 qsspecl_then [‘t’] assume_tac asR_Fun >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 drule App_asF_Eval >> uex_tac >>
 qexists_tac ‘asF(f)’ >>
 arw[] >> rw[GSYM App_Eval_asR] >> rpt strip_tac >>
 irule $ iffLR asR_eq_eq >> drule asR_asF >> arw[] >>
 first_x_assum irule >> arw[asR_Fun,GSYM App_Eval_asR])
(form_goal
 “!X x A t. ?!f:List(A)~> X. 
 App(f,Nil(A)) = x &
 !a l. App(f,CONS(a,l)) = App(t,Pair(a,App(f,l)))
 ”));

val Eval_o_p2 = prove_store("Eval_o_p2",
e0
(rpt strip_tac >> irule $ iffRL Eval_o_l >>
 arw[p2_Fun] >> rw[Eval_p2_Pair])
(form_goal
 “!X B f:B->X. isFun(f) ==> !A a b. Eval(f o p2(A,B),Pair(a,b)) = Eval(f,b)”));

val Eval_o_p1 = prove_store("Eval_o_p1",
e0
(rpt strip_tac >> irule $ iffRL Eval_o_l >>
 arw[p1_Fun] >> rw[Eval_p1_Pair])
(form_goal
 “!X A f:A->X. isFun(f) ==> !B a b. Eval(f o p1(A,B),Pair(a,b)) = Eval(f,a)”));


val Thm1_mem = prove_store("Thm1_fun",
e0
(rpt gen_tac >> disch_tac >> drule Thm1 >> 
 pop_assum strip_assume_tac >> uex_tac >>
 qexists_tac ‘f’ >> 
 first_assum (qspecl_then [‘f’] assume_tac) >> fs[] >>
 strip_tac (* 2 *)
 >-- (rpt strip_tac (* 2 *) >-- 
     (qby_tac ‘ Eval(g, a) = Eval(g o p1(A, 1),Pair(a,dot))’ 
     >-- (flip_tac >> irule $ iffRL Eval_o_l >> rw[Eval_p1_Pair] >>
         arw[p1_Fun]) >>
     arw[] >>
     qpick_x_assum ‘f o Pa(p1(A, 1), El(O) o p2(A, 1)) = g o p1(A, 1)’
     (assume_tac o GSYM) >> arw[] >>
     flip_tac >> irule  $ iffRL Eval_o_l  >>
     qby_tac
     ‘isFun(Pa(p1(A, 1), El(O) o p2(A, 1)))’
     >-- (irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >>
          rw[p2_Fun,El_Fun]) >> arw[] >>
     irule Eval_input_eq >> 
     qby_tac ‘isFun(p1(A,1)) & isFun(El(O) o p2(A,1))’ 
     >-- (rw[p1_Fun] >> irule o_Fun >> rw[p2_Fun,El_Fun]) >>
     drule Eval_Pa_Pair >> arw[] >> rw[Pair_eq_eq,Eval_p1_Pair] >>
     irule $ iffRL Eval_o_l >> rw[El_Fun,p2_Fun] >>
     rw[El_def,dot_def]) >>
     qby_tac
     ‘Eval(f, Pair(a, Suc(n))) = Eval(f o Pa(p1(A, N), SUC o p2(A, N)),Pair(a,n))’
     >-- (flip_tac >> irule $ iffRL Eval_o_l >> 
         qby_tac ‘isFun(p1(A,N)) & isFun(SUC o p2(A, N))’
         >-- (rw[p1_Fun] >> irule o_Fun >> rw[SUC_Fun,p2_Fun]) >>
         drule Pa_Fun >> arw[] >>
         irule Eval_input_eq >> drule Eval_Pa_Pair >> 
         arw[Eval_p1_Pair] >> rw[Pair_eq_eq] >> 
         irule  $ iffRL Eval_o_l >> rw[p2_Fun,SUC_Fun] >>
         rw[Suc_def,Eval_p2_Pair]) >>
     arw[] >> pop_assum (K all_tac) >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     irule  $ iffRL Eval_o_l >> arw[] >>
     qby_tac ‘isFun(Pa(id(A * N), f))’ 
     >-- (irule Pa_Fun >> arw[id_Fun]) >>
     arw[] >> irule Eval_input_eq >> 
     qby_tac ‘isFun(id(A * N)) & isFun(f)’ 
     >-- arw[id_Fun] >>
     drule Eval_Pa_Pair >> arw[Eval_id]) >>
rpt strip_tac >>  first_x_assum (irule o iffLR) >>
arw[] >> strip_tac (* 2 *) >-- 
(irule $ iffRL FUN_EXT >> rpt strip_tac (* 3 *)
>-- (qsspecl_then [‘a’] (x_choosel_then ["a0","n0"] assume_tac)
    Pair_has_comp >> arw[] >> irule $ iffRL Eval_o_l >>
    arw[] >> 
    qsspecl_then [‘id(A * N)’,‘f'’] assume_tac Pa_Fun >>
    rfs[id_Fun] >> 
    qsspecl_then [‘id(A * N)’,‘f'’] assume_tac Eval_Pa_Pair >>
    rfs[id_Fun] >> rw[Eval_id] >> flip_tac >>
    irule  $ iffRL Eval_o_l >> 
    qby_tac ‘isFun(p1(A,N)) & isFun(SUC o p2(A,N))’
    >-- (rw[p1_Fun] >> irule o_Fun >> rw[SUC_Fun,p2_Fun]) >>
    arw[] >> drule Pa_Fun >> arw[] >> 
    drule Eval_Pa_Pair >> arw[Eval_p1_Pair] >>
    assume_tac SUC_Fun >> drule Eval_o_p2 >> arw[Suc_def])
>-- (irule o_Fun >> arw[] >> irule Pa_Fun >> arw[id_Fun]) >>
irule o_Fun >> arw[] >> irule Pa_Fun >> rw[p1_Fun] >>
irule o_Fun >> rw[SUC_Fun,p2_Fun]) >>
irule $ iffRL FUN_EXT  >> rpt strip_tac (* 3 *)
>-- (qsspecl_then [‘a’] (x_choosel_then ["a0","n0"] assume_tac)
    Pair_has_comp >> arw[] >>  irule $ iffRL Eval_o_l >> arw[] >>
    qby_tac ‘isFun(p1(A,1)) & isFun(El(O) o p2(A, 1))’
    >-- (rw[p1_Fun] >> irule o_Fun >> rw[El_Fun,p2_Fun]) >>
    drule Pa_Fun >> arw[] >> drule Eval_Pa_Pair >> arw[] >>
    rw[Eval_p1_Pair] >> qsspecl_then [‘O’] assume_tac El_Fun >>
    drule Eval_o_p2 >> arw[] >> rw[dot_def,El_def] >> arw[] >>
    rev_drule Eval_o_p1 >> arw[]) 
>-- (irule o_Fun >> arw[] >> irule Pa_Fun >> rw[p1_Fun] >>
    irule o_Fun >> rw[El_Fun,p2_Fun]) >>
irule o_Fun >> arw[p1_Fun])
(form_goal
 “!A B g:A->B h : (A * N) * B -> B. 
 isFun(g) & isFun(h) ==> 
 ?!f:A * N -> B. 
 isFun(f) & 
 (!a.Eval(f, Pair(a,O)) = Eval(g,a)) &
 (!a n. Eval(f,Pair(a,Suc(n))) = Eval(h,Pair(Pair(a,n),Eval(f,Pair(a,n)))))”));


val Thm1_fun = prove_store("Thm1_fun",
e0
(rpt strip_tac >> uex_tac >> 
 qby_tac ‘isFun(asR(g)) & isFun(asR(h))’
 >-- rw[asR_Fun] >>
 drule Thm1_mem >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘asF(f)’ >>
 strip_tac (* 2 *)
 >-- (rpt strip_tac (* 2 *)
     >-- (drule App_asF_Eval >> arw[] >> rw[Eval_asR]) >>
     drule App_asF_Eval >> arw[] >> rw[Eval_asR]) >>
 rpt strip_tac >> irule $ iffLR asR_eq_eq >>
 drule asR_asF >> arw[] >>
 first_x_assum irule >> rw[asR_Fun] >>
 arw[Eval_asR])
(form_goal
 “!A B g:A~>B h : (A * N) * B ~> B. 
  ?!f.
     (!a.App(f, Pair(a,O)) = App(g,a)) &
     (!a n. App(f,Pair(a,Suc(n))) = App(h,Pair(Pair(a,n),App(f,Pair(a,n)))))”));

val Hd_def0 = List_rec_fun |> qspecl [‘A’,‘Arb(A)’,‘A’,‘pi1(A,A)’]
                           |> uex_expand |> ex2fsym0 "Hd" ["A"]
                           |> gen_all |> store_as "Hd_def0";

val HD_ex = prove_store("HD_ex",
e0
(rpt strip_tac >> qexists_tac ‘App(Hd(A),l)’ >> rw[])
(form_goal
 “!A l. ?h. App(Hd(A),l) = h”));

val HD_def = HD_ex |> spec_all |> ex2fsym0 "HD" ["l"]
                   |> gen_all |> store_as "HD_def";

val HD = prove_store("HD",
e0
(rpt strip_tac >> rw[GSYM HD_def] >>
 qspecl_then [‘A’] strip_assume_tac Hd_def0 >>
 arw[] >> rw[pi1_of_Pair])
(form_goal
 “!A a:mem(A) l.HD(CONS(a,l)) = a”));


val CONS_ne_Nil = prove_store("CONS_ne_Nil",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac ‘sof(CONS(h,t)) = sof(Nil(A))’ 
 >-- arw[] >>
 fs[sof_Nil] >> pop_assum mp_tac >>
 rw[GSYM CONS_eqn] >> rw[Ins_NONEMPTY])
(form_goal “!A h t. ~(CONS(h,t) = Nil(A))”));

local
val l = 
fVar_Inst [("P",([("l",mem_sort (rastt "List(A)")),
                  ("t",mem_sort (rastt "List(A)"))],
“(l = Nil(A) & t = Nil(A)) | (?h t0. l = CONS(h,t0) & t = t0)”))]
(AX1 |> qspecl [‘List(A)’,‘List(A)’]) |> uex_expand
in
val Tl_ex0 = prove_store("Tl_ex0",
e0
(strip_tac >> strip_assume_tac l >>
 pop_assum (K all_tac) >> qexists_tac ‘R’ >> 
 qby_tac ‘isFun(R)’ >--
 (rw[Fun_expand] >> rpt strip_tac (* 2 *)
  >-- (qsspecl_then [‘a’] strip_assume_tac CONS_or_Nil 
      >-- (arw[] >> qexists_tac ‘Nil(A)’ >> rw[]) >>
      arw[] >> qexists_tac ‘l0’ >> disj2_tac >> 
      qexistsl_tac [‘a0’,‘l0’] >> arw[]) >>
  qsspecl_then [‘a’] strip_assume_tac CONS_or_Nil >--
  (fs[] >> rfs[GSYM CONS_ne_Nil]) >>
  fs[] >> rfs[CONS_ne_Nil] >> fs[CONS_eq_eq]) >>
 arw[] >> drule $ GSYM Eval_def >> flip_tac >> arw[] >>
 rpt strip_tac >> rw[CONS_ne_Nil] >>
 qexistsl_tac [‘a’,‘l’] >> rw[])
(form_goal
 “!A. ?tl. isFun(tl) & Eval(tl,Nil(A)) = Nil(A) & 
 (!a l. Eval(tl,CONS(a,l)) = l)”));
end

val Tl_ex = prove_store("Tl_ex",
e0
(strip_tac >>
 qspecl_then [‘A’] strip_assume_tac Tl_ex0 >>
 qexists_tac ‘asF(tl)’ >> drule App_asF_Eval >>
 arw[])
(form_goal
 “!A. ?tl. App(tl,Nil(A)) = Nil(A) & 
 (!a l. App(tl,CONS(a,l)) = l)”));

val Tl_def =  Tl_ex |> spec_all |> ex2fsym0 "Tl" ["A"]
                   |> gen_all |> store_as "Tl_def";

val TL_ex = prove_store("TL_ex",
e0
(rpt strip_tac >> qexists_tac ‘App(Tl(A),l)’ >> rw[])
(form_goal
 “!A l. ?h. App(Tl(A),l) = h”));

val TL_def = TL_ex |> spec_all |> ex2fsym0 "TL" ["l"]
                   |> gen_all |> store_as "TL_def";
 
val Cons_Fun = Cons_def |> spec_all |> conjE1 |> gen_all
                        |> store_as "Cons_Fun";



val TL = prove_store("TL",
e0
(rpt strip_tac >> rw[GSYM TL_def] >>
 qspecl_then [‘A’] strip_assume_tac Tl_def >> arw[])
(form_goal
 “!A. TL(Nil(A)) = Nil(A) & !a:mem(A) l.TL(CONS(a,l)) = l”));

(*Rel is still useful when want to prove well-defined*)

val m2r_ex = prove_store("m2r_ex",
e0
(cheat)
(form_goal
 “!A B m:mem(Exp(A,B)). ?f:A->B. isFun(f) & !a b. Holds(f,a,b) <=> 
  b = Eval(Ev(A,B),Pair(a,m)) ”));

val m2r_def = m2r_ex |> spec_all |> ex2fsym0 "m2r" ["m"]
                     |> gen_all |> store_as "m2r_def";

val Ro_ex = prove_store("Ro_ex",
e0
(cheat)
(form_goal
 “!B C f:C->B. isFun(f) ==> !A.?f1:Exp(B,A) -> Exp(C,A). isFun(f1) &
  !b2a c2a. Holds(f1,b2a,c2a) <=> 
  c2a = Tpm(m2r(b2a) o f)”)); 

val Ro_def = Ro_ex |> spec_all |> undisch |> spec_all 
                   |> ex2fsym0 "Ro" ["f","A"] |> gen_all
                   |> disch_all |> gen_all


val FrN_ex = prove_store("FrN_ex",
e0
()
(form_goal
 “!X f:X~>X. ?frn:N~>X.”));

val nth_def = Nind_def |> qspecl [‘A’,‘Ro(Tl0(A),A)’]
(*

val nth_def = Thm1_fun |> qspecl [‘1’,‘Exp(List(A),A)’,
                                   ‘asF(Tp1(asR(Hd(A))))’],
                                   ‘o1(,Tl(A))’]

[‘List(A)’,‘A’,‘Hd(A)’,‘’]
*)
