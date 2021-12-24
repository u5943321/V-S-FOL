
(*

!xs n. Card xs n ==> !x\in xs ==> Card (xs DELETE x)  (n - 1)

!x. x\notin xs ==> Card( x INSERT xs) (n + 1)


Card: Pow(X) -> N

can have a Card: Pow(X) -> N that map every infinite set to 0


define a choice function that 



CHOICE: Pow(A)->A.



“@a.”

Card: Fin(X) -> N

*)


val Ins_ex = 
fVar_Inst 
[("P",([("x",mem_sort (mk_set "X"))],
“x:mem(X) = x0 | IN(x,s0)”))] 
(IN_def_P_expand |> qspecl [‘X’]) |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
|> store_as "Ins_ex";





val Del_ex = 
fVar_Inst 
[("P",([("x",mem_sort (mk_set "X"))],
“IN(x,s0) & (~(x:mem(X) = x0))”))] 
(IN_def_P_expand |> qspecl [‘X’]) |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
|> store_as "Del_ex";


val Ins_def = Ins_ex |> spec_all |> ex2fsym0 "Ins" ["x0","s0"]
                     |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
                     |> store_as "Ins_def";



val Del_def = Del_ex |> spec_all |> ex2fsym0 "Del" ["s0","x0"]
                     |> qgen ‘x0’ |> qgen ‘s0’ |> qgen ‘X’
                     |> store_as "Del_def";

val Ins_property = Ins_def |> spec_all |> conjE1
                           |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
                           |> store_as "Ins_property";


val Del_property = Del_def |> spec_all |> conjE1
                           |> qgen ‘x0’ |> qgen ‘s0’ |> qgen ‘X’
                           |> store_as "Del_property";

val Del_Ins = prove_store("Del_Ins",
e0
(rpt strip_tac >> irule IN_EXT >> rw[GSYM Ins_property,GSYM Del_property] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >> ccontra_tac >> fs[])
(form_goal “!X x0:mem(X) xs0. (~IN(x0,xs0)) ==> Del(Ins(x0,xs0),x0) =xs0”));




val Ins_absorb = prove_store("Ins_absorb",
e0
(rpt strip_tac >> irule IN_EXT >> rw[GSYM Ins_property] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal “!X x0:mem(X) xs0. IN(x0,xs0) ==> Ins(x0,xs0) =xs0”));


val Empty_ex = 
fVar_Inst 
[("P",([("x",mem_sort (mk_set "X"))],
“F”))] 
(IN_def_P_expand |> qspecl [‘X’]) |> gen_all
|> store_as "Empty_ex";

val Empty_def = Empty_ex |> spec_all |> ex2fsym0 "Empty" ["X"] 
                         |> gen_all |> store_as "Empty_def";

val Empty_property = Empty_def |> spec_all |> conjE1 |> GSYM 
                               |> gen_all |> store_as "Empty_property";


val cFins_ex = 
fVar_Inst 
[("P",([("xss",mem_sort $ Pow $Pow (mk_set "X"))],
“IN(Empty(X),xss) & !xs0. IN(xs0,xss) ==> !x0. IN(Ins(x0,xs0),xss)”))] 
(IN_def_P_expand |> qspecl [‘Pow(Pow(X))’]) |> gen_all
|> store_as "cFins_ex";

val cFins_def =  cFins_ex |> spec_all |> ex2fsym0 "cFins" ["X"]
                       |> gen_all
                       |> store_as "cFins_def";

val cFins_property = cFins_def |> spec_all |> conjE1
                             |> gen_all |> store_as "cFins_property";   

val Fin_lemma = 
fVar_Inst 
[("P",([("xs",mem_sort $ Pow (mk_set "X"))],
“IN(xs,Eval(BI(Pow(X)),cFins(X)))”))]
(Thm_2_4 |> qspecl [‘Pow(X)’]) |> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all BI_property) 
|>conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all $ GSYM cFins_property) 
|> ex2fsym0 "Fins" ["X"] |> ex2fsym0 "FI" ["X"]


val Fin_lemma' = Fin_lemma |> conjE2 |> iffRL
                       |> allE (rastt "Eval(FI(X),b)")
                       |> C mp
                       (existsI ("b'",mem_sort (rastt "Fins(X)")) (rastt "b:mem(Fins(X))")
                                “Eval(FI(X), b) = Eval(FI(X), b')”
                                (refl (rastt "Eval(FI(X), b)")))
                       |> strip_all_and_imp
                       |> gen_all
                       |> disch_all
                       |> gen_all


val _ = new_pred "Fin" [("A",mem_sort $ Pow (mk_set "X"))]

val Fin_def = store_ax("Fin_def",
“!X A:mem(Pow(X)). Fin(A) <=> ?b:mem(Fins(X)). A = Eval(FI(X),b)”)

val Fin_property = prove_store("Fin_property",
e0
(rw[Fin_def] >> once_rw[GSYM Fin_lemma] >> rpt strip_tac >> 
 first_assum irule >> first_assum irule >> arw[])
(form_goal
 “!X. Fin(Empty(X)) & !A:mem(Pow(X)). Fin(A) ==> !x. Fin(Ins(x,A))”));

val Fin_ind = prove_store("Fin_ind",
e0
(strip_tac >> strip_tac >> disch_tac >> drule Fin_lemma' >>
 rw[Fin_def] >> rpt strip_tac >> arw[])
(form_goal
 “!X ss. (IN(Empty(X),ss) & 
  !xs0. IN(xs0,ss) ==> !x0. IN(Ins(x0,xs0),ss)) ==>
  !A. Fin(A) ==> IN(A,ss)”));


local
val l0 = 
(IN_def_P_expand |> qspecl [‘Pow(X)’]) 
in
val Fin_ind_P = prove_store("Fin_ind_P",
e0
(rpt strip_tac >> strip_assume_tac l0 >> pop_assum (K all_tac) >>
 qsuff_tac ‘IN(A,s)’
 >-- (strip_tac >> first_assum (qspecl_then [‘A’] assume_tac) >>
      accept_tac (dimp_mp_r2l (assume “P(A:mem(Pow(X))) <=> IN(A, s)”)
                              (assume “IN(A:mem(Pow(X)), s)”))) >>
 irule Fin_ind >> strip_tac (* 2 *)
 >-- first_assum accept_tac >>
 strip_tac >-- (first_assum (irule o iffLR) >> first_assum accept_tac) >>
 rpt strip_tac >> first_assum (irule o iffLR) >> 
 qsuff_tac ‘!x0. P(Ins(x0,xs0))’
 >-- (strip_tac >> first_assum (qspecl_then [‘x0’] accept_tac)) >>
 first_assum irule >> first_assum (irule o iffRL) >>
 first_assum accept_tac)
(form_goal
 “!X.(P(Empty(X)) & !xs0:mem(Pow(X)). P(xs0) ==> !x0. P(Ins(x0,xs0))) ==> 
  !A:mem(Pow(X)). Fin(A) ==> P(A)”));
end

(*hascard(0,Empty(X)) &
 !n xs. hascard(n,xs) ==> !x. x\notin xs ==> hascard(Suc(n),Ins(x,xs))*)

val BIGINTER_ex = prove_store("BIGINTER_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(BI(A),sss)’ >> rw[])
(form_goal
 “!A sss:mem(Pow(Pow(A))). ?isss.Eval(BI(A),sss) = isss”))


val BIGINTER_def = BIGINTER_ex |> spec_all |> ex2fsym0 "BIGINTER" ["sss"]
                               |> store_as "BIGINTER_def";

val IN_BIGINTER = BI_def |> rewr_rule[BIGINTER_def] |> spec_all |> conjE2 |> gen_all
                         |> store_as "IN_BIGINTER";


(*
local
val lemma = 
 fVar_Inst 
[("P",([("A",mem_sort$ Pow $ Cross N $Pow (mk_set "X"))],
“IN(Pair(O,Empty(X)),A) &
 (!n xs.IN(Pair(n,xs),A) ==> 
  !x0. (~(IN(x0,xs))) ==>IN(Pair(Suc(n),Ins(x0,xs)),A))”))] 
(IN_def_P_expand |> qspecl [‘Pow(N * Pow(X))’]) 
(*set of subsets contains hascard sets*)
val As_def = lemma |> ex2fsym0 "As" ["X"] |> conjE1 
                   |> gen_all |> GSYM
val U_ex_lemma = fVar_Inst 
[("P",([("nxs",mem_sort $ Cross N $Pow (mk_set "X"))],
“IN(nxs,BIGINTER(As(X)))”))]
(Thm_2_4 |> qspecl [‘N * Pow(X)’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all IN_BIGINTER)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all As_def)
val U_i_def = U_ex_lemma |> ex2fsym0 "U" ["X"] |>ex2fsym0 "i" ["X"]
val IN_U = U_i_def |> conjE2 |> gen_all |> 
conv_rule $ basic_once_fconv no_conv (rewr_fconv (eq_sym "mem"))
|> GSYM
val rel_ex_lemma = 
fVar_Inst 
[("P",([("n",mem_sort N),("xs",mem_sort $Pow (mk_set "X"))],
“?r.Eval(i(X):U(X)-> N * Pow(X),r) = Pair(n,xs)”))]
(AX1 |> qspecl [‘N’,‘Pow(X)’]) |> uex_expand |> ex2fsym0 "hasCard" ["X"]
|> conjE1
|> conv_rule $ basic_once_fconv no_conv (rewr_fconv (spec_all IN_U))
*)








val lemma = 
 fVar_Inst 
[("P",([("A",mem_sort$ Pow $ Cross (Pow (mk_set "X")) N)],
“IN(Pair(Empty(X),O),A) &
 (!xs n.IN(Pair(xs,n),A) ==> 
  !x0. (~(IN(x0,xs))) ==>IN(Pair(Ins(x0,xs),Suc(n)),A))”))] 
(IN_def_P_expand |> qspecl [‘Pow(Pow(X) * N)’]) 
(*set of subsets contains hascard sets*)
val As_def = lemma |> ex2fsym0 "As" ["X"] |> conjE1 
                   |> gen_all |> GSYM
val U_ex_lemma = fVar_Inst 
[("P",([("nxs",mem_sort $ Cross (Pow (mk_set "X")) N)],
“IN(nxs,BIGINTER(As(X)))”))]
(Thm_2_4 |> qspecl [‘Pow(X) * N’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all IN_BIGINTER)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all As_def)
val U_i_def = U_ex_lemma |> ex2fsym0 "U" ["X"] |>ex2fsym0 "i" ["X"]
val IN_U = U_i_def |> conjE2 |> gen_all |> 
conv_rule $ basic_once_fconv no_conv (rewr_fconv (eq_sym "mem"))
|> GSYM
val Card_lemma = 
fVar_Inst 
[("P",([("xs",mem_sort $Pow (mk_set "X")),("n",mem_sort N)],
“?r.Eval(i(X):U(X)-> Pow(X) * N,r) = Pair(xs,n)”))]
(AX1 |> qspecl [‘Pow(X)’,‘N’]) |> uex_expand |> ex2fsym0 "Card" ["X"]
|> conjE1
|> conv_rule $ basic_once_fconv no_conv (rewr_fconv (spec_all IN_U))
val _ = new_pred "hasCard" [("xs",mem_sort $Pow (mk_set "X")),("n",mem_sort N)]
val hasCard_def = store_ax("hasCard_def",
“!X xs:mem(Pow(X)) n.hasCard(xs,n) <=> Holds(Card(X),xs,n)”)

val Card_def' = Card_lemma |> rewr_rule[GSYM hasCard_def]


val Fin_ind_card = 
fVar_Inst 
[("P",([("xs",mem_sort $ Pow (mk_set "X"))],
“?!n.hasCard(xs:mem(Pow(X)),n)”))]
(Fin_ind_P |> qspecl [‘X’])

val hasCard_Empty = prove_store("hasCard_property",
e0
(rw[Card_def'] >> rpt strip_tac)
(form_goal
 “!X.hasCard(Empty(X),O)”));

val hasCard_Ins = prove_store("hasCard_Ins",
e0
(rw[Card_def'] >> rpt strip_tac >>
 first_assum irule >> arw[] >> first_assum irule >> arw[])
(form_goal
 “!X xs:mem(Pow(X)) n.hasCard(xs,n) ==>
  !x0. (~(IN(x0,xs))) ==> hasCard(Ins(x0,xs),Suc(n))”));




val Ins_NONEMPTY = prove_store("Ins_NONEMPTY",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac
 ‘!x. IN(x,Ins(x0,xs)) <=> IN(x,Empty(X))’ >-- arw[] >>
 fs[Empty_property,GSYM Ins_property] >>
 first_x_assum (qspecl_then [‘x0’] assume_tac) >> fs[])
(form_goal
 “!X x0 xs:mem(Pow(X)).~(Ins(x0,xs) = Empty(X))”));

val IN_Ins_SND = prove_store("IN_Ins_SND",
e0
(rw[GSYM Ins_property] >> rpt strip_tac)
(form_goal “!X x0 xs0:mem(Pow(X)) x. IN(x, Ins(x0, xs0)) & (~(x = x0)) ==> IN(x,xs0)”));

local
val l = 
fVar_Inst 
[("P",([("xsns",mem_sort $ Cross (Pow $ mk_set "X") N)],
“hasCard(Fst(xsns),Snd(xsns)) & 
 ~(Fst(xsns) = Empty(X) & Snd(xsns) = n)”))] 
(IN_def_P_expand |> qspecl [‘(Pow(X) * N)’])
in 
val Card_Empty_unique = prove_store("Card_Empty_unique",
e0
(rpt strip_tac >> ccontra_tac >>
 qsuff_tac
 ‘?ss. IN(Pair(Empty(X),O),ss) &
  (!xs n. IN(Pair(xs,n),ss) ==>
   !x0. (~IN(x0,xs)) ==> IN(Pair(Ins(x0,xs),Suc(n)),ss)) &
  ~(IN(Pair(Empty(X),n),ss))’
 >-- (fs[Card_def'] >>
     ccontra_tac >> pop_assum strip_assume_tac >>
     qsuff_tac ‘IN(Pair(Empty(X), n), ss)’ >-- arw[] >>
     first_assum irule >> arw[]) >>
 strip_assume_tac l >> pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> qexists_tac ‘s’ >>
 once_arw[] >>
 rw[Pair_def'] >> rw[hasCard_Empty] >> strip_tac 
 >-- (flip_tac >> first_assum accept_tac) >>
 strip_tac >> strip_tac >>  (*do not know why does not work if not strip,
 maybe know, how to fix?
*)
 arw[] >>
 rw[Pair_def'] >> rpt strip_tac >--
 (irule hasCard_Ins >> arw[]) >> 
 qsuff_tac
 ‘~(Ins(x0,xs) = Empty(X))’ >-- (strip_tac >> arw[]) >>
 rw[Ins_NONEMPTY]
 )
(form_goal
 “!X n.hasCard(Empty(X),n) ==> n = O”));
end


val hasCard_ind = prove_store("hasCard_ind",
e0
(once_rw[Card_def'] >> rpt strip_tac >>
 first_assum irule >> arw[])
(form_goal
“!X ss. IN(Pair(Empty(X),O),ss) & 
      (!xs n. IN(Pair(xs,n),ss) ==>
       !x0. (~IN(x0,xs)) ==> IN(Pair(Ins(x0,xs),Suc(n)),ss)) ==>
      !xs n.hasCard(xs,n) ==> IN(Pair(xs,n),ss) ”));

val Del_Ins_SWAP = prove_store("Del_Ins_SWAP",
e0
(rpt strip_tac >> irule IN_EXT >> rw[GSYM Ins_property,GSYM Del_property] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X x0 x:mem(X).(~(x0 = x)) ==> !xs.Del(Ins(x0, xs), x) = Ins(x0,Del(xs,x))”));




local
val l = 
fVar_Inst 
[("P",([("xsns",mem_sort $ Cross (Pow $ mk_set "X") N)],
“hasCard(Fst(xsns),Snd(xsns)) & !x0:mem(X) xs0. Fst(xsns) = Ins(x0,xs0) ==> ?n0. Snd(xsns) = Suc(n0)”))] 
(IN_def_P_expand |> qspecl [‘(Pow(X) * N)’])
in
val hasCard_Ins_Suc = prove_store("hasCard_Ins_Suc",
e0
(strip_tac >> strip_assume_tac l >> pop_assum (K all_tac) >>
 qsuff_tac ‘!xs n.hasCard(xs,n) ==> IN(Pair(xs,n),s)’ 
 >-- (pop_assum (assume_tac o GSYM) >> arw[Pair_def']) >>
 strip_tac >> strip_tac >> match_mp_tac hasCard_ind >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rw[Pair_def'] >> 
 rw[hasCard_Empty] >> rpt strip_tac (* 3 *)
 >-- (qby_tac ‘IN(x0,Ins(x0,xs0))’ >-- fs[GSYM Ins_property] >>
     qpick_x_assum ‘Empty(X) = Ins(x0, xs0)’ (assume_tac o GSYM) >>
     fs[Empty_property]) 
 >-- (drule hasCard_Ins >> first_assum drule >> arw[]) >>
 qexists_tac ‘n'’ >> rw[])
(form_goal
 “!X xs:mem(Pow(X)) n. hasCard(xs,n) ==> hasCard(xs,n) & !x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0)”));
end

local
val l = 
fVar_Inst 
[("P",([("xsns",mem_sort $ Cross (Pow $ mk_set "X") N)],
“hasCard(Fst(xsns),Snd(xsns)) & !x. IN(x:mem(X),Fst(xsns)) ==> hasCard(Del(Fst(xsns),x),Pre(Snd(xsns)))”))] 
(IN_def_P_expand |> qspecl [‘(Pow(X) * N)’])
in
val hasCard_Del = prove_store("hasCard_Del",
e0
(strip_tac >> strip_assume_tac l >> pop_assum (K all_tac) >>
 qsuff_tac ‘!xs n.hasCard(xs,n) ==> IN(Pair(xs,n),s)’  >--
 (rpt strip_tac >> first_x_assum drule >> 
  first_x_assum (qspecl_then [‘Pair(xs,n)’] assume_tac) >> 
  pop_assum (assume_tac o GSYM) >> fs[] >> fs[Pair_def'] >> first_x_assum drule >>
  arw[]) >>
 strip_tac >> strip_tac >>
 match_mp_tac hasCard_ind >> (*
 qby_tac 
 ‘!xs n. (!x.IN(x,xs) ==> hasCard(Del(xs,x),Pre(n))) <=> IN(Pair(xs,n),s)’
 >-- (rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[Pair_def']) >>*)
 pop_assum (assume_tac o GSYM) >> arw[] >> rpt strip_tac (* 2 *)
 >-- fs[Pair_def',hasCard_Empty] >-- fs[Empty_property,Pair_def'] >--
 (fs[Pair_def'] >> drule hasCard_Ins >> first_x_assum drule >> arw[]) >>
 fs[Pair_def'] >>
 cases_on “x:mem(X) = x0” >--
 (fs[] >> drule Del_Ins >> arw[Pre_Suc]) >> 
 qby_tac ‘IN(x,xs')’ >-- (irule IN_Ins_SND >> qexists_tac ‘x0’ >> arw[]) >>
 first_x_assum drule >>  
 qpick_x_assum ‘~(x = x0)’ (assume_tac o GSYM) >>
 drule Del_Ins_SWAP >> arw[] >> drule hasCard_Ins >> 
 qby_tac ‘~(IN(x0,Del(xs',x)))’ >--
 (rw[GSYM Del_property] >> arw[]) >>
 first_x_assum drule >> rw[Pre_Suc] >>
 cases_on “n' = O”
 >-- (fs[] >>
     drule Ins_absorb >>
     qby_tac ‘hasCard(Ins(x, xs'), O)’ >-- arw[] >>
     drule hasCard_Ins_Suc >> pop_assum strip_assume_tac >>
     first_x_assum (qspecl_then [‘x’,‘xs'’] assume_tac) >> fs[GSYM Suc_NONZERO])>>
 fs[O_xor_Suc] >> fs[] >>
 fs[Pre_Suc])
(form_goal
 “!X xs:mem(Pow(X)) n.hasCard(xs,n) ==> hasCard(xs,n) & 
  !x. IN(x,xs) ==> hasCard(Del(xs,x),Pre(n))”));
end







val Fin_Card = prove_store("Card_Fun",
e0
(rw[Fun_expand,Card_lemma] >> strip_tac >> match_mp_tac Fin_ind_card >>
 strip_tac >--
 (uex_tac >> qexists_tac ‘O’ >> rw[hasCard_Empty] >> rpt strip_tac >> drule Card_Empty_unique >> arw[]) >>
 rpt strip_tac >> pop_assum (strip_assume_tac o uex_expand) >> uex_tac >>
 cases_on “IN(x0,xs0:mem(Pow(X)))” 
 >-- (qexists_tac ‘n’ >> 
     qby_tac ‘Ins(x0,xs0) = xs0’ 
     >-- (irule Ins_absorb >> arw[]) >> arw[]) >>    
 qexists_tac ‘Suc(n)’ >> drule hasCard_Ins >> first_x_assum drule >> arw[] >>
 rpt strip_tac >> 
 drule hasCard_Del >>
 fs[] >>
 qby_tac ‘IN(x0, Ins(x0, xs0))’ >-- fs[GSYM Ins_property] >>
 first_x_assum drule >> drule Del_Ins >> fs[] >> first_x_assum drule >>
 qpick_x_assum ‘hasCard(Ins(x0, xs0), n')’ (assume_tac o GSYM) >>
 drule hasCard_Ins_Suc >> fs[] >>
 first_x_assum (qspecl_then [‘x0’,‘xs0’] assume_tac) >> fs[] >>
 fs[] >> fs[Pre_Suc])
(form_goal
 “!X xs:mem(Pow(X)).Fin(xs) ==> ?!n.hasCard(xs,n)”));




val Card_def = 
 fVar_Inst 
[("P",([("xs",mem_sort $ Pow (mk_set "X")),
        ("n",mem_sort N)],
“(Fin(xs:mem(Pow(X))) & hasCard(xs,n)) | (~Fin(xs) & n = O)”))]
(AX1 |> qspecl [‘Pow(X)’,‘N’]) 
|> uex_expand |> ex2fsym0 "Card" ["X"] |> conjE1
|> gen_all 
|> store_as "Card_def";

val Card_Fun = prove_store("Card_Fun",
e0
(rw[Fun_expand,Card_def] >> rpt strip_tac (* 3 *)
 >-- (cases_on “Fin(a:mem(Pow(X)))” (* 2 *)
     >-- (drule Fin_Card >> 
         pop_assum (strip_assume_tac o uex_expand) >>
         qexists_tac ‘n’ >> arw[]) >>
     qexists_tac ‘O’ >> arw[])
 >-- (drule Fin_Card >> pop_assum (strip_assume_tac o uex_expand)>>
     first_assum rev_drule >> arw[] >> flip_tac >>
     first_assum irule >> arw[]) >>
 arw[])
(form_goal 
 “!X. isFun(Card(X))”));
 
val CARD_ex = prove_store("CARD_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(Card(X),xs)’ >> rw[])
(form_goal
 “!X xs:mem(Pow(X)). ?cxs. Eval(Card(X),xs) = cxs”));

val CARD_def = CARD_ex |> spec_all |> ex2fsym0 "CARD" ["xs"]
                       |> gen_all |> store_as "CARD_def"; 

 
val Fin_Empty= Fin_property |> spec_all |> conjE1
                            |> gen_all |> store_as "Fin_Empty";

val Fin_Ins = Fin_property |> spec_all |> conjE2
                            |> gen_all |> store_as "Fin_Ins";

val Del_Empty = prove_store("Del_Empty",
e0
(rpt strip_tac >> match_mp_tac IN_EXT >>
  rw[GSYM Del_property,Empty_property])
(form_goal
 “!X x. Del(Empty(X),x) = Empty(X)”));

val IN_Ins =  GSYM Ins_property |> store_as "IN_Ins";

val Ins_eq_eq = prove_store("Ins_eq_eq",
e0
(rpt strip_tac >-- (ccontra_tac >>
 qsuff_tac ‘~(IN(a2,Ins(a2,s2)))’
 >-- rw[GSYM Ins_property] >>
 qsuff_tac ‘~(IN(a2,Ins(a1,s1)))’
 >-- arw[] >>
 rw[IN_Ins] >> arw[] >> flip_tac >> first_x_assum accept_tac) >>
 irule IN_EXT >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘IN(x,Ins(a1,s1))’ >-- arw[IN_Ins] >> rfs[] >>
      fs[IN_Ins] >> pop_assum (assume_tac o GSYM) >> fs[]) >>
 qpick_x_assum ‘Ins(a1, s1) = Ins(a2, s2)’ (assume_tac o GSYM) >>
 qby_tac ‘IN(x,Ins(a2,s2))’ >-- arw[IN_Ins] >>
 rfs[] >> fs[IN_Ins] >> pop_assum (assume_tac o GSYM) >> fs[]
 )
(form_goal
 “!A a1:mem(A) s1 a2 s2. ~(IN(a1,s1)) & ~(IN(a2,s2)) & ~(IN(a1,s2)) & ~(IN(a2,s1)) & 
 Ins(a1,s1) = Ins(a2,s2) ==> a1 = a2 & s1 = s2”));


local
val l = fVar_Inst 
[("P",([("xs",mem_sort $ Pow (mk_set "X"))],
“Fin(xs) & !x. Fin(Del(xs,x:mem(X)))”))]
(Fin_ind_P |> qspecl [‘X’])
in
val Fin_Del0 = prove_store("Fin_Del",
e0
(strip_tac >> strip_tac >> match_mp_tac l >>
 rw[Del_Empty,Fin_Empty] >> rpt strip_tac >--
 (drule Fin_Ins >> arw[]) >>
 cases_on “x = x0:mem(X)” 
 >-- (arw[] >> cases_on “IN(x0:mem(X),xs0)”
      >-- (drule Ins_absorb >> arw[]) >>
      drule Del_Ins >> arw[]) >>
 pop_assum (assume_tac o GSYM) >>
 drule Del_Ins_SWAP >> arw[]>> 
 last_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Fin_Ins >> arw[])
(form_goal
 “!X xs:mem(Pow(X)).Fin(xs) ==> Fin(xs) &  !x. Fin(Del(xs,x)) ”));
end

val Fin_Del = prove_store("Fin_Del",
e0
(rpt strip_tac >> drule Fin_Del0 >> arw[])
(form_goal “!X xs:mem(Pow(X)).Fin(xs) ==> !x. Fin(Del(xs,x))”));

val Card_Fin = prove_store("Card_Fin",
e0
(rpt strip_tac >> rw[GSYM CARD_def] >> assume_tac Card_def >>
 first_x_assum (qspecl_then [‘X’,‘xs’,‘n’] assume_tac) >>
 rfs[] >> pop_assum (assume_tac o GSYM)>> arw[] >>
 qspecl_then [‘X’] assume_tac Card_Fun >>
 drule Eval_def >> arw[] >> lflip_tac >> rw[])
(form_goal
 “!X xs:mem(Pow(X)). Fin(xs) ==>
  (!n. CARD(xs) = n <=> hasCard(xs,n))”));


val CARD_Empty = prove_store("CARD_Empty",
e0
(assume_tac Fin_Empty >> strip_tac >>
 first_x_assum $ qspecl_then [‘X’] assume_tac >>
 drule Card_Fin >> arw[] >> rw[hasCard_Empty])
(form_goal
 “!X. CARD(Empty(X)) = O”));

val CARD_Ins = prove_store("CARD_Ins",
e0
(rpt strip_tac >> drule Fin_Ins >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Card_Fin >> arw[] >> irule hasCard_Ins >>
 arw[] >> rev_drule $ GSYM Card_Fin >> arw[])
(form_goal
 “!X xs:mem(Pow(X)). 
  Fin(xs) ==> !x.~(IN(x,xs)) ==> CARD(Ins(x,xs)) = Suc(CARD(xs))”));

val hasCard_Del' = hasCard_Del |> strip_all_and_imp 
                               |> conjE2 |> disch_all 
                               |> gen_all
                               |> store_as "hasCard_Del'";

val CARD_Del = prove_store("CARD_Del",
e0
(rpt strip_tac >> drule Fin_Del >> 
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Card_Fin >> arw[] >>
 irule hasCard_Del' >> arw[] >>
 rev_drule Card_Fin >> pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!X xs:mem(Pow(X)). Fin(xs) ==> 
  !x. IN(x,xs) ==> CARD(Del(xs,x)) = Pre(CARD(xs))”));
 


(*

 Card_def' |> spec_all |> iffRL

val hasCard_Ins_pre = prove_store("hasCard_Ins_pre",
e0
(rw[Card_def'] >>
 rpt strip_tac (* 2 *)
 >-- (first_assum irule >> arw[]) >>
 


 >-- first_assum accept_tac >> 
 first_assum irule
 )
(form_goal
 “!X xs:mem(Pow(X)) n. hasCard(xs,n) ==> hasCard(xs,n) & 
  (!x0 xs0 n0. (~IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) ==> hasCard(xs0,n0))”));

val Fin_Card = prove_store("Card_Fun",
e0
(rw[Fun_expand,Card_lemma] >> strip_tac >> match_mp_tac Fin_ind_card >>
 strip_tac >-- cheat >>
 rpt strip_tac >> )
(form_goal
 “!X xs:mem(Pow(X)).Fin(xs) ==> ?!n.hasCard(xs,n)”));


val rel_ex_lemma = 
fVar_Inst 
[("P",([("n",mem_sort N),("xs",mem_sort $Pow (mk_set "X"))],
“?r.Eval(u0:U-> N * Pow(X),r) = Pair(n,xs)”))]
(AX1 |> qspecl [‘N’,‘Pow(X)’]) |> uex_expand
val hasCard_ex = prove_store("hasCard_ex",
e0
()
(form_goal
 “!X. ?hc. IN(Pair(O,Empty(X)),hc) & 
 !x0. ”));



(*union is finite <=> A and B are finite*)

end
*)
