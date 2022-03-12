
(* inNf X = {0} ∪ {x + 1 | x ∈ X} *)

val inNf_ex = prove_store("inNf_ex",
e0
(cheat)
(form_goal “∃f. ∀p:mem(Pow(N0)). (∀x. IN(x,App(f,p)) ⇔ 
 (x = O0 | 
           ∃n0:mem(N0). IN(n0,p) ∧ x = App(S1,n0)) )”));

val inNf_def = inNf_ex |> ex2fsym0 "inNf" []


(* FIf xss = {∅_X} ∪ {{x} ∪ xs | x ∈ X | xs ∈ xss} *)
val FIf_ex = prove_store("FIf_ex",
e0
(cheat)
(form_goal
 “∃f. ∀p:mem(Pow(Pow(X))). (∀xs. IN(xs,App(f,p)) ⇔ 
 (xs = Empty(X) | 
  ∃xs0:mem(Pow(X)) x. IN(xs0,p) ∧ xs = Ins(x,xs0)) )”));

val FIf_def = FIf_ex |> ex2fsym0 "FIf" ["X"]


val FIf_monotone = prove_store("FIf_monotone",
e0
(cheat)
(form_goal “∀s1 s2. SS(s1,s2) ⇒ SS(App(FIf(X),s1), App(FIf(X),s2))”));


val FI's_def = 
    IN_def_P_ex |> allE (rastt "Pow(Pow(X))") |> GSYM
                |> fVar_sInst_th “P(a:mem(Pow(Pow(X))))” 
                “SS(App(FIf(X),a:mem(Pow(Pow(X)))), a)”
                |> ex2fsym0 "FI's" ["X"]
                |> store_as "FI's_def";

val FIs_ex = prove_store("FIs_ex",
e0
(qexists_tac ‘BIGINTER(FI's(X))’ >> rw[])
(form_goal “∃FIs. FIs = BIGINTER(FI's(X))”));

val FIs_def = FIs_ex |> ex2fsym0 "FIs" ["X"]


val FIs_SS = prove_store("FIs_SS",
e0
(cheat)
(form_goal 
“∀xs.SS(App(FIf(X), xs), xs) ⇒ SS(FIs(X), xs)”));

val FIs_cond = prove_store("FIs_cond",
e0
(cheat)
(form_goal 
“∀a.(!xs. SS(App(FIf(X), xs), xs) ==> IN(a, xs)) ⇔ IN(a,FIs(X))”));



val Cdf_ex = prove_store("Cdf_ex",
e0
(cheat)
(form_goal
 “∃f. ∀p:mem(Pow(Pow(X) * N)). (∀xsn. IN(xsn,App(f,p)) ⇔ 
 (xsn = Pair(Empty(X),O) | 
  ∃xsn0 x. IN(xsn0,p) ∧ xsn = Pair(Ins(x,Fst(xsn0)),Suc(Snd(xsn0)))) )”));

val Cdf_def = Cdf_ex |> ex2fsym0 "Cdf" ["X"]


val Cdf_monotone = prove_store("Cdf_monotone",
e0
(cheat)
(form_goal “∀s1 s2. SS(s1,s2) ⇒ SS(App(Cdf(X),s1), App(Cdf(X),s2))”));


val Cd's_def = 
    IN_def_P_ex |> allE (rastt "Pow(Pow(X) * N)") |> GSYM
                |> fVar_sInst_th “P(a:mem(Pow(Pow(X) * N)))” 
                “SS(App(Cdf(X),a:mem(Pow(Pow(X) * N))), a)”
                |> ex2fsym0 "Cd's" ["X"]
                |> store_as "Cd's_def";

val Cds_ex = prove_store("Cds_ex",
e0
(qexists_tac ‘BIGINTER(Cd's(X))’ >> rw[])
(form_goal “∃Cds. Cds = BIGINTER(Cd's(X))”));

val Cds_def = Cds_ex |> ex2fsym0 "Cds" ["X"]


val Cds_SS = prove_store("Cds_SS",
e0
(cheat)
(form_goal 
“∀xs.SS(App(Cdf(X), xs), xs) ⇒ SS(Cds(X), xs)”));




val Cds_cond = prove_store("Cds_cond",
e0
(cheat)
(form_goal 
“∀a.(!xs. SS(App(Cdf(X), xs), xs) ==> IN(a, xs)) ⇔ IN(a,Cds(X))”));

(*
“∀ls. ls = Empty(N * X) ⇒ IN(ls,p) ∧ 
      (∀)
 ”

*)
val isLf_ex = prove_store("isLf_ex",
e0
(cheat)
(form_goal
 “∃f. ∀p:mem(Pow(Pow(N * X))). (∀ls. IN(ls,App(f,p)) ⇔ 
 (ls = Empty(N * X) | 
  ∃ls0 x. IN(ls0,p) ∧ ls = Ins(Pair(CARD(ls0),x),ls0)))”));

val isLf_def = isLf_ex |> ex2fsym0 "isLf" ["X"]


val isLf_monotone = prove_store("isLf_monotone",
e0
(cheat)
(form_goal “∀s1 s2. SS(s1,s2) ⇒ SS(App(isLf(X),s1), App(isLf(X),s2))”));


val isL's_def = 
    IN_def_P_ex |> allE (rastt "Pow(Pow(N * X))") |> GSYM
                |> fVar_sInst_th “P(a:mem(Pow(Pow(N * X))))” 
                “SS(App(isLf(X),a:mem(Pow(Pow(N * X)))), a)”
                |> ex2fsym0 "isL's" ["X"]
                |> store_as "isL's_def";

val isLs_ex = prove_store("isLs_ex",
e0
(qexists_tac ‘BIGINTER(isL's(X))’ >> rw[])
(form_goal “∃isLs. isLs = BIGINTER(isL's(X))”));

val isLs_def = isLs_ex |> ex2fsym0 "isLs" ["X"]


val isLs_SS = prove_store("isLs_SS",
e0
(cheat)
(form_goal 
“∀xs.SS(App(isLf(X), xs), xs) ⇒ SS(isLs(X), xs)”));




val isLs_cond = prove_store("isLs_cond",
e0
(cheat)
(form_goal 
“∀a.(!xs. SS(App(isLf(X), xs), xs) ==> IN(a, xs)) ⇔ IN(a,isLs(X))”));

val (monotone,SS,cond) = (inNf_monotone,inNs_SS,inNs_cond);
val (monotone,SS,cond) = (FIf_monotone,FIs_SS,FIs_cond);
val (monotone,SS,cond) = (Cdf_monotone,Cds_SS,Cds_cond);
val (monotone,SS,cond) = (isLf_monotone,isLs_SS,isLs_cond);

fun mk_App fnterm arg = mk_fun "App" [fnterm,arg];

fun mk_rules monotone SS cond = 
    let val fnterm = monotone |> concl |> #1 o strip_forall
                              |> #2 o dest_imp |> #2 o dest_pred
                              |> hd |> #3 o dest_fun
                              |> hd
        val LFP = cond |> concl |> #1 o strip_forall
                       |> #2 o dest_dimp |> #2 o dest_pred |> el 2
        val st_genset = sort_of LFP
        val LFP_in = st_genset |> hd o #2 o dest_sort
        val LFP_inpow = LFP_in |> hd o #3 o dest_fun
        val avoids = HOLset.union(HOLset.union(cont monotone,cont SS),cont cond)
        val genset = pvariantt avoids (mk_var ("s0",st_genset))
        val fLFP = mk_App fnterm LFP
        val th_stment = mk_pred "SS" [fLFP,genset]
        val ori_goal = assume th_stment
        val expand_SS0 = ori_goal |> rewr_rule[SS_def]
        val ((memn,mems),_) = dest_forall (concl expand_SS0)
        val expand_SS = expand_SS0 |> strip_all_and_imp
        val itmd_set = mk_App fnterm genset
        val spec_trans = SS_Trans |> specl [LFP_inpow,fLFP,itmd_set]
                                  |> undisch
                                  |> specl [genset]
                                  |> undisch
        val by_trans = expand_SS |> prove_hyp spec_trans
        val spec_monotone = monotone |> specl [LFP,genset] |> undisch
        val by_monotone = by_trans |> prove_hyp spec_monotone
        val spec_SS = SS |> specl [genset] |> undisch
        val by_SS = by_monotone |> prove_hyp spec_SS
        val SS_assum = mk_pred "SS" [mk_App fnterm genset,genset]
        val disch_SS_assum = by_SS |> disch SS_assum
        val vgenset = dest_var genset
        val by_cond = disch_SS_assum |> allI vgenset |> rewr_rule[cond]
        val IN_assum = mk_pred "IN" [mk_var(memn,mems),fLFP] 
        val disch_IN_assum = by_cond |> disch IN_assum
        val wrap_SS = disch_IN_assum |> allI (memn,mems) |> rewr_rule[GSYM SS_def]
    in wrap_SS
    end

assume “SS(App(isLf(X),isLs(X)),xs)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘Pow(N * X)’,‘App(isLf(X),isLs(X))’,
                                ‘App(isLf(X),xs)’]
                    |> undisch
                    |> qspecl [‘xs:mem(Pow(Pow(N * X)))’]
                    |> undisch)
       |> prove_hyp
          (isLf_monotone 
               |> qspecl [‘isLs(X)’,‘xs:mem(Pow(Pow(N * X)))’]
               |> undisch)
       |> prove_hyp
          (isLs_SS |> qspecl [‘xs:mem(Pow(Pow(N * X)))’]
                   |> undisch)
       |> disch “SS(App(isLf(X), xs), xs)”
       |> allI ("xs",mem_sort (rastt "Pow(Pow(N * X))"))
       |> rewr_rule[isLs_cond]
       |> disch “IN(a, App(isLf(X), isLs(X)))”
       |> allI ("a",mem_sort (rastt "Pow(N * X)"))
       |> rewr_rule[GSYM SS_def]



assume “SS(App(Cdf(X),Cds(X)),xs)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘Pow(X) * N’,‘App(Cdf(X),Cds(X))’,
                                ‘App(Cdf(X),xs)’]
                    |> undisch
                    |> qspecl [‘xs:mem(Pow(Pow(X) * N))’]
                    |> undisch)
       |> prove_hyp
          (Cdf_monotone 
               |> qspecl [‘Cds(X)’,‘xs:mem(Pow(Pow(X) * N))’]
               |> undisch)
       |> prove_hyp
          (Cds_SS |> qspecl [‘xs:mem(Pow(Pow(X) * N))’]
                   |> undisch)
       |> disch “SS(App(Cdf(X), xs), xs)”
       |> allI ("xs",mem_sort (rastt "Pow(Pow(X) * N)"))
       |> rewr_rule[Cds_cond]
       |> disch “IN(a, App(Cdf(X), Cds(X)))”
       |> allI ("a",mem_sort (rastt "Pow(X) * N"))
       |> rewr_rule[GSYM SS_def]

assume “SS(App(FIf(X),FIs(X)),xs)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘Pow(X)’,‘App(FIf(X),FIs(X))’,
                                ‘App(FIf(X),xs)’]
                    |> undisch
                    |> qspecl [‘xs:mem(Pow(Pow(X)))’]
                    |> undisch)
       |> prove_hyp
          (FIf_monotone 
               |> qspecl [‘FIs(X)’,‘xs:mem(Pow(Pow(X)))’]
               |> undisch)
       |> prove_hyp
          (FIs_SS |> qspecl [‘xs:mem(Pow(Pow(X)))’]
                   |> undisch)
       |> disch “SS(App(FIf(X), xs), xs)”
       |> allI ("xs",mem_sort (rastt "Pow(Pow(X))"))
       |> rewr_rule[FIs_cond]
       |> disch “IN(a, App(FIf(X), FIs(X)))”
       |> allI ("a",mem_sort (rastt "Pow(X)"))
       |> rewr_rule[GSYM SS_def]


assume “SS(App(inNf,inNs),X)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘N0’,‘App(inNf,inNs)’,
                                ‘App(inNf,X)’]
                    |> undisch
                    |> qspecl [‘X:mem(Pow(N0))’]
                    |> undisch)
       |> prove_hyp
          (inNf_monotone 
               |> qspecl [‘inNs’,‘X:mem(Pow(N0))’]
               |> undisch)
       |> prove_hyp
          (inNs_SS |> qspecl [‘X:mem(Pow(N0))’]
                   |> undisch)
       |> disch “SS(App(inNf, X), X)”
       |> allI ("X",mem_sort (rastt "Pow(N0)"))
       |> rewr_rule[inNs_cond]
       |> disch “IN(a, App(inNf, inNs))”
       |> allI ("a",mem_sort (rastt "N0"))
       |> rewr_rule[GSYM SS_def]
