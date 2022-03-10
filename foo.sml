
fun fVar_sInst_th f f' th = 
    let val (P,args) = dest_fvar f
        val vl = List.map dest_var args
    in fVar_Inst_th (P,(vl,f')) th
    end


val _ = new_sort "fun" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "fun" "->"

fun fun_sort A B = mk_sort "fun" [A,B]
fun mk_func f A B = mk_var(f,fun_sort A B)
val _ = EqSorts := "fun" :: (!EqSorts)

val _ = new_fun "App" (mem_sort (mk_set "B"),
                       [("f",fun_sort (mk_set "A") (mk_set "B")),
                       ("a",mem_sort (mk_set "A"))]);

val rel2fun = store_ax("rel2fun",
“!A B R:A~>B. isFun(R) ==> ?!f:A->B. !a b. App(f,a) = b <=> Holds(R,a,b)”);

val rel2fun_ex = prove_store("rel2fun_ex",
e0
(rpt strip_tac >> assume_tac rel2fun >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f’ >> arw[] )
(form_goal “!A B R:A~>B. isFun(R) ==> ?f:A->B. !a b. App(f,a) = b <=> Holds(R,a,b)”));



val inNf_ex = prove_store("inNf_ex",
e0
(cheat)
(form_goal “∃f. ∀p:mem(Pow(N0)). (∀x. IN(x,App(f,p)) ⇔ 
 (x = O0 | 
           ∃n0:mem(N0). IN(n0,p) ∧ x = App(S1,n0)) )”));

val inNf_def = inNf_ex |> ex2fsym0 "inNf" []


val SS_def = define_pred “∀A P1:mem(Pow(A)) P2. SS(P1,P2) ⇔ 
 (∀a. IN(a,P1) ⇒ IN(a,P2))”

val SS_Trans = prove_store("SS_Trans",
e0
(rw[SS_def] >> rpt strip_tac >> first_x_assum irule >>
 first_x_assum irule >> arw[])
(form_goal 
 “∀A P1:mem(Pow(A)) P2. SS(P1,P2) ⇒ ∀P3. SS(P2,P3) ⇒ SS(P1,P3)”));


val inN's_def = 
    IN_def_P_ex |> allE (rastt "Pow(N0)") |> GSYM
                |> fVar_sInst_th “P(a:mem(Pow(N0)))” 
                “SS(App(inNf,a:mem(Pow(N0))), a)”
                |> ex2fsym0 "inN's" []
                |> store_as "inN's_def";

val inNs_ex = prove_store("inNs_ex",
e0
(qexists_tac ‘BIGINTER(inN's)’ >> rw[])
(form_goal “∃inNs. inNs = BIGINTER(inN's)”));

val inNs_def = inNs_ex |> ex2fsym0 "inNs" []



val inNf_monotone = prove_store("inNf_monotone",
e0
(rw[inNf_def,SS_def] >> rpt strip_tac (* 2 *)
 >-- arw[] >> disj2_tac >> qexists_tac ‘n0’ >> arw[] >>
 first_x_assum irule >> arw[])
(form_goal “∀s1 s2. SS(s1,s2) ⇒ SS(App(inNf,s1), App(inNf,s2))”));

val inN_rule0 = prove_store("inN_rule0",
e0
(rw[SS_def] >> rpt strip_tac >>
 rw[inNs_def] >> rw[IN_BIGINTER] >>
 rpt strip_tac >> 
 qby_tac ‘SS(inNs,ss)’
 >-- (rw[SS_def,inNs_def] >> rw[IN_BIGINTER] >> 
      rpt strip_tac >> first_x_assum irule >> arw[]) >>
 fs[inN's_def] >>
 drule inNf_monotone >>
 qby_tac ‘SS(App(inNf, inNs),ss)’
 >-- (irule SS_Trans >> qexists_tac ‘App(inNf, ss)’ >>
     arw[]) >>
 pop_assum (assume_tac o (rewr_rule [SS_def])) >>
 first_x_assum irule >> arw[])
(form_goal “SS(App(inNf,inNs),inNs)”));

val inN_ind0 = prove_store("inN_ind0",
e0
(rpt strip_tac >>
 rw[inNs_def] >> rw[SS_def] >> rw[IN_BIGINTER] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘p’] assume_tac) >>
 rfs[inN's_def])
(form_goal
 “!p:mem(Pow(N0)). SS(App(inNf,p),p) ==> SS(inNs,p)”));

val SS_SS_eq = prove_store("SS_SS_eq",
e0
(rpt strip_tac >> irule IN_EXT >> fs[SS_def] >> 
 strip_tac >> dimp_tac >> strip_tac >> 
 first_x_assum irule >> arw[])
(form_goal “∀A p1:mem(Pow(A)) p2. SS(p1,p2) ∧ SS(p2,p1) ⇒
 p1 = p2”));

val inN_cases0 = prove_store("inN_cases0",
e0
(irule SS_SS_eq >> rw[inN_rule0] >> 
 rw[SS_def] >> strip_tac >> rw[inNs_def] >>
 rw[IN_BIGINTER] >> strip_tac >>
 first_x_assum 
 (qspecl_then [‘App(inNf, BIGINTER(inN's))’] assume_tac) >>
 first_x_assum irule >> 
 assume_tac inN_rule0 >> rw[inN's_def] >>
 rw[GSYM inNs_def] >>
 irule inNf_monotone >> first_x_assum accept_tac)
(form_goal
 “App(inNf,inNs) = inNs”));
