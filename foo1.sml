
val SS_def = define_pred “∀A P1:mem(Pow(A)) P2. SS(P1,P2) ⇔ 
 (∀a. IN(a,P1) ⇒ IN(a,P2))”

val SS_Trans = prove_store("SS_Trans",
e0
(rw[SS_def] >> rpt strip_tac >> first_x_assum irule >>
 first_x_assum irule >> arw[])
(form_goal 
 “∀A P1:mem(Pow(A)) P2. SS(P1,P2) ⇒ ∀P3. SS(P2,P3) ⇒ SS(P1,P3)”));

val SS_SS_eq = prove_store("SS_SS_eq",
e0
(rpt strip_tac >> irule IN_EXT >> fs[SS_def] >> 
 strip_tac >> dimp_tac >> strip_tac >> 
 first_x_assum irule >> arw[])
(form_goal “∀A p1:mem(Pow(A)) p2. SS(p1,p2) ∧ SS(p2,p1) ⇒
 p1 = p2”));

fun fVar_sInst_th f f' th = 
    let val (P,args) = dest_fvar f
        val vl = List.map dest_var args
    in fVar_Inst_th (P,(vl,f')) th
    end



val IN_def_P_ex = prove_store("IN_def_P_ex",
e0
(strip_tac >>
 qspecl_then [‘A’] strip_assume_tac IN_def_P_expand >>
 qexists_tac ‘s’ >> first_x_assum accept_tac)
(form_goal “!A. ?s:mem(Pow(A)). (!a. P(a) <=> IN(a,s))”));


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



val S1_def = rel2fun_ex |> qspecl [‘N0’,‘N0’,‘S0’]
                        |> C mp S0_Fun
                        |> ex2fsym0 "S1" []
                        |> store_as "S1_def";

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


val Cdf_ex = prove_store("Cdf_ex",
e0
(cheat)
(form_goal
 “∃f. ∀p:mem(Pow(Pow(X) * N)). (∀xsn. IN(xsn,App(f,p)) ⇔ 
 (xsn = Pair(Empty(X),O) | 
  ∃xsn0 x. IN(xsn0,p) ∧ xsn = Pair(Ins(x,Fst(xsn0)),Suc(Snd(xsn0)))) )”));

val Cdf_def = Cdf_ex |> ex2fsym0 "Cdf" ["X"]


val isLf_ex = prove_store("isLf_ex",
e0
(cheat)
(form_goal
 “∃f. ∀p:mem(Pow(Pow(N * X))). (∀ls. IN(ls,App(f,p)) ⇔ 
 (ls = Empty(N * X) | 
  ∃ls0 x. IN(ls0,p) ∧ ls = Ins(Pair(CARD(ls0),x),ls0)))”));

val isLf_def = isLf_ex |> ex2fsym0 "isLf" ["X"]


fun mk_App fnterm arg = mk_fun "App" [fnterm,arg];


fun conj_monotone ip1 ip2 = 
    let val A2A' = concl ip1
        val B2B' = concl ip2
        val (A,A') = dest_imp A2A'
        val (B,B') = dest_imp B2B'
        val AnB = mk_conj A B
        val A'nB' = mk_conj A' B'
        val AnB2A' = assume AnB |> conjE1 |> mp ip1
        val AnB2B' = assume AnB |> conjE2 |> mp ip2
    in conjI AnB2A' AnB2B' |> disch AnB
    end


fun disj_monotone ip1 ip2 = 
    let val A2A' = concl ip1
        val B2B' = concl ip2
        val (A,A') = dest_imp A2A'
        val (B,B') = dest_imp B2B'
        val AuB = mk_disj A B
        val A'uB' = mk_disj A' B'
        val A2A'uB' = assume A |> mp ip1 |> disjI1 B'
        val B2A'uB' = assume B |> mp ip2 |> disjI2 A'
    in disjE (assume AuB) A2A'uB' B2A'uB' |> disch AuB
    end

fun forall_monotone allip = 
    let val ((n,s),ip) = allip |> concl |> dest_forall
        val (ante,conseq) = dest_imp ip
        val allante = mk_forall n s ante
        val allconseq = mk_forall n s conseq 
        val v0 = mk_var(n,s)
    in allante |> assume |> allE v0 |> mp (allE v0 allip) |> allI (n,s)
               |> disch allante 
    end


fun exists_monotone allip = 
    let val ((n,s),ip) = allip |> concl |> dest_forall
        val (ante,conseq) = dest_imp ip
        val exante = mk_exists n s ante
        val exconseq = mk_exists n s conseq 
        val v0 = mk_var(n,s)
    in ante |> assume |> mp (allE v0 allip) |> existsI (n,s) v0 conseq
            |> existsE (n,s) (assume exante)
            |> disch exante
    end


fun trivial_imp f = iffLR $ frefl f 


fun imp_induce ip fm = 
    let val ((n,s),b) = dest_forall (concl ip)
        val v0 = mk_var (n,s)
        val ip1 = allE v0 ip
        val (ante0,conseq0) = dest_imp (concl ip1)
        val (ante,conseq) = dest_imp fm
    in (*assume ante and conseq same pattern*)
        if eq_form(ante,conseq) then trivial_imp ante else 
        if can (match_form essps (HOLset.empty String.compare) ante ante0) mempty
        then let val env = match_form essps 
                           (HOLset.empty String.compare) ante0 ante mempty
                 val ip1' = inst_thm env ip1 
                 val (ante',conseq') = dest_imp (concl ip1')
             in if eq_form(ante,ante') andalso eq_form(conseq,conseq') 
                then ip1' else 
                raise simple_fail "imp_induce"
             end
        else
        case (view_form ante,view_form conseq) of 
            (vConn("&",[a1,a2]),vConn("&",[c1,c2])) => 
            let val ip1 = imp_induce ip (mk_imp a1 c1)
                val ip2 = imp_induce ip (mk_imp a2 c2)
            in conj_monotone ip1 ip2
            end 
          | (vConn("|",[a1,a2]),vConn("|",[c1,c2])) => 
            let val ip1 = imp_induce ip (mk_imp a1 c1)
                val ip2 = imp_induce ip (mk_imp a2 c2)
            in disj_monotone ip1 ip2
            end 
          (*assume the two sides has the same bound name to work!*)
          | (vQ("!",n1,s1,b1),vQ("!",n2,s2,b2)) => 
            let val ip0 = imp_induce ip (mk_imp b1 b2)
            in forall_monotone (allI (n1,s1) ip0)
            end
          | (vQ("?",n1,s1,b1),vQ("?",n2,s2,b2)) => 
            let val ip0 = imp_induce ip (mk_imp b1 b2)
            in exists_monotone (allI (n1,s1) ip0)
            end
    end


(*maybe have something like dest_IN which dests a particular pred*)
fun mk_monotone fdef = 
    let val (pvar as (pname,psort),b) = fdef |> concl |> dest_forall
        val (mvar as (mname,msort),b1) = b |> dest_forall
        val (b1l,b1r) = dest_dimp b1 
        val fnterm = b1l |> dest_pred |> #2 |> el 2 |> dest_fun |> #3 |> hd
        val avoids = cont fdef
        val gens1 = pvariantt avoids (mk_var("s1",psort))
        val gens2 = pvariantt avoids (mk_var("s2",psort))
        val goalant = mk_pred "SS" [gens1,gens2] 
        val goalconsq = mk_pred "SS" [mk_App fnterm gens1,mk_App fnterm gens2]
        val goalant_ipth = goalant |> basic_fconv no_conv 
                                   (rewr_fconv (spec_all SS_def))
                                   |> iffLR |> undisch
        val goalconsq' = goalconsq |> basic_fconv no_conv 
                                      (first_fconv [rewr_fconv(spec_all SS_def),
                                                 rewr_fconv (spec_all fdef)])
        val (var0,toinduce)= goalconsq' |> concl |> #2 o dest_dimp |> dest_forall
        val imp_induce_th = imp_induce goalant_ipth toinduce
        val th1 = imp_induce_th |> allI var0 |> dimp_mp_r2l goalconsq'
                                |> disch goalant 
                                |> allI (dest_var gens2)
                                |> allI (dest_var gens1)
    in th1
    end


fun mk_prim fdef = 
    let val ((pname,psort),b) = fdef |> concl |> dest_forall
        val ((mname,msort),b1) = b |> dest_forall
        val pisin = psort|> dest_sort |> #2 |> hd
        val pvar = mk_var (pname,psort)
        val fvar0 = mk_fvar "P" [mk_var (pname,psort)]
        val (lb1,rb1) = b1 |> dest_dimp
        val fnterm = lb1 |> dest_pred |> #2 |> el 2 |> dest_fun |> #3 |> hd
        val fvar1 = mk_pred "SS" [mk_App fnterm pvar,pvar]
        val defname = fnterm |> dest_fun |> #1 |> explode |> rev |> tl 
                             |> rev |> implode
        val spec_IN_ex = IN_def_P_ex |> allE pisin |> GSYM
                                     |> fVar_sInst_th fvar0 fvar1
        val skinputs = cont spec_IN_ex |> HOLset.listItems
        val sk = spec_IN_ex |> ex2fsym0 (defname ^ "'s") (List.map #1 skinputs)
    in sk
    end



fun mk_LFP primtm = 
    let val bigintertm = mk_fun "BIGINTER" [primtm]
        val defname = primtm |> dest_fun |> #1 |> explode |> rev |> tl |> tl
                             |> rev |> implode
        val st = sort_of bigintertm
        val LFPname = defname^"s"
        val templ = mk_eq (mk_var(defname^"s",st)) bigintertm
        val exth = bigintertm |> refl 
                              |> existsI (defname^"s",st) bigintertm templ
        val skinputs = cont exth |> HOLset.listItems
        val LFP_def = exth |> ex2fsym0 LFPname (List.map #1 skinputs)
    in LFP_def
    end


fun mk_cond LFPdef primdef = 
   let val avoids = HOLset.union(cont LFPdef,cont primdef)
       val (LFP,bi) = LFPdef |> concl |> dest_eq
       val pofset = bi |> sort_of
                      |> #2 o dest_sort |> hd |> #3 o dest_fun |> hd
       val memvar = pvariantt avoids (mk_var ("a",mem_sort pofset))
       val startwith = mk_pred "IN" [memvar,LFP]
       val by_LFP = startwith |> basic_fconv (rewr_conv LFPdef)
                              (rewr_fconv (spec_all IN_BIGINTER))
       val by_primdef = by_LFP |> rewr_rule[primdef] |> GSYM
       val gened = by_primdef |> allI (dest_var memvar)
   in gened
   end



fun mk_SS LFPdef primdef = 
    let val ((pname,psort),b) = primdef |> concl |> dest_forall
        val s0 = psort |> dest_sort |> #2 |> hd |> dest_fun |> #3 |> hd
        val (pl,pr) = b |> dest_dimp
        val (LFP,bi) = LFPdef |> concl |> dest_eq
        val pvar = mk_var (pname,psort)
        val goal_conc = mk_pred "SS" [LFP,pvar]
        val goal_ant = pr
        val SS_bi = mk_pred "SS" [bi,pvar]
        val by_LFP = goal_conc |> basic_fconv (rewr_conv LFPdef) no_fconv
        val expand_SS = iff_trans by_LFP 
                                  (SS_bi |> basic_fconv 
                                   no_conv (rewr_fconv (spec_all SS_def))) 
        val by_prim = expand_SS |> rewr_rule[IN_BIGINTER,primdef]
                                |> iffRL |> undisch
        val avoids = HOLset.union(cont LFPdef,cont primdef)
        val genvar = pvariantt avoids (mk_var("a0",mem_sort s0))
        val lemmaf0 = mk_imp goal_ant (mk_pred "IN" [genvar,pvar]) 
        val lemmaf = mk_forall pname psort lemmaf0
        val lemma = lemmaf |> assume |> specl [pvar] 
                           |> C mp (assume goal_ant)
                           |> disch lemmaf
                           |> allI (dest_var genvar)
        val provedhyp = by_prim |> prove_hyp lemma
        val disch_gen = provedhyp |> disch goal_ant |> allI (pname,psort)
    in
        disch_gen
    end


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


fun mk_cases monotone rules0 cond = 
    let val fLFP = rules0 |> concl |> #2 o dest_pred |> hd
        val [fnterm,LFP] = fLFP |> #3 o dest_fun
                           handle _ => raise 
                                    simple_fail "mk_cases.cannot identify LFP"
        val ((mname,msort),b) = cond |> concl |> dest_forall
        val misin = msort |> dest_sort |> #2 |> hd
        val (lb,rb) = b |> dest_dimp
        val ((sname,ssort),lb0) = lb |> dest_forall
        val toasm_conseq = mk_pred "IN" [mk_var (mname,msort),fLFP]
        val toasm_ant = mk_pred "SS" [mk_App fnterm fLFP,fLFP]
        val orig = assume (mk_imp toasm_ant toasm_conseq)
        val mp_ant = orig |> C mp (assume toasm_ant)
        val spec_monotone = monotone |> specl [fLFP,LFP] |> undisch
        val by_monotone = mp_ant |> prove_hyp spec_monotone
        val by_rules0 = by_monotone |> prove_hyp rules0
        val spec_asm_lb = lb |> assume |> specl [fLFP] 
        val by_above = by_rules0 |> prove_hyp spec_asm_lb
        val spec_cond = cond |> iffRL |> allE (mk_var (mname,msort)) |> undisch
        val by_cond = by_above |> prove_hyp spec_cond |> disch rb
                               |> allI (mname,msort)
        val by_SS_def = by_cond |> rewr_rule[GSYM SS_def]
        val conj = by_SS_def |> conjI rules0
        val spec_SS_eq = SS_SS_eq |> specl [misin,fLFP,LFP]
        val mp_above = conj |> mp spec_SS_eq
    in mp_above
    end

fun mk_ind cond = 
    let val ((memn,mems),b) = cond |> concl |> dest_forall
        val toassume0 = b |> #1 o dest_dimp
        val ((sname,ssort),toassume) = dest_forall toassume0
        val tomp = toassume |> #1 o dest_imp
        val orig = assume toassume
        val mp_tomp = orig |> C mp (assume tomp)
        val spec_toassume0 = toassume0 |> assume |> specl [mk_var (sname,ssort)]
        val by_spec_above = mp_tomp |> prove_hyp spec_toassume0
                                    |> disch toassume0
                                    |> allI (memn,mems)
        val by_cond = by_spec_above |> rewr_rule[cond]
        val by_SS_def = by_cond |> rewr_rule[GSYM SS_def]
        val disch_tomp = by_SS_def |> disch tomp
        val gened = disch_tomp |> allI (sname,ssort)
    in gened
    end
