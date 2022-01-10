
(*need to rely on the fact that the ind principle always have conclusion
!a b. pred(a,b) ==> P(a,b)

or !a:sort. P(a)

where pred is not a fvar and P is 

*)

fun ind_with_ver1 th (ct,asl,w) = 
    let 
        val (P,args) = dest_fvar $ concl (strip_all_and_imp th)
        val (b,bvs) = strip_forall w
        val th1 = fVar_Inst_th (P,(bvs,b)) th
    in match_mp_tac th1 (ct,asl,w)
    end



fun ind_with_ver2 th (ct,asl,w) = 
    let 
        val th1 = undisch th
        val (bvs,conc) = dest_forall (concl th1)
        val (ante,con) = dest_imp conc
                         handle _ => (TRUE,conc)
        val (P,args) = dest_fvar con
        val (b,qvs) = strip_forall w
        val (gante,gcon) = dest_imp b
                           handle _ => (TRUE,b)
        val th2 = fVar_Inst_th (P,(qvs,gcon)) th
    in match_mp_tac th2 (ct,asl,w)
    end

fun efn (n,s) (f,th) = 
    let 
        val ef = mk_exists n s f
    in
        (ef,existsE (n,s) (assume ef) th)
    end
fun match_mp_tac th (ct:cont,asl:form list,w) = 
    let
        val (impl,gvs) = strip_forall (concl th)
        val (hyp,conseq) = dest_imp impl
        val (con,cvs) = strip_forall (conseq)
        val th1 = (C specl) (undisch ((C specl) th (List.map mk_var gvs))) (List.map mk_var cvs) 
        val (vs,evs) = partition (fn v => HOLset.member(fvf con,v)) gvs
        val th2 = uncurry disch (itlist efn evs (hyp, th1)) 
        val (gl,vs) = strip_forall w
        val env = match_form (fvfl (ant th)) (fVarsl (ant th)) con gl mempty
        val ith = inst_thm env th2
        val gth = simple_genl (rev vs) (undisch ith)
        val hyp = fst (dest_imp (concl ith))
    in
        ([(ct,asl,hyp)], sing (mp (disch hyp gth)))
    end


fun ind_with th (ct,asl,w) = 
    let 
        val th1 = undisch th
        val (conc,bvs) = strip_forall (concl th1)
        val (ante,con) = dest_imp conc
                         handle _ => (TRUE,conc)
        val (P,args) = dest_fvar con
        val (b,qvs) = strip_forall w
        val (gante,gcon) = dest_imp b
                           handle _ => (TRUE,b)
        val th2 = fVar_Inst_th (P,(qvs,gcon)) th
    in match_mp_tac th2 (ct,asl,w)
    end


fun ind_with' th (ct,asl,w) = 
    let 
        val th1 = undisch th
        val (conc,bvs) = strip_forall (concl th1)
        val (ante,con) = dest_imp conc
                         handle _ => (TRUE,conc)
        val (P,args) = dest_fvar con
        val (b,qvs) = strip_forall w
        val (gante,gcon) = dest_imp b
                           handle _ => (TRUE,b)
        val th2 = fVar_Inst_th (P,(qvs,gcon)) th
    in irule th2 (ct,asl,w)
    end

val Sub_mono_eq = prove_store("Sub_mono_eq",
e0
(strip_tac >> ind_with' N_ind_P >> rw[Sub_O,Sub_Suc,Suc_def] >> 
 rpt strip_tac (* 2 *) >-- rw[Pre_Suc] >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!m n. Sub(Suc(m),Suc(n)) = Sub(m,n)”));


rewr_rule[Suc_def] N_ind_P

EQ_psym "P" [assume “Eval(SUC,n) = Suc(n)”]
rewr_fconv




val l = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “Sub(Suc(a),Suc(b)) = Sub(a,b)”))] 
 N_ind_P 

val (ct, asl,w) = cg $ 
e0
(strip_tac >> ind_with N_ind_P >> )
(form_goal
 “!a b. Sub(Suc(a),Suc(b)) = Sub(a,b)”);

