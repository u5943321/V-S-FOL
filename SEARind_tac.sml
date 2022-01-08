
(*need to rely on the fact that the ind principle always have conclusion
!a b. pred(a,b) ==> P(a,b)

or !a:sort. P(a)

where pred is not a fvar and P is 

*)

fun ind_with th (ct,asl,w) = 
    let 
        val (P,_) = dest_fvar $ concl (strip_all_and_imp th)
        val (b,bvs) = strip_forall w
        val th1 = fVar_Inst [(P,(bvs,b))] th
    in match_mp_tac th1 (ct,asl,w)
    end


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

