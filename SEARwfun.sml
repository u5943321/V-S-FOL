
fun fVar_Inst_f (pair as (P,(argl:(string * sort) list,Q))) f = 
    let val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q) argl
    in
    case view_form f of
        vPred(P0,false,args0) =>
        if P0 = P
        then let val venv = match_tl essps 
                                     (List.map mk_var argl) args0
                                     emptyvd
             in inst_form (mk_menv venv emptyfvd) Q
             end 
             handle _ => f 
        else f
      | vConn(co,fl) => mk_conn co (List.map (fVar_Inst_f pair) fl)
      | vPred(_,true,_) => f
      | vQ(q,n,s,b) => 
        (case HOLset.find (fn (n0,s0) => n0 = n) lcs of
            NONE => mk_quant q n s (fVar_Inst_f pair b) 
          | SOME _ =>
            let val (n',_) = dest_var (pvariantt lcs (mk_var(n,s)))
                val f' = rename_bound n' f 
            in fVar_Inst_f pair f'
            end)
    end


fun fVar_Inst_th (pair as (P,(argl:(string * sort) list,Q))) th = 
    let val (ct,asl,w) = dest_thm th
        val asl' = List.map (fVar_Inst_f pair) asl
        val w' = fVar_Inst_f pair w
        val vs = bigunion (pair_compare String.compare sort_compare)
                          (List.map fvf (w' :: asl'))
        val newct = HOLset.union(ct,vs)
    in mk_thm (newct,asl',w')
    end


fun ind_with th (ct,asl,w) = 
    let 
        val (P,args) = dest_fvar $ concl (strip_all_and_imp th)
        val (b,bvs) = strip_forall w
        val th1 = fVar_Inst_th (P,(bvs,b)) th
    in match_mp_tac th1 (ct,asl,w)
    end
