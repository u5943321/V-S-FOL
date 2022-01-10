
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



val _ = new_sort "set" [];
val _ = new_sort "mem" [("A",mk_sort "set" [])];
val _ = new_sort "rel" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "rel" "->"

val set_sort = mk_sort "set" []
fun mem_sort A = mk_sort "mem" [A]
fun rel_sort A B = mk_sort "rel" [A,B]
fun mk_set A = mk_var(A,set_sort)
fun mk_rel R A B = mk_var(R,rel_sort A B)
fun mk_mem a A = mk_var(a,mem_sort A)

val _ = EqSorts := "rel" :: (!EqSorts)
val _ = EqSorts := "mem" :: (!EqSorts)

val _ = new_pred "Holds" [("R",rel_sort (mk_set "A") (mk_set "B")),
                         ("a",mem_sort (mk_set "A")),
                         ("b",mem_sort (mk_set "B"))]



fun eq_sym a = 
    if mem a (!EqSorts) then 
        let val ns0 = srt2ns a
            val v1 = mk_var ns0
            val v2 = pvariantt (HOLset.add(essps,ns0)) v1
            val v1v2 = mk_eq v1 v2
            val v2v1 = mk_eq v2 v1
            val l2r = assume v1v2 |> sym|> disch_all
            val r2l = assume v2v1 |> sym|> disch_all
        in dimpI l2r r2l
        end
    else raise ERR ("eq_sym.input sort: " ^ a ^ " does not have equality",
                    [],[],[])



val lflip_tac =
fconv_tac 
 (land_fconv no_conv 
 $ basic_once_fconv no_conv
 (first_fconv (List.map (rewr_fconv o eq_sym) (!EqSorts))))

 

val rflip_tac =
fconv_tac 
 (rand_fconv no_conv 
 $ basic_once_fconv no_conv
 (first_fconv (List.map (rewr_fconv o eq_sym) (!EqSorts))))



val flip_tac = 
fconv_tac 
 (basic_once_fconv no_conv 
  (first_fconv (List.map (rewr_fconv o eq_sym) (!EqSorts))))



val _ = new_sort "set" [];
val _ = new_sort "mem" [("A",mk_sort "set" [])];
val _ = new_sort "rel" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "rel" "->"

val set_sort = mk_sort "set" []
fun mem_sort A = mk_sort "mem" [A]
fun rel_sort A B = mk_sort "rel" [A,B]
fun mk_set A = mk_var(A,set_sort)
fun mk_rel R A B = mk_var(R,rel_sort A B)
fun mk_mem a A = mk_var(a,mem_sort A)

val _ = EqSorts := "rel" :: (!EqSorts)
val _ = EqSorts := "mem" :: (!EqSorts)

val _ = new_pred "Holds" [("R",rel_sort (mk_set "A") (mk_set "B")),
                         ("a",mem_sort (mk_set "A")),
                         ("b",mem_sort (mk_set "B"))]

val Fun_def = define_pred “!A B R:rel(A,B). isFun(R) <=> !x:mem(A). ?!y:mem(B). Holds(R,x,y)”


val Fun_expand = prove_store("Fun_expand",
e0
(rpt strip_tac >> rw[Fun_def] >>
 rw[uex_def “?!y:mem(B).Holds(R,x,y)”] >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac (* 2 *)
     >-- (first_x_assum (qspecl_then [‘a’] assume_tac) >> 
          pop_assum strip_assume_tac >> qexists_tac ‘y’ >> arw[]) 
     >-- (first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
          first_assum rev_drule >>
          first_assum (qspecl_then [‘b2’] assume_tac) >>
          first_assum drule >> arw[])) >>
 rpt strip_tac >> last_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 qexists_tac ‘b’ >> arw[] >> rpt strip_tac >> first_x_assum irule >>
 qexists_tac ‘x’ >> arw[])
(form_goal
“!A B R:A->B. isFun(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2) ==> b1 = b2)”));

val _ = new_fun "Eval" (mem_sort (mk_set "B"),[("R",rel_sort (mk_set "A") (mk_set "B")),
                        ("x",mem_sort (mk_set "A"))]) 

val Eval_def = new_ax “!A B Fn:rel(A,B). isFun(Fn) ==>!x y. Holds(Fn,x,y) <=> y = Eval(Fn,x)”

