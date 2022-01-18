structure conv :> conv = 
struct
open term form logic drule abbrev

exception unchanged of string * term list * form list

fun part_tmatch partfn th t = 
    let 
        val env = mk_menv (match_term (fvfl (ant th)) (partfn th) t emptyvd) emptyfvd
    in 
        inst_thm env th
    end

val rewr_conv = part_tmatch (fst o dest_eq o concl)



(*operations on conv*)

fun all_conv t = refl t

infix thenc

fun thenc (c1,c2) t = 
    let 
        val th1 = c1 t 
    in 
        trans th1 (c2 (snd (dest_eq (concl th1))))
    end

infix orelsec

fun orelsec (c1,c2) t = 
    c1 t handle _ => c2 t

fun try_conv c = c orelsec all_conv

fun repeatc c t =
    ((c thenc (repeatc c)) orelsec all_conv) t

fun no_conv f = raise simple_fail "no_conv" 

fun first_conv cl:conv = 
    case cl of [] => no_conv
             | h :: t => h orelsec (first_conv t)

(*conv on subterms*)


fun arg_conv c t = 
    case (view_term t) of 
        vFun (f,s,l) => EQ_fsym f (List.map c l)
      | _ => raise ERR ("arg_conv.not a function term",[],[t],[])


fun land_conv c t = 
    case (view_term t) of 
        vFun (f,s,[t1,t2]) => EQ_fsym f [c t1,refl t2]
      | _ => raise ERR ("land_conv.not a function term",[],[t],[])


fun rand_conv c t = 
    case (view_term t) of 
        vFun (f,s,[t1,t2]) => EQ_fsym f [refl t1,c t2]
      | _ => raise ERR ("land_conv.not a function term",[],[t],[])


fun depth_conv c t = 
    ((try_conv (arg_conv (depth_conv c))) thenc (repeatc c)) t

fun redepth_conv c t =
    (try_conv (arg_conv (redepth_conv c)) thenc
              ((c thenc (redepth_conv c)) orelsec all_conv))
        t

fun changed_conv (c:term -> thm) t = 
    if eq_thm (c t) (refl t) then raise unchanged ("changed_conv",[t],[])
    else c t


fun top_depth_conv conv tm =
   (repeatc conv thenc
    try_conv (changed_conv (arg_conv (top_depth_conv conv)) thenc
              try_conv (conv thenc top_depth_conv conv))) tm


 

(*fconvs*)

val simp_trace = ref false




fun part_fmatch partfn th f = 
    let 
        val fvd = match_form (fvfl (ant th)) (fVarsl (ant th)) (partfn th) f mempty
    in 
        inst_thm fvd th
    end


 
fun rewr_fconv th = part_fmatch (fst o dest_dimp o concl) th
    (*if is_dimp (concl th) then part_fmatch (fst o dest_dimp o concl) th
    else
        raise
            ERR ("rewr_fconv.conclusion of the input theorem is not an iff",
                 [],[],[concl th]) *)


(*TODO: let rewr_fconv check the imput thm is an iff, so it raises err before the conv is applied*)
(*operation on fconvs*)

infix thenfc

fun thenfc (fc1:fconv,fc2:fconv) f = 
    let 
        val th1 = fc1 f 
    in 
        iff_trans th1 (fc2 (snd (dest_dimp (concl th1))))
    end


fun all_fconv f = frefl f

infix orelsefc;

fun orelsefc (fc1,fc2) f = fc1 f handle _ => fc2 f

fun no_fconv f = raise simple_fail "no_fconv"

fun first_fconv fcl:fconv = 
    case fcl of [] => no_fconv
             | h :: t => h orelsefc (first_fconv t)

fun try_fconv fc = fc orelsefc all_fconv

fun changed_fconv (fc:form -> thm) f = 
    if eq_thm (fc f) (frefl f) then raise unchanged ("changed_fconv",[],[f])
    else fc f

fun repeatfc fc f = 
    ((fc thenfc (repeatfc fc)) orelsefc all_fconv) f

fun pred_fconv c f = 
    case view_form f of 
        vPred (P,_,tl) => EQ_psym P (List.map c tl)
      | _ => raise ERR ("pred_fconv.not a predicate",[],[],[f])

(*conv on subformulas*)

fun disj_fconv fc f = 
    case view_form f of 
        vConn("|",[p,q]) => disj_iff (fc p) (fc q)
      | _ => raise ERR ("disj_fconv.not a disjunction",[],[],[f])

fun ldisj_fconv fc f = 
    case view_form f of 
        vConn("|",[p,q]) => disj_iff (fc p) (frefl q)
      | _ => raise ERR ("ldisj_fconv.not a disjunction",[],[],[f])


fun rdisj_fconv fc f = 
    case view_form f of 
        vConn("|",[p,q]) => disj_iff (frefl p) (fc q)
      | _ => raise ERR ("rdisj_fconv.not a disjunction",[],[],[f])

fun conj_fconv fc f = 
    case view_form f of 
        vConn("&",[p,q]) => conj_iff (fc p) (fc q)
      | _ => raise ERR ("conj_fconv.not a conjunction",[],[],[f])


fun lconj_fconv fc f = 
    case view_form f of 
        vConn("&",[p,q]) => conj_iff (fc p) (frefl q)
      | _ => raise ERR ("lconj_fconv.not a conjunction",[],[],[f])


fun rconj_fconv fc f = 
    case view_form f of 
        vConn("&",[p,q]) => conj_iff (frefl p) (fc q)
      | _ => raise ERR ("rconj_fconv.not a conjunction",[],[],[f])


fun neg_fconv fc f = 
    case view_form f of 
        vConn("~",[f0]) => neg_iff (fc f0)
      | _ => raise ERR ("neg_fconv.not a negation",[],[],[f])


fun imp_fconv fc f = 
    case view_form f of
        vConn("==>",[p,q]) => imp_iff (fc p) (fc q)       
      | _ => raise ERR ("imp_fconv.not an implication",[],[],[f])


fun limp_fconv fc f = 
    case view_form f of
        vConn("==>",[p,q]) => imp_iff (fc p) (frefl q)       
      | _ => raise ERR ("limp_fconv.not an implication",[],[],[f])


fun rimp_fconv fc f = 
    case view_form f of
        vConn("==>",[p,q]) => imp_iff (frefl p) (fc q)       
      | _ => raise ERR ("rimp_fconv.not an implication",[],[],[f])


fun dimp_fconv fc f = 
    case view_form f of
        vConn("<=>",[p,q]) => dimp_iff (fc p) (fc q)
      | _ => raise ERR ("dimp_fconv.not an iff",[],[],[f])


fun ldimp_fconv fc f = 
    case view_form f of
        vConn("<=>",[p,q]) => dimp_iff (fc p) (frefl q)
      | _ => raise ERR ("ldimp_fconv.not an iff",[],[],[f])


fun rdimp_fconv fc f = 
    case view_form f of
        vConn("<=>",[p,q]) => dimp_iff (frefl p) (fc q)
      | _ => raise ERR ("rdimp_fconv.not an iff",[],[],[f])





fun forall_fconv fc f = 
    case view_form f of
        (vQ("!",n,s,b)) => 
        forall_iff (n,s) $ fc (subst_bound (mk_var(n,s)) b)
      | _ => raise ERR ("forall_fconv.not an all",[],[],[f])

fun exists_fconv fc f = 
    case view_form f of
        (vQ("?",n,s,b)) => 
         exists_iff (n,s) $ fc (subst_bound (mk_var(n,s)) b)
      | _ => raise ERR ("exists_fconv.not an all",[],[],[f])
 
fun exists_fconv fc f = 
    case view_form f of
        (vQ("?",n,s,b)) => 
        let val th0 = fc (subst_bound (mk_var(n,s)) b)
        in exists_iff (n,s) th0
           handle _ =>
                  let val (n',_) = dest_var 
                                  (pvariantt (cont th0) 
                                             (mk_var(n,s))) 
                      val f' = rename_bound n' f 
                      val ((n',s'),b') = dest_exists f'
                      val th1 = fc (subst_bound (mk_var(n',s')) b')
                  in
                      exists_iff (n',s') th1
                  end
        end
      | _ => raise ERR ("exists_fconv.not an all",[],[],[f])

fun uex_fconv fc f = 
    case view_form f of
        (vQ("?!",n,s,b)) => 
        uex_iff (n,s) $ fc (subst_bound (mk_var(n,s)) b)
      | _ => raise ERR ("uex_fconv.not an all",[],[],[f])


(*
val refl_fconv = 
    let val srts = List.map fst $ Binarymap.listItems (!SortDB)
        val refls = mapfilter (eqT_intro o refl o mk_var o srt2ns) srts
    in
        first_fconv (List.map rewr_fconv refls)
    end 
*)

fun refl_fconv eqsorts = 
    let
        val refls = mapfilter (eqT_intro o refl o mk_var o srt2ns) eqsorts 
    in
        first_fconv (List.map rewr_fconv refls)
    end 

fun sub_fconv c fc = 
    try_fconv (first_fconv [conj_fconv fc,
                 disj_fconv fc,
                 imp_fconv fc,
                 dimp_fconv fc,
                 neg_fconv fc,
                 forall_fconv fc,
                 exists_fconv fc,
                 uex_fconv fc,
                 pred_fconv c])

(*TODO: uex_fconv*)



fun depth_fconv c fc f =
    (sub_fconv c (depth_fconv c fc) thenfc
               (repeatfc fc))
        f

fun redepth_fconv c fc f =
    (sub_fconv c (redepth_fconv c fc) thenfc
              ((fc thenfc (redepth_fconv c fc)) orelsefc all_fconv))
        f

val taut_conj_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_conj_1,T_conj_2,F_conj_1,F_conj_2])

val taut_disj_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_disj_1,T_disj_2,F_disj_1,F_disj_2])

val f2f = disch (mk_fvar "f0" []) (assume (mk_fvar "f0" []))
val f2f_T  = eqT_intro f2f

val taut_imp_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_imp_1,T_imp_2,F_imp_1,F_imp_2,f2f_T])

val taut_dimp_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_dimp_1,T_dimp_2,F_dimp_1,F_dimp_2,eqT_intro (frefl (mk_fvar "f0" []))])

fun forall_T sname = 
    let val (n,s) = srt2ns sname
        val var = mk_var (n,s)
        val lform = mk_forall n s TRUE
        val l2r = trueI [lform] |> disch lform
        val r2l = add_cont (fvt var) $ trueI []
                           |> allI (n,s) |> add_assum TRUE
                           |> disch TRUE
    in dimpI l2r r2l
    end



fun taut_forall_fconv sortnames = 
    let val thms = List.map forall_T sortnames
    in first_fconv (List.map rewr_fconv thms)
    end

(*


fun refl_fconv eqsorts = 
    let
        val refls = mapfilter (eqT_intro o refl o mk_var o srt2ns) eqsorts 
    in
        first_fconv (List.map rewr_fconv refls)
    end 


val taut_forall_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [forall_true_ar,forall_true_ob,
                   forall_false_ar,forall_false_ob])



val taut_exists_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [(*exists_true_ar,*)exists_true_ob,
                   exists_false_ar,exists_false_ob])
*)

val basic_taut_fconv = 
    first_fconv [taut_conj_fconv,
                 taut_disj_fconv,
                 taut_imp_fconv,
                 taut_dimp_fconv]

val nFT_fconv = first_fconv [rewr_fconv nF2T,rewr_fconv nT2F]

val taut_fconv = basic_taut_fconv (*orelsec (refl_fconv (!EqSorts))*) orelsec nFT_fconv

fun top_depth_fconv c fc f =
   (repeatfc fc thenfc
    try_fconv (changed_fconv (sub_fconv c (top_depth_fconv c fc)) thenfc
              try_fconv (fc thenfc top_depth_fconv c fc))) f

                                                           

fun once_depth_conv conv tm =
   try_conv (conv orelsec (arg_conv (once_depth_conv conv))) tm

fun once_depth_fconv c fc f =
   try_fconv (fc orelsefc (sub_fconv c (once_depth_fconv c fc))) f

fun basic_once_fconv c fc = 
    once_depth_fconv (once_depth_conv c) 
                     (fc orelsefc taut_fconv orelsefc (refl_fconv (!EqSorts)) orelsefc (taut_forall_fconv $ List.map fst $ listof_sorts (!SortDB)))



fun conv_rule c th = dimp_mp_l2r th (c (concl th)) 




fun right_imp_forall_fconv f  = 
    let
        val (ant,conc) = dest_imp f
        val (ns,b) = dest_forall conc
        val asm1 = assume f 
        val ath = assume ant 
        val mpth = mp asm1 ath
        val sth = specl [mk_var ns] mpth
        val gth = sth |> disch ant |> allI ns 
        val asm2 = assume (concl gth)
        val sasm2 = (C allE) asm2 (mk_var ns) 
        val mpsasm = mp sasm2 ath
        val gmpasm = allI ns mpsasm
        val dth' = disch ant gmpasm
    in dimpI (disch f gth)  (disch (concl gth) dth')
    end


fun sym_fconv f = 
    case view_form f of 
    vPred("=",true,[t1,t2]) => dimpI (assume f|> sym |> disch_all) (assume (mk_eq t2 t1) |> sym |> disch_all)
  | vConn("<=>", [f1,f2]) => dimpI (assume f|> iff_swap |> disch_all) (assume (mk_dimp f2 f1)|> iff_swap |> disch_all)
  | _ => raise simple_fail "not an iff or equality"


val GSYM = conv_rule (once_depth_fconv no_conv sym_fconv)

fun double_neg_fconv f = rewr_fconv double_neg_elim f


fun basic_fconv c fc =
    top_depth_fconv (top_depth_conv c) 
                    (fc orelsefc taut_fconv orelsefc (refl_fconv (!EqSorts)) orelsefc double_neg_fconv orelsefc
(taut_forall_fconv $ List.map fst $ listof_sorts (!SortDB)))

val neg_neg_elim = conv_rule (once_depth_fconv no_conv double_neg_fconv)


fun lpred_fconv c f = 
    case view_form f of 
        vPred (P,true,[t1,t2]) => EQ_psym P [c t1,refl t2]
      | _ => raise ERR ("lpred_fconv.not a predicate",[],[],[f])


fun rpred_fconv c f = 
    case view_form f of 
        vPred (P,true,[t1,t2]) => EQ_psym P [refl t1,c t2]
      | _ => raise ERR ("rpred_fconv.not a predicate",[],[],[f])

fun land_fconv c fc f = 
    case view_form f of 
        vConn(co,[f1,f2]) =>
        if co = "&" then lconj_fconv fc f else
        if co = "|" then ldisj_fconv fc f else
        if co = "==>" then limp_fconv fc f else
        if co = "<=>" then ldimp_fconv fc f else
        raise simple_fail ("not a connective: " ^ co)
      | vPred (p,true,[t1,t2]) => lpred_fconv c f
      | _ => all_fconv f


fun rand_fconv c fc f = 
    case view_form f of 
        vConn(co,[f1,f2]) =>
        if co = "&" then rconj_fconv fc f else
        if co = "|" then rdisj_fconv fc f else
        if co = "==>" then rimp_fconv fc f else
        if co = "<=>" then rdimp_fconv fc f else
        raise simple_fail ("not a connective: " ^ co)
      | vPred (p,true,[t1,t2]) => rpred_fconv c f
      | _ => all_fconv f


val IMP_IFF_DISTR = 
    let val p = mk_fvar "p" []
        val q = mk_fvar "q" []
        val q' = mk_fvar "q'" []
    in 
        mk_thm(essps,[],mk_dimp (mk_imp p (mk_dimp q q')) (mk_dimp (mk_imp p q) (mk_imp p q')))
    end

fun IMP_ANT_FCONV f = 
    case view_form f of
        vConn("==>",[a0,c0]) => 
        let val th0 = assume a0
            val rw_result1 = top_depth_fconv (rewr_conv th0) (rewr_fconv th0) c0
            val th1 = disch a0 rw_result1
            val th2 = rewr_fconv IMP_IFF_DISTR (concl th1)
        in mp (dimpl2r th2) th1
        end
      | _ => raise ERR ("IMP_ANT_FCONV.not an implication",[],[],[f])

(*

e.g.   (f = g o h) ⇒ f = j

  input:  “p ⇒ q”

  assume p, means to use theorem

  let val pth = p ⊢ p..    (* f = g o h ⊢ f = g o h *)

    REWRITE_fCONV [pth] q

    output is:  p ⊢ q ⇔ q'    (* f = g o h ⊢ f = j ⇔ g o h = j *)

    by using DISCH to get ⊢ (p ⇒ (q = q'))


    and then MP with

       (p ⇒ (q ⇔ q')) ⇒ ((p ⇒ q) ⇔ (p ⇒ q'))

    to get:

        ⊢ (p ⇒ q) ⇔ (p ⇒ q')
*)


fun conj_fconv fc f = 
    case view_form f of 
        vConn("&",[p,q]) => conj_iff (fc p) (fc q)
      | _ => raise ERR ("conj_fconv.not a conjunction",[],[],[f])

val ASSUME_CONJUNCT_LEMMA = 
    let val P1 = mk_fvar "P1" []
        val P2 = mk_fvar "P2" []
        val Q1 = mk_fvar "Q1" []
        val Q2 = mk_fvar "Q2" []
        val f0 = mk_imp (mk_conj (mk_imp P1 (mk_dimp Q1 Q2)) 
                                 (mk_imp Q2 (mk_dimp P1 P2)))
                        (mk_dimp (mk_conj P1 Q1) (mk_conj P2 Q2))
    in
        mk_thm (essps,[],f0)
    end

(*
fun part_fmatch partfn th f = 
    let 
        val fvd = match_form (fvfl (ant th)) (HOLset.empty String.compare) (partfn th) f mempty
    in 
        inst_thm fvd th
    end

*)


fun ASSUME_CONJUNCT_RULE th1 th2 = 
    let val th = conjI th1 th2
       (* val th' = rewr_fconv ASSUME_CONJUNCT_LEMMA (concl th)*)
    in
        mp (part_fmatch (fst o dest_imp o concl) ASSUME_CONJUNCT_LEMMA (concl th)) th
    end

fun ASSUME_CONJUNCT_FCONV f = 
    case view_form f of 
    vConn("&",[p,q]) => 
    let val thp = assume p 
        val qiffq' = basic_fconv (rewr_conv thp) (rewr_fconv thp) q
        val q' = (snd o dest_dimp $ concl qiffq')
        val thq' = assume q'
        val piffp' = basic_fconv (rewr_conv thq') (rewr_fconv thq') p
        val th1 = disch p qiffq'
        val th2 = disch q' piffp'
    in 
        ASSUME_CONJUNCT_RULE th1 th2
    end
  | _ => raise ERR ("ASSUME_CONJUNCT_FCONV.not a conjunction",[],[],[f])



fun conj_pair th =
    (conjE1 th,conjE2 th)
    handle ERR _ => 
      raise ERR ("conj_pair.not a conjunction",[],[],[concl th])
 


fun rv_subset_lv th = 
    let val th0 = spec_all th 
        val (l,r) = dest_dimp (concl th)
        val (lv,rv) = (fvf l,fvf r)
    in HOLset.isSubset (lv,rv)
    end 


fun rw_fcanon th = 
    let val th = spec_all th
        val f = concl th
    in 
        if is_dimp f then [th] else
        if is_conj f then (op@ o (rw_fcanon ## rw_fcanon) o conj_pair) th else
        if is_neg f then [eqF_intro th]  else
        [eqT_intro th]
    end 


fun rw_tcanon th = 
    let val th = spec_all th
        val f = concl th
    in 
        if is_eq f then [th] else
        if is_conj f then (op@ o (rw_tcanon ## rw_tcanon) o conj_pair) th else
        []
    end 



fun EXISTS_EQN_FCONV f = 
    case view_form f of
        vQ("?",n,s,b) => 
        let val (eqn, pred) = dest_conj b
            val (x,y) = dest_eq eqn
            val eqnth = assume eqn
            val predth = assume pred
            val p2p' = basic_fconv 
                           (rewr_conv eqnth) no_fconv pred
            val th1 = dimpl2r p2p' |> undisch 
            val cjed_th1 = conj_assum eqn pred th1
            val l2r = existsE (n,s) (assume f) cjed_th1 |> disch f
            val p' = snd o dest_dimp o concl $ p2p'
            val p'th = assume p'
            val th2 = conjI (refl y) p'th
            val th3 = existsI (n,s) y b th2
            val r2l = disch p' th3
        in dimpI l2r r2l
        end
      | _ => raise ERR ("EXISTS_EQN_FCONV.input is not an existensial",[],[],[f])

(*
fun EXISTS_EQN_FCONV f = 
    case view_form f of
        vQ("?",n,s,b) => 
        let val (eqn, pred)
            val fth = assume f
            val f0 = b
            val f0th = assume f0
            val thl = rw_tcanon f0th
   (*do not need fcanon because equalities are only between terms*)
            val f0ifff0' = 
                basic_fconv 
                    (first_conv $ List.map rewr_conv thl) no_fconv f0
            val th1 = dimp_mp_l2r f0th f0ifff0' 
            val l2r = existsE (n,s) fth th1 |> disch f
            val rform = concl th1
            val r2l = *)

(*
if define new

treat "=" differently, not using mk_pred ,only mk eq
val _ = EqSorts := "ar" :: (!EqSorts)

val _  = new_pred "=" [("f",ar_sort (mk_ob "A") (mk_ob "B")),
("g",ar_sort (mk_ob "A") (mk_ob "B"))]

val asc = rapf "!A B C. "

rapf "a = b & c = d & (a = c)"

rapf "a:A->B = b & (c:A->B = d & a = b)"
val f = “!A f:A->B. f o id(A) = f”

val th0 = mk_thm(essps, [], f)

val f' = “f o (id(A)) o id(A) o id(A) = f:A->B”


top_depth_conv (rewr_conv (spec_all th0)) (rastt "f:A->B o (id(A)) o id(A) o id(A)")

basic_fconv (rewr_conv (spec_all th0)) no_fconv f'



pred_fconv (top_depth_conv $ rewr_conv (spec_all th0)) f'

top_depth_fconv no_conv ASSUME_CONJUNCT_FCONV f

val f = it;

   P1 ⊢ Q1 ⇔ Q2
   -------------------
     ⊢ P1 ⇒ (Q1 ⇔ Q2)      ⊢ Q2 ⇒ (P1 ⇔ P2)
   - - - - - - - - - - -- - - -- - -- - -- - - - - 
            ⊢ (P1 ∧ Q1) ⇔ (P2 ∧ Q2)

“(p1 ⇒ (q1 ⇔ q2)) ∧ (q2 ⇒ (p1 ⇔ p2)) ⇔ (p1 ∧ q1 ⇔ p2 ∧ q2)”
 eq_tac >> rpt strip_tac >- eq_tac >> strip_tac >> first_assum drule >>
  strip_tac  >> fs[] >>
 strip_tac >> first_assum drule  >> strip_tac >> fs[] >>

(p1 ⇒ (q1 ⇔ q2)) ∧ (q2 ⇒ (p1 ⇔ p2)) ⇒ (p1 ∧ q1 ⇔ p2 ∧ q2)

remain 
(p1 ∧ q1 ⇔ p2 ∧ q2) ⇒ (p1 ⇒ (q1 ⇔ q2)) ∧ (q2 ⇒ (p1 ⇔ p2))

rpt strip_tac >> Cases_on ‘q1’ >> fs[] >>
fs[]
metis_tac[]
     

     (P1 ∧ P2) ∧ P3

  first, rewrite P3 while assuming P1 ∧ P2.  (Assuming P1 ∧ P2, may generate multiple rewrites.)

  then, rewrite P1 ∧ P2 while assuming P3'

     (recursively) 
         rewrite P2 while assuming P1, generating P2'
         rewrite P1 while assuming P2', generating P1'



    ⊢ P1 ⇔ P2   ⊢ Q1 ⇔ Q2 
 --------------------------
      ⊢ P1 ∧ Q1 ⇔ P2 ∧ Q2



*) 
end
