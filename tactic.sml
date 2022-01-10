structure tactic :> tactic = 
struct
open term form logic drule abbrev conv

fun empty th [] = th
  | empty th _ = raise simple_fail "empty" 

fun sing f [x] = f x
  | sing f _ = raise simple_fail "sing" 

fun pairths f [x, y] = f x y
  | pairths f _ = raise simple_fail "pairths" 

val accept_tac = 
 fn th => fn (ct,asl,w) =>
    if eq_form(concl th,w)  then ([], empty th) 
    else raise ERR ("accept_tac.concl of th not equal to the goal",[],[],[concl th,w])

val T_INTRO_TAC:tactic = 
 fn (ct,asl,w) => 
    if eq_form(w,TRUE) then ([], empty (trueI asl))
    else raise ERR ("T_intro_tac.the goal is not T",[],[],[w])

fun gen_tac (ct,asl,w) = 
    case view_form w of
        vQ("!",n,s,b) =>
        let val t0 = pvariantt ct (mk_var (n,s))
            val w' = substf ((n,s),t0) b 
            val ct' = HOLset.union(ct,fvt t0) 
        in
            ([(ct',asl,w')], sing (allI (dest_var t0)))
        end
        | _ => raise ERR ("gen_tac.goal is not universally quantified",[],[],[w])


fun spec_tac0 (n,s): tactic = 
    fn (ct,asl,w) =>
    let val ct' = HOLset.delete(ct,(n,s))
        val w' = mk_forall n s w
    in
        ([(ct',asl,w')], sing $ allE $ mk_var (n,s))
    end

fun spec_tac n: tactic = 
    fn (ct,asl,w) =>
    let val (n,s) = case List.find (fn (n0,s0) => n0 = n) (HOLset.listItems ct) of
                        SOME ns => ns
                       | _ => raise simple_fail ("spec_tac.no variable with name: " ^ n)
    in spec_tac0 (n,s) (ct,asl,w)
    end


(*

A1 |- t1 A2 |- t2
 ------------------------ PROVE_HYP
 A1 u (A2 - {t1}) |- t2

*)



val assume_tac:thm_tactic = 
    fn th => fn (G:(string * sort) set,fl:form list,f:form) =>
    ([(HOLset.union(G,cont th),concl th:: fl,f)], sing (prove_hyp th))

val hyp = ant



fun drule0 optfn  th (G,fl:form list,f) = 
    let 
        val c = concl th
        val (b,vs) = strip_forall c
        val (ant',con) = dest_imp b
        fun mfn _ asm = 
            let 
                val menv = match_form (fvfl (ant th)) (fVarsl (ant th)) ant' asm mempty
                val ith = inst_thm menv (spec_all th)
            in
                SOME (mp ith (assume asm))
            end
            handle _ => NONE 
    in
        case (optfn mfn fl) of 
            NONE => raise simple_fail "drule.no match"
          | SOME th => assume_tac th (G,fl,f)
    end

val drule = drule0 first_opt

fun last_opt f l = first_opt f (rev l) 

val rev_drule = drule0 last_opt


(*
require specially that the name of free variable substituted is precisely the bounded variable name.

?B:ob. P(B) |-  ?B. P(B)           P(B) |- C
-------------------------------------------- efn (B,ob) (P(B), P(B) |- C)
?B.P(B) |- C    

*)


fun efn (n,s) (f,th) = 
    let 
        val ef = mk_exists n s f
    in
        (ef,existsE (n,s) (assume ef) th)
    end



fun match_mp_tac th (ct:cont,asl:form list,w) = 
    let
        val (impl,gvs) = strip_forall (concl th)
        val (ant,conseq) = dest_imp impl
        val (con,cvs) = strip_forall (conseq)
        val th1 = (C specl) (undisch ((C specl) th (List.map mk_var gvs))) (List.map mk_var cvs) 
        val (vs,evs) = partition (fn v => HOLset.member(fvf con,v)) gvs
        val th2 = uncurry disch (itlist efn evs (ant, th1)) 
        val (gl,vs) = strip_forall w
        val env = match_form (fvfl (hyp th)) (fVarsl (hyp th)) con gl mempty
        val ith = inst_thm env th2
        val gth = genl vs (undisch ith)
        val ant = fst (dest_imp (concl ith))
    in
        ([(ct,asl,ant)], sing (mp (disch ant gth)))
    end


(*
val (ct,asl,w) = cg $ 
e0
(rpt strip_tac >> rw[isPb_expand] >>
 qspecl_then [‘X * Y’,‘Z’,‘f o p1(X,Y)’,‘g o p2(X,Y)’] (x_choosel_then ["E","e"] assume_tac) isEq_ex >>
 qexistsl_tac [‘E’,‘p1(X,Y) o e’,‘p2(X,Y) o e’] >>
 qby_tac
 ‘f o p1(X, Y) o e = g o p2(X, Y) o e’
 >-- (rw[GSYM o_assoc] >> irule Eq_equality >> arw[]) >>
 arw[] >> rpt strip_tac >>
 qexists_tac ‘Eqa(f o p1(X,Y), g o p2(X,Y),e,Pa(u,v))’ >>
 rw[o_assoc] >>
 qby_tac
 ‘e o Eqa(f o p1(X, Y), g o p2(X, Y), e, Pa(u, v)) = 
  Pa(u,v)’ >--
 (flip_tac >> irule Eqa_eqn >> arw[o_assoc,p12_of_Pa]) >>
 arw[p12_of_Pa] >> rpt strip_tac >>
 drule Eqa_Mono >> fs[Mono_def] >> first_x_assum irule)
(form_goal
 “!X Z f:X->Z Y g:Y->Z. ?P p:P->X q. isPb(f,g,p,q)”);

*)
(*

A ==> !x. C x
---
!x. A ==> C
---

both directions 


A /\ B ==>C 

<=>

A ==> B ==> C

prove as a thm and rw with this

*)


fun conj_tac ((G,fl,f):goal):goal list * validation = 
    case view_form f of 
        (vConn("&",[f1,f2])) =>
        ([(G,fl,f1), (G,fl,f2)], pairths conjI)
      | _ => raise ERR ("conj_tac.not a conjunction",[],[],[f])

fun disj1_tac (g:goal as (G,fl,f)) = 
    case view_form f of
        vConn("|",[f1,f2]) => 
        ([(G,fl,f1)], sing (disjI1 f2))
      | _ => raise ERR ("disj1_tac.not a disjunction",[],[],[f])

fun disj2_tac (G,fl,f) = 
    case view_form f of
        vConn("|",[f1,f2]) => 
        ([(G,fl,f2)], sing (disjI2 f1))
      | _ => raise ERR ("disj2_tac.not a disjunction",[],[],[f])

                   
fun cases_on c (G,fl,f) =
    let 
        val G' = HOLset.union(G,fvf c)
    in
        ([(G',c::fl,f),(G',(mk_neg c)::fl,f)], pairths (disjE (tautI c))) 
    end

fun contra_tac (g:goal as (G,fl,f)) = 
    case view_form f of
        vConn("~",[A]) => 
        ([(G,A::fl,FALSE):goal], sing (negI A))
      | _ => raise ERR ("contra_tac.goal is not a negation",[],[],[f])


fun ccontra_tac (g:goal as (G,fl,f)) = 
    case view_form f of
        vConn("~",[A]) => 
        ([(G,A::fl,FALSE):goal], sing (negI A))
      | _ => 
        ([(G,(mk_neg f)::fl,FALSE):goal], fn [th] => dimp_mp_l2r (negI (mk_neg f) th) (double_neg f)
                          | _ => raise simple_fail "ccontra_tac.incorrect number of list items")



fun imp_tac (G,fl,f) = 
    case view_form f of 
        vConn("==>",[f1,f2]) => 
        ([(G,f1::fl,f2)], sing (disch f1))
      | _ => raise ERR ("imp_tac.goal is not an implication",[],[],[f])
 
 
fun dimp_tac (G,fl,f) = 
    case view_form f of
        vConn("<=>",[f1,f2]) => 
        ([(G,fl,mk_imp f1 f2),(G,fl,mk_imp f2 f1)],
         pairths dimpI)
      | _ => raise ERR ("dimp_tac.goal is not an double imp",[],[],[f])


fun conj_tac ((G,fl,f):goal):goal list * validation = 
    case view_form f of 
        (vConn("&",[f1,f2])) =>
        ([(G,fl,f1), (G,fl,f2)], pairths conjI)
      | _ => raise ERR ("conj_tac.goal is not conjunction",[],[],[f])

fun exists_tac t (G,fl,f) = 
    case view_form f of 
        vQ("?",n,s,b) =>
        if sort_of t = s then 
            let val nv = mk_var(n,s)
            in
            ([(G,fl,substf ((n,s),t) b)], 
             sing (existsI (dest_var nv) t (substf ((n,s),nv) b)))
            end
        else raise ERR ("exists_tac.inconsist sorts",[sort_of t,s],[t,mk_var(n,s)],[])
      | _ => raise ERR ("exists_tac.goal is not an existential",[],[],[f])



fun spec_all_tac (G,fl,f) = 
    case view_form f of
        vQ("!",n,s,b) =>
        let val f' = subst_bound (mk_var(n,s)) b 
            val G' = HOLset.union(G,fvt (mk_var(n,s))) 
        in
            ([(G',fl,f')], sing (allI (n,s)))
        end
        | _ => raise ERR ("spec_all_tac.goal is not universally quantified",[],[],[f])

 

fun then_tac ((tac1:tactic),(tac2:tactic)) (G,fl,f) = 
    let val (gl,func) = tac1 (G,fl,f)
        val branches = List.map tac2 gl
        val gl1 = flatten (fst $ unzip branches)
        fun func1 l = 
            (if List.length l = List.length gl1 then 
                 func (mapshape (List.map List.length (fst $ unzip branches))
                           (List.map (fn (a,b) => b) branches) l)
             else raise ERR ("then_tac.length list not consistent,start with respectively: ",[],[],[concl (hd l),#3 (hd gl1)]))
    in (gl1,func1) 
    end


val op >> = then_tac

fun then1_tac ((tac1:tactic),(tac2:tactic)) (G,fl,f) = 
    let val (gl,func) = tac1 (G,fl,f)
        val (gl1,func1) = tac2 (hd gl)
        val gl' = gl1 @ (tl gl)
        fun func' l = 
            (if length l = length gl' then
                 case view_thm (func1 (List.take (l,length gl1))) of vThm(G,A,C) =>
                 func (mk_thm(G,A,C) :: (List.drop (l,length gl1)))
             else raise simple_fail "then1_tac.incorrect number of list items")
    in (gl',func')
    end
 

val op >-- = then1_tac


fun op Orelse (tac1:tactic, tac2:tactic) = 
    fn (g as (G,fl,f)) =>
       tac1 g handle _ => tac2 g

infix Orelse


val stp_tac = conj_tac Orelse contra_tac Orelse imp_tac Orelse gen_tac

fun all_tac (G,fl,l) =  ([(G,fl,l):goal],sing I)

fun try tac:tactic = tac Orelse all_tac

fun repeat tac g = ((tac >> (repeat tac)) Orelse all_tac) g


fun fconv_tac fc (G,fl,f) = 
    let 
        val th = fc f
        val G' = HOLset.union(G,cont th)
        val (_,rhs) = dest_dimp (concl th)
    in
        if eq_form (rhs,TRUE) 
        then ([],empty (add_cont G' $ dimp_mp_l2r (trueI []) (iff_swap th)))
        else
            ([(G',fl,rhs)],
              sing (dimp_mp_r2l (fc f)))
    end


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

(*val th0 = mk_thm essps [] (rapf "!a b c. a = b & !a. b = a & !d. d = g");

tested rw_tcanon.
*)


fun is_refl_eq f = 
    if is_eq f then let val (l,r) = dest_eq f in if (*eq_term(dest_eq f)*) l = r  then true else false end
    else false


fun is_refl_dimp f = 
    if is_dimp f then if eq_form(dest_dimp f) then true else false
    else false

fun is_refl_th th = 
    is_refl_eq (concl th) orelse is_refl_dimp (concl th)

fun rewr_no_refl_conv th t = 
    let val th' = rewr_conv th t 
    in if is_refl_th th' then
           raise ERR ("rewr_no_refl_conv.the result of term matching is a refl",[],[],[concl th'])
       else th'
    end


fun rewr_no_refl_fconv th f = 
    let val th' = rewr_fconv th f
    in if is_refl_th th' then
           raise ERR ("rewr_no_refl_fconv.the result of form matching causes loop",[],[],[concl th'])
       else th'
    end


fun once_rw_tac thl = 
    let 
        val conv = first_conv (mapfilter rewr_no_refl_conv (flatten (mapfilter rw_tcanon thl)))
        val fconv = first_fconv (mapfilter rewr_no_refl_fconv (flatten (mapfilter rw_fcanon thl)))
    in fconv_tac (basic_once_fconv conv fconv) 
    end

(*TODO: !X (f : X# -> A)  (g : X# -> B). g# = p2 o pa(p1, p2, f#, g#)

check before rewr_conv that the variables in RHS is a subset of the variables in the LHS.

if subset error happens then drop the thm and do not use it.

 *)


(*
fun once_rw_tac thl = gen_rw_tac basic_once_fconv  (flatten (mapfilter conv_canon thl))
*)

(*
fun rw'_conv th t = part_tmatch
okay to let rw_conv loop, but do check here, and discard the thm after inst raise ERR if do not like it.

*)







fun occurs_tt t1 t2 = PolyML.pointerEq(t1,t2) orelse
   t1 = t2 orelse
    case (view_term t1,view_term t2) of 
        (vVar (n1,s1),vVar (n2,s2)) => 
        if n1 = n2 andalso s1 = s2 then 
            true 
        else if occurs_ts t1 s2 then true 
        else false
      | (vVar(n,s1),vFun(f,s2,l)) => 
        occurs_ts t1 s2 orelse List.exists (occurs_tt t1) l
      | _ => false
and occurs_ts t s = 
    case dest_sort s of 
        (_, tl) => List.exists (occurs_tt t) tl

fun occurs_f f1 f2 = PolyML.pointerEq(f1,f2) orelse
    case (view_form f1,view_form f2) of
        (vPred _,vPred _) => eq_form(f1,f2)
      | (vQ(q1,n1,s1,b1) ,vQ(q2,n2,s2,b2)) => 
        eq_form(f1,f2) orelse occurs_f f1 b2
      | (_,vConn(co,fl)) => List.exists (occurs_f f1) fl
      | (_,vQ(_,_,_,b)) => occurs_f f1 b
      | (_,_) => false





fun cause_loop_eq th = 
    let val (l,r) = dest_eq(concl th)
    in if occurs_tt l r then true else false
    end


fun cause_loop_dimp th = 
    let val (l,r) = dest_dimp(concl th)
    in if occurs_f l r then true else false
    end

fun rewr_no_loop_conv th t = 
    let val th' = rewr_conv th t 
    in if cause_loop_eq th' then
           raise ERR ("rewr_no_loop_conv.the result of term matching causes loop",[],[],[concl th'])
       else th'
    end


fun rewr_no_loop_fconv th f = 
    let val th' = rewr_fconv th f
    in if cause_loop_dimp th' then
           raise ERR ("rewr_no_loop_fconv.the result of form matching causes loop",[],[],[concl th'])
       else th'
    end

fun rw_tac thl:tactic = 
    let 
        val conv = first_conv (mapfilter rewr_no_refl_conv (flatten (mapfilter rw_tcanon thl)))
        val fconv = first_fconv (mapfilter rewr_no_refl_fconv (flatten (mapfilter rw_fcanon thl)))
    in fconv_tac (basic_fconv conv fconv) 
    end


fun no_loop_rw thl:tactic = 
    let 
        val conv = first_conv (mapfilter rewr_no_loop_conv (flatten (mapfilter rw_tcanon thl)))
        val fconv = first_fconv (mapfilter rewr_no_loop_fconv (flatten (mapfilter rw_fcanon thl)))
    in fconv_tac (basic_fconv conv fconv) 
    end



fun by_tac f0 (G,fl,f) = 
    let 
        val G' = HOLset.union(G,fvf f0) 
    in
    ([(G',fl,f0),(G',f0::fl,f)], pairths prove_hyp)
    end


fun suffices_tac f0 (G,fl,f) = 
    let
        val G' = HOLset.union(G,fvf f0)
    in 
        ([(G',fl,mk_imp f0 f),(G',fl,f0)], pairths mp)
    end

fun mp_tac th0 (G,asl,w) = 
    let val G' = HOLset.union(G,cont th0) in
    ([(G',asl, mk_imp (concl th0) w)], fn [th] => mp th th0) end

fun assum_list aslfun (g as (_,asl, _)) = aslfun (List.map assume asl) g

fun arw_tac thl = assum_list (fn l => rw_tac (l @ thl))

fun no_loop_arw thl = assum_list (fn l => no_loop_rw (l @ thl))

fun once_arw_tac thl = assum_list (fn l => once_rw_tac (l @ thl))

fun pop_assum_list (asltac:thm list -> tactic):tactic = 
    fn (G,asl, w) => asltac (List.map assume asl) (G,[], w) 

fun excl_ths P thlt: thm list -> tactic = 
    fn thl => 
       let val (_,ths) = partition P thl
       in thlt ths
       end


fun pop_assum thfun (ct,a :: asl, w) = thfun (assume a) (ct,asl, w)
  | pop_assum   _   (_,[], _) = raise simple_fail"pop_assum.no assum"

fun rev_pop_assum thfun (ct,a :: asl, w) = thfun (assume (hd (rev (a :: asl)))) (ct,(rev (tl (rev (a :: asl)))), w)
  | rev_pop_assum   _   (_,[], _) = raise simple_fail"rev_pop_assum.no assum"



fun every tacl = List.foldr (op then_tac) all_tac tacl

fun map_every tacf lst = every (List.map tacf lst) 

fun rule_assum_tac rule: tactic =
    pop_assum_list
        (fn asl => map_every assume_tac (rev_itlist (cons o rule) asl []))

fun choose_tac cn a0:tactic = 
    fn (ct,asl,w) => 
       let val _ = fmem a0 asl orelse
                   raise ERR ("choose_tac.formula to be substitute not in assumption list",[],[],[a0])
           val _ = not (mem cn (List.map fst (HOLset.listItems ct))) 
                   orelse raise simple_fail "name to be choose is already used"
           val ((n,s),b) = dest_exists a0
           val newasm = substf ((n,s),mk_var(cn,s)) b
       in ([(HOLset.add(ct,(cn,s)),newasm ::(ril a0 asl),w)],
           sing (existsE (cn,s) (assume a0)))
       end

fun masquerade (G,fl,f) = mk_thm(G,fl,f)

datatype validity_failure = Concl of form | Ant of form| Cont of (string * sort)

fun bad_prf th (ct,asl,w) =
    if not (eq_form(concl th,w)) then SOME (Concl (concl th))
    else
        let val clth = HOLset.listItems (cont th)
            val clct = HOLset.listItems ct
        in 
            case
                List.find 
                    (fn ns0 => List.all (fn ns => not (fst ns = fst ns0 andalso (*eq_sort(snd ns,snd ns0) *) snd ns = snd ns0)) clct) clth
             of
                SOME ns => SOME (Cont ns)
              | NONE => 
                (case List.find (fn h => List.all (not o ((curry eq_form) h)) asl)
                               (ant th) of
                    NONE => NONE
                  | SOME h => SOME (Ant h))
        end

(*AQ:what todo if I want to pp the ns of Cont ns with its sort here? *)

fun error f t e =
       let
         val pfx = "Invalid " ^ t ^ ": theorem has "
         val (desc, sl,tl,fl) =
             case e of
                 Ant h => ("bad hypothesis",[],[],[h])
               | Concl c => ("wrong conclusion",[],[],[c])
               | Cont ns => ("extra variable involved",[snd ns],[mk_var ns],[])
       in
         raise ERR (desc,sl,tl,fl)
       end

(*check the validaty error message: TODO, add term/form information*)

fun valid (tac: tactic) : tactic =
      fn g: goal =>
         let
            val (result as (glist, prf)) = tac g
         in
           case bad_prf (prf (List.map masquerade glist)) g of
               NONE => result
             | SOME e => error "VALID" "tactic" e
         end

infix then_tcl
infix orelse_tcl

fun (ttcl1: thm_tactical) then_tcl (ttcl2: thm_tactical) =
   fn ttac => ttcl1 (ttcl2 ttac)

fun (ttcl1: thm_tactical) orelse_tcl (ttcl2: thm_tactical) =
   fn ttac => fn th => ttcl1 ttac th handle _ => ttcl2 ttac th

fun repeat_tcl ttcl ttac th =
   ((ttcl then_tcl (repeat_tcl ttcl)) orelse_tcl I) ttac th

val all_then: thm_tactical = I
val no_then: thm_tactical = fn ttac => fn th => raise simple_fail "no_then"
val first_tcl = List.foldr (op orelse_tcl) no_then

val contr_tac: thm_tactic =
   fn cth => fn (ct,asl, w) =>
      let
         val th = contr w cth
      in
         ([], empty th)
      end
      handle e => raise (wrap_err "contr_tac." e)

fun first tacl g =
    case tacl of
        [] => raise simple_fail "no tactic"
      | h :: t => h g handle _ => (first t) g

fun conjuncts_then2 ttac1 ttac2 =
   fn cth =>
      let
         val (th1,th2) = conj_pair cth
      in
         then_tac (ttac1 th1, ttac2 th2)
      end

val conjuncts_then:thm_tactical = fn ttac => conjuncts_then2 ttac ttac

(* --------------------------------------------------------------------------*
 * OPPOSITE_TAC: proves the goal using the theorem p and an assumption ~p.   *
 * --------------------------------------------------------------------------*)

(*F_imp f = ~f ⇒ f ⇒ F
 
th = A |- C 

th' =  A' |- ~C

~C ⇒ C ⇒ F 
A,A' |- F
*)

fun resolve th th' = mp (mp (F_imp (concl th)) th') th
                     handle e => raise (wrap_err "resolve." e)

fun target_rule tm =
      if is_neg tm then (dest_neg tm, Lib.C resolve) else (mk_neg tm, resolve)

fun opposite_tac th:tactic = fn (ct,asl, w) =>
    let
        val (opp, rule) = target_rule (concl th)
    in
        case List.find ((C (curry eq_form)) opp) asl of
            NONE => raise simple_fail "opposite_tac"
          | SOME asm => contr_tac (rule th (assume asm)) (ct,asl, w)
    end

(*discard_tac*)

(* --------------------------------------------------------------------------*
 * DISCARD_TAC: checks that a theorem is useless, then ignores it.           *
 *  TODO: do not quite understand why it is necessary                                                  *
 * --------------------------------------------------------------------------*)

fun discard_tac th (ct,asl, w) =
   if Lib.exists ((curry eq_form) (concl th)) (TRUE :: asl) andalso HOLset.isSubset(cont th,ct)
      then all_tac (ct,asl, w)
   else raise simple_fail "discard_tac"


fun foo th m = mp (disch (concl th) (assume m)) th 
               handle e => raise wrap_err "foo." e


fun disj_cases_then2 (ttac1:thm_tactic) (ttac2:thm_tactic):thm_tactic =
   fn disth =>
   let
      val (disj1, disj2) = dest_disj (concl disth)
   in
      fn g  =>
         let
            val (gl1, prf1) = ttac1 (foo disth disj1) g
            and (gl2, prf2) = ttac2 (foo disth disj2) g
         in
            (gl1 @ gl2,
             fn thl =>
               let
                  val (thl1, thl2) = split_after (length gl1) thl
               in
                  disjE disth (prf1 thl1) (prf2 thl2)
               end)
         end
   end
   handle e => raise wrap_err "disj_cases_then2." e
 
val disj_cases_then: thm_tactical = fn ttac => disj_cases_then2 ttac ttac


(*choose_then*)

fun foo th m = mp (disch (concl th) (assume m)) th 
               handle e => raise wrap_err "foo." e

fun x_choose_then n0 (ttac: thm_tactic) : thm_tactic =
   fn xth =>
      let
         val ((n,s),b) = dest_exists (concl xth)
      in
         fn (ct,asl,w) =>
            let
               val th = add_cont (HOLset.add(essps,(n0,s)))
                                 (foo xth (substf ((n,s),mk_var (n0,s)) b))              
               val (gl,prf) = ttac th (ct,asl,w)
            in
               (gl, (existsE (n0,s) xth) o prf)
            end
      end
      handle e => raise wrap_err "x_choose_then." e

fun x_choosel_then nl (ttac: thm_tactic):thm_tactic =
    case nl of
        [] => ttac 
      | h :: t => x_choose_then h (x_choosel_then t ttac)



fun specl_then tl (ttac: thm_tactic): thm_tactic = 
    fn th => ttac (specl tl th)

val choose_then: thm_tactical =
   fn ttac => fn xth =>
      let
         val (cot,hyp,conc) = dest_thm xth
         val ((n,s),_) = dest_exists conc
      in
         fn (ct,asl,w) =>
         let
             val vd = HOLset.union(cot,ct)
             val y = pvariantt vd (mk_var(n,s))|> dest_var|> fst
         in
            x_choose_then y ttac xth (ct,asl,w)
         end
      end
      handle e => raise wrap_err "choose_then." e

val choose_tac' = choose_then assume_tac

fun x_choose_tac x = x_choose_then x assume_tac

fun x_choosel_tac xs = x_choosel_then xs assume_tac 

val check_assume_tac: thm_tactic =
   fn gth =>
      first [contr_tac gth, accept_tac gth, opposite_tac gth,
             discard_tac gth,assume_tac gth]
      handle e => raise wrap_err "check_assume_tac." e

val strip_thm_then = first_tcl [conjuncts_then, disj_cases_then, choose_then]

val strip_assume_tac = repeat_tcl strip_thm_then check_assume_tac
                       handle e => raise wrap_err "strip_assume_tac." e

(*val STRIP_ASM_CONJ_TAC = conjuncts_then assume_tac*)

fun find (ttac:thm_tactic) goal [] = raise simple_fail "find"
    | find ttac goal (a :: L) =
      ttac (assume a) goal handle _ => find ttac goal L
 
fun first_assum ttac = fn (ct,asl, w) => find ttac (ct,asl,w) asl

fun pick_assum f ttac = fn (ct,asl, w) => ttac (assume f) (ct,asl, w)

fun last_assum ttac = fn (ct,asl, w) => find ttac (ct,asl,w) (rev asl)

fun undisch_then f (ttac:thm_tactic): tactic = fn (ct,asl, w) =>
      let val (_, A) = Lib.pluck ((curry eq_form) f) asl in ttac (assume f) (ct,A, w) end

local
    fun f ttac th = undisch_then (concl th) ttac
in
val first_x_assum = first_assum o f
val last_x_assum = last_assum o f
fun pick_x_assum f0 = (pick_assum f0) o f
end



fun rewr_rule thl =
    let 
        val c = first_conv (mapfilter rewr_no_loop_conv (flatten (mapfilter rw_tcanon thl)))
        val fc = first_fconv (mapfilter rewr_no_loop_fconv (flatten (mapfilter rw_fcanon thl)))
    in
        conv_rule (basic_fconv c fc)
    end


fun arw_rule thl th = rewr_rule ((List.map assume $ ant th) @ thl) th

fun abbrev_tac eq0:tactic = 
    fn (ct,asl,w) => 
       let 
           val (lhs,rhs) = dest_eq eq0
           val (n,s) = dest_var rhs
           val _ = HOLset.isSubset(fvt lhs,ct) orelse
                   raise simple_fail "the term to be abbrev has unknown variable" 
           val _ = not (mem n (List.map fst (HOLset.listItems ct)))
                   orelse raise simple_fail "name of the abbrev is already used"
           val eth =  existsI (n,s) lhs (mk_eq lhs (mk_var(n,s))) (refl lhs) 
       in
           ([(HOLset.add(ct,(n,s)),eq0::asl,w)],sing $ existsE (n,s) eth)
       end


(*
x = 3, take every  x into 3.

... & !x. ...

If go into a binder with intersects of the fv of the LHS of the eqn, then stop.

use sub_fconv to go through subforms/subterms

*)
(*subst_all_tac which does not do matching, but check for exactly the occurrence of some term. *)

fun remove_asm_tac f: tactic = 
    fn (ct,asl,w) =>
       if fmem f asl then 
           ([(ct,ril f asl,w)], sing (add_assum f))
       else raise ERR ("assumption to be removed is not in the assumption list",[],[],[f])

 

val once_rwl_tac = map_every (fn th => once_rw_tac[th])
val once_arwl_tac = map_every (fn th => once_arw_tac[th])



fun disch_then (ttac: thm_tactic): tactic = 
 fn ((ct,asl,w):goal) =>
   let
      val (ant, conseq) = dest_imp w
      val (gl, prf) = ttac (assume ant) (ct,asl,conseq)
   in
      (gl, (if is_neg w then neg_disch ant else disch ant) o prf):(goal list * validation)
   end
 

fun strip_goal_then ttac : tactic = first [gen_tac, conj_tac, disch_then ttac] 

val strip_tac:tactic = fn g => strip_goal_then strip_assume_tac g

fun disch_tac g = disch_then assume_tac g 


fun simp_asm thms (t, l') = rewr_rule (l' @ thms) t :: l'



fun f r (tac:thm_tactic) thms asms:tactic = 
    map_every tac (r (List.foldl (simp_asm thms) [] (r asms)))

fun gen_full_simp_tac r tac thms =
    pop_assum_list (f r tac thms) then_tac arw_tac thms
 
val full_tac = gen_full_simp_tac Lib.I
val rev_full_tac = gen_full_simp_tac List.rev

fun full_simp_tac thms = 
    pop_assum_list (f Lib.I strip_assume_tac thms) then_tac arw_tac thms

fun rev_full_simp_tac thms = 
    pop_assum_list (f List.rev strip_assume_tac thms) then_tac arw_tac thms



val cheat:tactic = fn (ct,asl,w) => ([], fn _ => mk_thm(ct,asl,w))


val rw = rw_tac
val arw = arw_tac
val once_rw = once_rw_tac
val once_arw = once_arw_tac

val fs = full_simp_tac
val rpt = repeat  

fun existsl_tac l = map_every (exists_tac) l




fun sspecl tl th = 
    let val (b,vs) = strip_forall $ concl th
        val ars = List.filter (fn (n,s) => not (on_ground o fst o dest_sort o snd $ (n,s))) vs
        val env = match_tl essps (List.map mk_var ars) tl emptyvd
        val tl' = List.map (inst_term env) (List.map mk_var vs)
    in specl tl' th
    end


fun sspecl_then tl (ttac: thm_tactic): thm_tactic = 
    fn th => ttac (sspecl tl th)

(*val qsspecl_then = qterml_tcl sspecl_then *)


end
    
