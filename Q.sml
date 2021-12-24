structure Q :> Q = 
struct
open drule tactic

fun q2str [QUOTE s] = s

fun qparse_form_with_cont ct fq =
    parse_form_with_cont ct (q2str fq)

fun qparse_term_with_cont ct tq =
    parse_term_with_cont ct (q2str tq)

fun qterm_tac ttac tq: tactic =
    fn (ct,asl,w) => ttac (qparse_term_with_cont ct tq) (ct,asl,w)

fun qterml_tac tltac qtl: tactic = 
    fn (ct,asl,w) => 
       tltac (List.map 
                  (qparse_term_with_cont ct) qtl)
             (ct,asl,w)

fun qform_tac ftac qt: tactic =
    fn (ct,asl,w) =>
       ftac (qparse_form_with_cont ct qt) (ct,asl,w)

val qexists_tac = qterm_tac exists_tac

val qexistsl_tac = qterml_tac existsl_tac

val qabbrev_tac  = qform_tac abbrev_tac

val qsuff_tac = qform_tac suffices_tac

val qby_tac = qform_tac by_tac

fun qterml_tcl (tltcl:term list -> thm_tactic -> thm_tactic) qtl thtac th :tactic = 
    fn (ct,asl,w) => tltcl (List.map (qparse_term_with_cont ct) qtl) thtac th (ct,asl,w)

val qspecl_then = qterml_tcl specl_then


fun qterm_rule (rule:term -> thm -> thm) tql th = rule (qparse_term_with_cont (cont th) tql) th
fun qterml_rule (rule:term list -> thm -> thm) tql th = rule (List.map (qparse_term_with_cont (cont th)) tql) th
val qspec = qterm_rule spec
val qspecl = qterml_rule specl

fun qpick_assum fq (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => 
       pick_assum (qparse_form_with_cont ct fq) 
                  thtac (ct,asl,w) 

fun qpick_x_assum fq (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => pick_x_assum (qparse_form_with_cont ct fq)  thtac (ct,asl,w) 

fun qgen qt th = genl [dest_var o qparse_term_with_cont (cont th) $ qt] th


(*
fun filter_cont ct = 
    let val ctl = HOLset.listItems ct
        val sctl = List.map snd ctl
        val obl = List.map fvs sctl
        val rptob = List.foldr (fn (e,s) => HOLset.add(s,e)) essps sctl
            (*mk_sss obl *)
    in HOLset.difference(ct,rptob)
    end

fun ex2fsym fsym strl th = 
    let val th' = spec_all th
        val (ct,asl) = (cont th',ant th')
        val (hyp,conc) = dest_imp (concl th')
        val inputvars0 = filter_cont (cont th') 
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) essps 
                                   (List.map (dest_var o (pwct ct)) strl)
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val inputvl = List.map (pwct ct) strl
        val ((n,s),b) = dest_exists conc
        val _ = new_fun fsym (s,List.map dest_var inputvl)
        val fterm = mk_fun fsym inputvl
        val b' = substf ((n,s),fterm) b
    in mk_thm ct asl (mk_imp hyp b')
    end

*)

(*
fun uex_def f = 
    let val ((n,s),_) = dest_exists f
        val b0 = fst (strip_exists f)
        val ct0 = fvf b0
        val v1 = pvariantt ct0 (mk_var n s)
        val (n1,s1) = dest_var v1
        val v2 = pvariantt (HOLset.add(ct0,(n1,s1))) (mk_var n s)
        val (n2,s2) = dest_var v2
        val b1 = substf ((n,s),v1) b0
        val b2 = substf ((n,s),v2) b0
        val b = mk_imp (mk_conj b1 b2) (mk_eq v1 v2)
        val conj2_rhs = mk_forall n1 s1 (mk_forall n2 s2 b)
        val rhs = mk_conj (mk_exists n s b0) conj2_rhs
        val thf = mk_dimp f rhs
    in mk_thm(fvf thf) [] thf
    end

(*function symbol from unique existence under some precondition, if no precondition then the condition is just T*)


fun filter_cont ct = 
    let val ctl = HOLset.listItems ct
        val sctl = List.map snd ctl
        val obl = List.map fvs sctl
        val rptob = (*List.foldr (fn (e,s) => HOLset.add(s,e)) essps sctl*)
            mk_sss obl
    in HOLset.difference(ct,rptob)
    end

(*val order_vars l1 user should be able to control the order of inputs*)

(*(!a. P(a) ==> Q(b) <=> (?a.P(a)) ==> Q(b))*)

fun ALL_IMP2EX_IMP0 (ns as (n,s)) P Q =
    let (* val P = mk_fvar "P"
        val Q = mk_fvar "Q"  
        val (n,s) = ("a",ob_sort)*)
        val P2Q = mk_imp P Q
        val l = mk_forall n s P2Q
        val eP = mk_exists n s P
        val r = mk_imp eP Q
        val l2r = existsE (n,s) (assume eP) (assume l |> allE (var (n,s)) |> C mp (assume P)) 
                          |> disch eP |> disch l
        val r2l = assume P |> existsI (n,s) (var(n,s)) P |> mp (assume r)
                         |> disch P |> allI (n,s) |> disch r
    in 
        dimpI l2r r2l
    end

val ALL_IMP2EX_IMP_ob = ALL_IMP2EX_IMP0 ("A",ob_sort) (mk_fvar "P") (mk_fvar "Q")
val ALL_IMP2EX_IMP_ar = ALL_IMP2EX_IMP0 ("f",ar_sort (mk_ob "A") (mk_ob "B")) (mk_fvar "P") (mk_fvar "Q")



(*TODO: check the matching to see where does P(B(0)) appear*)

(*



!A B. P(A,B) ==> Q(A)

!A.(?B. P(A,B)) ==> Q(A)

sort_of (mk_bound 1)


!y.P(x) match !y. P(y)

match_form essps “!y:A->B.ismono(x:A->B)” “!y:A->B.ismono(B(0))” mempty

match_form essps “!A. areiso(B,1)” “!A.areiso(A,1)” mempty

should raise an error here saying B cannot be matched into a bound variable.



P(B(0)) 

fun is_form f = 
...

P()




P(a)

val f = “!B. areiso(A,B) ==> areiso(A,A)”

rewr_fconv ALL_IMP2EX_IMP_ob f
val th = mk_thm (fvf f) [] f

val P = “areiso(A,B)” val Q = “areiso(A,A)”
val (n,s) = ("B",ob_sort)


val th' = rewr_rule[ALL_IMP2EX_IMP_ob] th

val f0 = “!A B. areiso(A,B) ==> areiso(A,A)”

sort_of  (mk_bound 1)      

val th0 = mk_thm (fvf f0) [] f0 |> allE (var("A",ob_sort))

val th0' = rewr_rule[ALL_IMP2EX_IMP_ob] th0


ALL_IMP2EX_IMP0 ("B",ob_sort) “areiso(A,B)” “areiso(A,A)”

have not seen the case like the wrongone produce through all these proofs, either when using convs or interactively.


val wrongone = mk_thm (fvf f0) [] f0 

rewr_rule[ALL_IMP2EX_IMP_ob] wrongone

P(B(0))

rewr_fconv (ALL_IMP2EX_IMP_ob) f0


if we reorder wrongone as 

val f0' = “!B A. areiso(A,B) ==> areiso(A,A)”

val thf0' = mk_thm (fvf f0') [] f0'

rewr_rule[ALL_IMP2EX_IMP_ob] thf0' 


val ff = “!f:A->B g:C->D. ismono(f) ==> ismono(g)”

val tth = mk_thm (fvf ff) [] ff

rewr_rule[ALL_IMP2EX_IMP_ar] tth

val ff' = “!f:A->B g:C->D. ismono(g) ==> ismono(f0)”

val tth' = mk_thm (fvf ff') [] ff'

rewr_rule[ALL_IMP2EX_IMP_ar] tth'


does nothing. 



!A B. P(A,B) ==> Q(A) 

(?B.P(A,B)) ==> Q(A)


*)


(* before ex2fsym, want to rewr_rule on the thm, then strip *)

fun ex2fsym fsym strl th = 
    let val th' = spec_all th
        val (ct,asl) = (cont th',ant th')
        val (hyp,conc) = dest_imp (concl th')
        val inputvars0 = filter_cont (cont th') 
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) essps 
                                   (List.map (dest_var o (pwct ct)) strl)
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val inputvl = List.map (pwct ct) strl
        val ((n,s),b) = dest_exists conc
        val _ = new_fun fsym (s,List.map dest_var inputvl)
        val fterm = mk_fun fsym inputvl
        val b' = substf ((n,s),fterm) b
    in mk_thm ct asl (mk_imp hyp b')
    end

*)

end
