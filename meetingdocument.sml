(*1.top_depth_fconv should make change, but not, since if a conv in some argument fails, then will not rw a term, how am I suggested to change it? just edit the arg_conv? No counterpart of this in HOL, the code is steal from Larry's paper. *)

top_depth_conv (rewr_conv (assume “nas':mem(Pow(N * A)) = Ins(Pair(CARD(nas0), a0), nas0)”))
(rastt "Ins(Pair(CARD(nas':mem(Pow(N * A)) ), a), nas')")

(*the above works, but not as in the goal*)

val isL_cases = prove_store("isL_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!nas. isL(nas) ==> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (isL_ind |> allE (rastt "A")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] (*figure out why the arw work here*)>> 
      qexistsl_tac [‘Empty(N * A)’,‘a’] >> 
      rw[isL_rules]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘nas'’,‘a’] >> rw[] >> arw[] >>
 match_mp_tac isL_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[isL_rules] >>
 arw[] >> match_mp_tac isL_rules_step >> arw[])
(form_goal
 “!A nas. isL(nas) <=> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))”));


val c = rewr_conv (assume “nas':mem(Pow(N * A)) = Ins(Pair(CARD(nas0), a0), nas0)”)


val f = “?nas0:mem(Pow(N * A)) a0:mem(A).
          Ins(Pair(CARD(nas'), a), nas') =
          Ins(Pair(CARD(nas0), a0), nas0) & isL(nas0)”


top_depth_fconv (top_depth_conv c) no_fconv f (*no change *)


val f1 = “Ins(Pair(CARD(nas'), a), nas') =
          Ins(Pair(CARD(nas0:mem(Pow(N * A))), a0:mem(A)), nas0) & isL(nas0)”


top_depth_fconv (top_depth_conv c) no_fconv f1 (*made change *)


val f2 = “?a0.Ins(Pair(CARD(nas'), a), nas') =
          Ins(Pair(CARD(nas0:mem(Pow(N * A))), a0:mem(A)), nas0) & isL(nas0)”

top_depth_fconv (top_depth_conv c) no_fconv f2 (*no change *)

exists_fconv (top_depth_fconv (top_depth_conv c) no_fconv) f2

val f1f1' = (top_depth_fconv (top_depth_conv c) no_fconv) f1


val f21 = rename_bound "a1" f2;


exists_fconv (top_depth_fconv (top_depth_conv c) no_fconv) f21

(*so is the way of edit exists_fconv handle err as renaming variables?*)


(*




top_depth_conv c
(rastt "Ins(Pair(CARD(nas':mem(Pow(N * A)) ), a), nas')")

top_depth_fconv (top_depth_conv c) no_fconv
“?aa.Ins(Pair(CARD(nas':mem(Pow(N * A)) ), a), nas') = aa & P(a)”


(*does not work*)



top_depth_fconv 
(first_conv 
(List.map rewr_conv
[assume “xs = xs':mem(Pow(X))”,
 assume “n = n0:mem(N)”]))
no_fconv
“Cd(xs:mem(Pow(X)),n:mem(N))”

(*the above works since it is first_fconv, so success on both inputs*)

top_depth_fconv 
(first_conv 
(List.map rewr_conv
[assume “xs = xs':mem(Pow(X))”]))
no_fconv
“Cd(xs:mem(Pow(X)),n:mem(N))”

basic_fconv (rewr_conv (assume “xs = xs':mem(Pow(X))”))
no_fconv
“Cd(xs:mem(Pow(X)),n:mem(N))”

top_depth_fconv 
(rewr_conv (assume “nas' = Empty(N * A)”))
no_fconv
“Ins(Pair(CARD(nas':mem(Pow(N * A))), a:mem(A)), nas') = aa”

basic_fconv 
(rewr_conv (assume “nas' = Empty(N * A)”))
no_fconv
“Ins(Pair(CARD(nas':mem(Pow(N * A))), a:mem(A)), nas') = aa”

(*because nas' is wrapped in some function which has one input...*)

(*
should I edit the code in sub_fconv, so it use pred_fconv (try_conv c) instead of just c? 
Or edit top_depth_fconv, so it use try somewhere?

But HOL does not do this:

fun TOP_DEPTH_CONV conv tm =
   (REPEATC conv THENC
    TRY_CONV (CHANGED_CONV (SUB_CONV (TOP_DEPTH_CONV conv)) THENC
              TRY_CONV (conv THENC TOP_DEPTH_CONV conv))) tm


how it deal with the situation like mine?
*)


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

*)


(*2. my new fVar_Inst, any obvious improvement?*)



Q := x + y 

argl [x,y]

args0 [2,a]

P(a:mem(A * B))

P(a:mem(A))

ListPair.foldl 



(*make it into form.sml so does not need to call view_form, does not need to worry about capture.*)


“!a b. P(a,b)”

“P(m,n) <=> m < n”

local 

fun match_term_pri = 

fun inst_thm_pri


(*raise unchanged exception if doesn not made change to the formula

“P(a,b) & Inj(f)”

calculate fVar_inst in LHS, if exception, then try other part, if all parts raises exception, then throw exn

fun COMB2_CONV (c1,c2) tm =
   let
      val {Rator, Rand} = dest_comb tm
   in
      let
         val th = c1 Rator
      in
         MK_COMB (th, c2 Rand) handle UNCHANGED => AP_THM th Rand
      end
      handle UNCHANGED => AP_TERM Rator (c2 Rand)
   end


in Conv.sml

*)
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



fun spec_fVar pdef th = 
    let val (l,r) = dest_dimp pdef 
        val (P,vars0) = dest_fvar l
        val vars = List.map dest_var vars0
    in fVar_Inst_th (P,(vars,r)) th
    end

(* 3. ind_with function and soe examples: redefined match_mp_tac sine the old one used genl, messed up the order of variables. more examples in relnbyhand*)




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


val Sub_mono_eq = prove_store("Sub_mono_eq",
e0
(strip_tac >> ind_with N_ind_P >> rw[Sub_O,Sub_Suc,Suc_def] >> 
 rpt strip_tac (* 2 *) >-- rw[Pre_Suc] >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!m n. Sub(Suc(m),Suc(n)) = Sub(m,n)”));


(*4. reln by hand basically uniform but not absolutely uniform. Any suggested approach of normalising them?*)

val AX4 = new_ax
“?N0 O0:mem(N0) S0:N0->N0. isFun(S0) & (!n:mem(N0). ~(Eval(S0,n) = O0)) & 
 !n m. Eval(S0,n) = Eval(S0,m) <=> n = m”


val inN_def = define_pred
“!n:mem(N0). inN(n) <=>
(!P.IN(O0,P) &
 (!n0. IN(n0,P) ==> IN(Eval(S0,n0),P)) ==> 
 IN(n,P))”


val inN_ind0 = 
    inN_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “inN(n)”
            |> gen_all
            |> disch_all 
            |> gen_all

local 
val l = allE (rastt "N0") IN_def_P_expand
in
val inN_ind = prove_store("inN_ind",
e0
(strip_tac >> rw[inN_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !n:mem(N0). IN(n,P0) <=> P(n)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “(P(O0) &
   (!n0. P(n0) ==> P(Eval(S0,n0))) ==>
  !n.inN(n) ==> P(n))”))
end

val inN_rules = prove_store("inN_rules",
e0
(strip_tac >-- (rw[inN_def] >> rpt strip_tac) >>
 rw[inN_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “inN(O0) & 
  (!n. inN(n) ==> inN(Eval(S0,n)))”));

val inN_rules_step = inN_rules |> conjE2


(*inN_cases there is a case that rw does not work and do not know why*)
val inN_cases = prove_store("inN_cases",
e0
(strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!n0. inN(n0) ==> (n0 = O0 |
  (?a. n0 = Eval(S0,a) & inN(a)))’
 >-- (strip_tac >> arw[]) >>
 ind_with inN_ind >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexists_tac ‘O0’ >> rw[inN_rules]) >>
 disj2_tac >> qexists_tac ‘n0'’ >> rw[] >>
 arw[] >> match_mp_tac inN_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[inN_rules] >>
 arw[] >> match_mp_tac inN_rules_step >> arw[])
(form_goal
 “!n0. inN(n0) <=> (n0 = O0 |
  (?a. n0 = Eval(S0,a) & inN(a)))”));



val FI_def = define_pred 
“!X xs:mem(Pow(X)). FI(xs) <=> 
 !P. (IN(Empty(X),P) &
      (!xs. IN(xs,P)==> !x.IN(Ins(x,xs),P))) ==>
     IN(xs,P)”



val FI_ind0 = 
    FI_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “FI(xs:mem(Pow(X)))”
            |> gen_all
            |> disch_all 
            |> gen_all

local 
val l = allE (rastt "Pow(X)") IN_def_P_expand
in
val FI_ind = prove_store("FI_ind",
e0
(strip_tac >> strip_tac >> rw[FI_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !xs:mem(Pow(X)). IN(xs,P0) <=> P(xs)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “!X.(P(Empty(X)) &
   (!xs. P(xs) ==> !x:mem(X).P(Ins(x,xs)))) ==>
  !xs:mem(Pow(X)).FI(xs) ==> P(xs)”))
end

val FI_rules = prove_store("FI_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[FI_def] >> rpt strip_tac) >>
 rw[FI_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “!X. FI(Empty(X))& 
     (!xs:mem(Pow(X)). FI(xs) ==> !x. FI(Ins(x,xs)))”));

val FI_rules_step = FI_rules |> spec_all |> conjE2


val FI_cases = prove_store("FI_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!xs. FI(xs) ==> (xs = Empty(X) |
  (?xs0 x0. xs = Ins(x0,xs0) & FI(xs0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (FI_ind |> allE (rastt "X")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘Empty(X)’,‘x’] >> 
     rw[FI_rules]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘xs'’,‘x’] >> rw[] >> arw[] >>
 match_mp_tac FI_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[FI_rules] >>
 arw[] >> match_mp_tac FI_rules_step >> arw[])
(form_goal
 “!X xs. FI(xs) <=> (xs = Empty(X) |
  (?xs0 x0. xs = Ins(x0,xs0) & FI(xs0)))”));


val Cd_def = define_pred
“!X xs:mem(Pow(X)) n. Cd(xs,n) <=>
(!P.IN(Pair(Empty(X),O),P) &
   (!xs0 n0 x. IN(Pair(xs0,n0),P) & ~IN(x,xs0) ==>
   IN(Pair(Ins(x,xs0),Suc(n0)),P)) ==> 
 IN(Pair(xs,n),P))”


val Cd_ind0 = 
    Cd_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “Cd(xs:mem(Pow(X)),n)”
            |> qgen ‘n’ |> qgen ‘xs’
            |> disch_all 
            |> gen_all 

val Fst_of_Pair = prove_store("Fst_of_Pair",
e0
(rw[GSYM Fst_def,Eval_p1_Pair])
(form_goal
 “!A B a:mem(A) b:mem(B). Fst(Pair(a,b)) = a”));


val Snd_of_Pair = prove_store("Snd_of_Pair",
e0
(rw[GSYM Snd_def,Eval_p2_Pair])
(form_goal
 “!A B a:mem(A) b:mem(B). Snd(Pair(a,b)) = b”));


(* try to always apply Fst_of_Pair/Snd_of_pair.
   figure out a drule of doing this, instead of a tactic.
*)
local 
val l = allE (rastt "Pow(X) * N") IN_def_P_expand |>
spec_fVar “P(xsn) <=> P(Fst(xsn),Snd(xsn))”
in
val Cd_ind = prove_store("Cd_ind",
e0
(strip_tac >> rw[Cd_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !xs:mem(Pow(X)) n. IN(Pair(xs,n),P0) <=> P(xs,n)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> (* simply arw[] works for previous cases but not for this, since the pattern is different *)
 qby_tac ‘!xs n. P(xs,n) <=> IN(Pair(xs,n),s)’ 
 >-- (rpt strip_tac >> 
      first_x_assum (qspecl_then [‘Pair(xs',n')’] assume_tac) >>
      fs[Fst_of_Pair,Snd_of_Pair]) >>
 arw[])
(form_goal 
 “!X.(P(Empty(X),O) &
     (!xs n x:mem(X). 
      P(xs,n) & (~IN(x,xs)) ==> 
      P(Ins(x,xs),Suc(n)))) ==>
  !xs:mem(Pow(X)) n.Cd(xs,n) ==> P(xs,n)”))
end

val Cd_rules = prove_store("Cd_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[Cd_def] >> rpt strip_tac) >>
 rw[Cd_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> arw[] (*to eliminate the ~IN(x,xs) in the goal, previously did not have it*) >> 
 first_x_assum match_mp_tac >> arw[])
(form_goal
 “!X. Cd(Empty(X),O)& 
     (!xs:mem(Pow(X)) n x. Cd(xs,n) & ~(IN(x,xs)) ==> 
     Cd(Ins(x,xs),Suc(n)))”));

val Cd_rules_step = Cd_rules |> spec_all |> conjE2


val Cd_cases = prove_store("Cd_cases",
e0
(strip_tac >> strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!xs n. Cd(xs,n) ==> ((xs = Empty(X) & n = O) |
  (?xs0 n0 x0. ~(IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) &
  Cd(xs0,n0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (Cd_ind |> allE (rastt "X")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘Empty(X)’,‘O’,‘x’] >> 
     rw[Cd_rules] >> (*previously the rw [..._rules] solve the goal, but here require the condition not in empty*) 
     rw[Empty_property]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘xs'’,‘n'’,‘x’] >> rw[] >> arw[] >>
 match_mp_tac Cd_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[Cd_rules] >>
 arw[] >> match_mp_tac Cd_rules_step >> arw[])
(form_goal
 “!X xs:mem(Pow(X)) n. Cd(xs,n) <=> ((xs = Empty(X) & n = O) |
  (?xs0 n0 x0. ~(IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) &
   Cd(xs0,n0)))”));




val isL_def = define_pred 
“!A nas:mem(Pow(N * A)). isL(nas) <=>
(!P.IN(Empty(N * A),P) &
   (!nas0. IN(nas0,P) ==>
    !a.IN(Ins(Pair(CARD(nas0),a),nas0),P)) ==> 
 IN(nas,P))”

val isL_ind0 = 
    isL_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “isL(nas:mem(Pow(N * A)))”
            |> gen_all  
            |> disch_all 
            |> gen_all 


local 
val l = allE (rastt "Pow(N * A)") IN_def_P_expand
in
val isL_ind = prove_store("isL_ind",
e0
(strip_tac >> rw[isL_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !nas:mem(Pow(N * A)). IN(nas,P0) <=> P(nas)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “!A.(P(Empty(N * A)) &
   (!nas. P(nas) ==> !a:mem(A).P(Ins(Pair(CARD(nas),a),nas)))) ==>
  !nas:mem(Pow(N * A)).isL(nas) ==> P(nas)”))
end


val isL_rules = prove_store("isL_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[isL_def] >> rpt strip_tac) >>
 rw[isL_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “!A. isL(Empty(N * A))& 
     (!nas:mem(Pow(N * A)). isL(nas) ==> 
              !a. isL(Ins(Pair(CARD(nas),a),nas)))”));

val isL_rules_step = isL_rules |> spec_all |> conjE2



val isL_cases = prove_store("isL_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!nas. isL(nas) ==> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (isL_ind |> allE (rastt "A")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] (*figure out why the arw work here*)>> 
      qexistsl_tac [‘Empty(N * A)’,‘a’] >> 
      rw[isL_rules]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘nas'’,‘a’] >> rw[] >> arw[] >>
 match_mp_tac isL_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[isL_rules] >>
 arw[] >> match_mp_tac isL_rules_step >> arw[])
(form_goal
 “!A nas. isL(nas) <=> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))”));

(*5. uex_expand use rewr_rule, despite the fact that it is not in kernel, worrying about use it too much, any better way to expand uex?*)

fun uex_expand th = rewr_rule [uex_def $ concl th] th

(*6. to define new pred, the new pred can be parsed as a formula variable, and then turn its name into an actually predicate. cannot do the same thing for fsyms, since the new ones are not parsable. 

fair to use ex2fsym and axioms(*maybe the theory itself contains some function symbol, that is why I think axioms are plausible *) as the only two ways of define new funs?



*)


(*7. new dest_forall. if okay will edit dest_exists as it as well. but why it is slow?*)


(*AX5 working example, cannot have an elegant way to write this*)

val Eqv_def = define_pred
“!A B. Eqv(A,B) <=> ?f:A->B. isBij(f)”

(*member of pow as set*)

val Asset_def = define_pred
“!B bs:mem(Pow(B)) B0. Asset(bs,B0) <=> 
 !B1 i:B1->B. 
 isInj(i) & 
 (!b. (?b0:mem(B1). Eval(i,b0) = b) <=> IN(b,bs)) ==> 
 Eqv(B0,B1)”


val nPow_def = define_pred
“!B n Pn. nPow(B,n,Pn) <=> 
 ?C f:N->Pow(C). isFun(f) &
    (!C0. Asset(Eval(f,O),C0) ==> Eqv(C0,B)) &
    (!k Ck Csk. 
      Lt(k,n) &
      Asset(Eval(f,O),Ck) & Asset(Eval(f,O),Csk) ==>
      Eqv(Csk,Pow(Ck))) & 
    (!Cn. Asset(Eval(f,n),Cn) ==> Eqv(Cn,Pn))”

val AX5 = store_ax("AX5",
“!A.?B p:B->A Y M:B->Y.  
 (!b Mb.
     (?i:Mb->Y. Inj(i) & 
                !y. (?y0. Eval(i,y0) = y) <=> Holds(M,b,y))
     ==> P(Eval(p,b),Mb)) & 
 !a:mem(A) X. P(a,X) ==> ?b. Eval(p,b) = a”)


(* 9. tool for construct internal logic predicates, can give the term, but the proof that the term has the property is far from automatic.

my thoughts on this is to let it look at the term it constructs, and expand its definition according to theorem layer by layer, rather than do a big rw. But the term may split into smaller pieces, not sure how to do the code. 
*)


(* 10. ex2fsym into kernel*)




val lemma = fVar_Inst [("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "A"))],“~(a:mem(A) = a)”))] (AX1 |> qspecl [‘A’,‘A’])


val AX1 = new_ax
“!A B:set.?!R:A->B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)”;


fVar_Inst_f ("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "A"))],“~(a:mem(A) = a)”)) (concl $ (AX1 |> qspecl [‘A’,‘A’]))

val pair =  ("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "A"))],“~(a:mem(A) = a)”)) 

val(P,(argl,Q)) = pair

val f = (concl $ (AX1 |> qspecl [‘A’,‘A’]))

