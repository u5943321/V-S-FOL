fun fVar_Inst_th (pair as (P,(argl:(string * sort) list,Q))) th = 
    let val (ct,asl,w) = dest_thm th
        val asl' = List.map (form.fVar_Inst_f pair) asl
        val w' = form.fVar_Inst_f pair w
        val vs = bigunion (pair_compare String.compare sort_compare)
                          (List.map fvf (w' :: asl'))
        val newct = HOLset.union(ct,vs)
    in mk_thm (newct,asl',w')
    end


fun fVar_Inst [pair] th = fVar_Inst_th pair th





exception UNCHANGED
 fun total f x = SOME (f x) handle e => NONE

fun MAP f l = 
   let
     (* map2 is the version where something has changed *)
     fun map2 A [] = List.rev A
       | map2 A (h::t) = map2 ((f h handle e => h) :: A) t
     (* map1 is the version to call where nothing has changed yet *)
     fun map1 n [] = raise UNCHANGED
       | map1 n (h::t) = 
           case total f h of
             SOME fh => map2 (fh::(rev $ List.take(l,n))) t
           | NONE => map1 (n + 1) t
   in
     map1 0 l
   end





fun fVar_Inst_th (pair as (P,(argl:(string * sort) list,Q))) th = 
    let val (ct,asl,w) = dest_thm th
        val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q) argl
        val ct' = HOLset.union(ct,lcs)
        val aslw' = MAP (fVar_Inst_f pair) (w :: asl)
    in mk_thm (ct',tl aslw',hd aslw')
    end


(*fun fVar_Inst [pair] th = fVar_Inst_th pair th*)


fun ind_with th (ct,asl,w) = 
    let 
        val (P,args) = dest_fvar $ concl (strip_all_and_imp th)
        val (b,bvs) = strip_forall w
        val th1 = fVar_Inst_th (P,(bvs,b)) th
    in match_mp_tac th1 (ct,asl,w)
    end

val _ = new_pred "T" [];
val _ = new_pred "F" [];


val _ = new_sort "set" [];
val _ = new_sort "mem" [("A",mk_sort "set" [])];
val _ = new_sort "rel" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "rel" "~>";

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

fun flip_fconv eqs = 
(first_fconv (List.map (rewr_fconv o eq_sym) eqs))


fun uex_ex f = 
    let val th0 = iffLR $ uex_def f |> undisch
        val c0 = concl th0
        val ((n,s),b) = dest_exists c0
        val th1 = assume b |> conjE1 
        val th2 = existsI (n,s) (mk_var(n,s)) (concl th1) th1
        val th3 = existsE (n,s) th0 th2
    in disch f th3
    end

fun uex2ex_rule th = mp (uex_ex $concl th) th




fun uex_expand th = dimp_mp_l2r th (uex_def $concl th)

val uex_tac:tactic = fn (ct,asl,w) =>
    let val th = uex_def w
        val w' = snd $ dest_dimp $ concl th
    in ([(ct,asl,w')],(sing (dimp_mp_r2l th)))
    end


fun ex2fsym0 name args th = th |> eqT_intro |> iffRL |> ex2fsym name args
                               |> C mp (trueI [])



val flip_tac = 
(fconv_tac (basic_once_fconv no_conv (flip_fconv (!EqSorts))));

val lflip_tac =
fconv_tac 
 (land_fconv no_conv 
 $ basic_once_fconv no_conv (flip_fconv (!EqSorts)))


val rflip_tac =
fconv_tac 
 (rand_fconv no_conv 
 $ basic_once_fconv no_conv (flip_fconv (!EqSorts)))


val AX0 = new_ax “?A a:mem(A).T”;

val Fun_def = 
define_pred “!A B R:rel(A,B). isFun(R) <=> !x:mem(A). ?!y:mem(B). Holds(R,x,y)”;



val Fun_expand = proved_th $
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
“!A B R:A~>B. isFun(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2) ==> b1 = b2)”)

val EX1_mem = prove_store("EX1_mem",
e0
(strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (pop_assum (strip_assume_tac o uex_expand) >> 
     qexists_tac ‘x’ >> arw[]) >> 
 uex_tac >> qexists_tac ‘x’ >> arw[])
(form_goal
“!A. (?!x:mem(A). P(x)) <=> (?x:mem(A). P(x) & !x'. P(x') ==> x' = x)”));


(*
val EX1 = prove_store("EX1",
e0
(dimp_tac >> rpt strip_tac (* 2 *)
 >-- pop_assum (assume_tac o uex_expand))
“(?!x. P(x)) <=> (?x. P(x) & !x'. P(x') ==> x' = x)”


 ERR
     ("mk_eq.the sort: set does not have equality, attempting to make equality on",
      [set, set], [x', x], []) raised

reason of why do not use a thm for def of uex

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


fun ir_canon th =
  let
    val th1 = norm (gen_all th)
    val origl = ant th
    val gfvs = fvfl (concl th1 :: origl) 
    val newhyps = form_list_diff (ant th1)  origl
    val grouped = group_hyps gfvs newhyps
    val (cs, th2) = reconstitute' grouped th1
  in
    case cs of
        [] => gen_all th2
      | _ =>
        let
          val (th3,c) = conjl (rev cs) th2
        in
          disch c th3 |> gen_all
        end
  end

val irule = match_mp_tac o ir_canon

val Fun_expand_alt = prove_store("Fun_expand_alt",
e0
(rpt strip_tac >> rw[Fun_def] >>
 rw[fVar_Inst_th ("P",
 ([("b",mem_sort (mk_set "B"))],“Holds(R:A~>B,a,b)”)) (EX1_mem |> qspec ‘B’) |> qgen ‘a:mem(A)’])
(form_goal
 “!A B R:A~>B. isFun(R) <=>
  (!a.?b.Holds(R,a,b) & 
      !b'. Holds(R,a,b') ==> b' = b)”))

val Eval_def0 = Fun_expand_alt |> iffLR 
                               |> strip_all_and_imp
                               |> ex2fsym0 "Eval" ["R","a"]
                               |> qgen ‘a’
                               |> disch_all
                               |> gen_all

val Eval_def = prove_store("Eval_def",
e0
(rpt strip_tac >> drule Eval_def0 >>
 first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 dimp_tac >> strip_tac (*2 *)
 >-- (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal
 “!A B Fn:A ~> B. isFun(Fn) ==>!x y. Holds(Fn,x,y) <=> y = Eval(Fn,x)”));


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

val asF_def = rel2fun |> spec_all |> undisch
                      |> uex_expand |> ex2fsym0 "asF" ["R"]
                      |> disch_all |> gen_all
                      |> store_as "asF_def";

val asF_App = asF_def |> spec_all |> undisch |> conjE1
                      |> disch_all |> gen_all
                      |> store_as "asF_App";

val is_asF = asF_def |> spec_all |> undisch |> conjE2
                      |> disch_all |> gen_all
                      |> store_as "is_asF";


val Inj_def = define_pred
 “!A B R:rel(A,B). isInj(R) <=> isFun(R) & !x1:mem(A) x2:mem(A). Eval(R,x1) = Eval(R,x2) ==> x1 = x2”;
val Surj_def = define_pred “!A B R:rel(A,B). isSurj(R) <=> isFun(R) & !y:mem(B).?x:mem(A). Eval(R,x) = y”;
val Bij_def = define_pred “!A B R:A~>B. isBij(R) <=> isInj(R) & isSurj(R)”;

val INJ = define_pred 
“!A B f:A->B.INJ(f) <=> (!a1 a2. App(f,a1) = App(f,a2) ==> a1 = a2)”;


val SURJ = define_pred 
“!A B f:A->B.SURJ(f) <=> (!b. ?a. App(f,a) = b)”

val BIJ = define_pred
“!A B f:A->B.BIJ(f) <=> (INJ(f) & SURJ(f))”

val AX1 = new_ax
“!A B:set.?!R:A~>B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)”;

local
val l = fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
 “App(f1:A->B,a) = b”))] 
(AX1 |> qspecl [‘A’, ‘B’] |> uex_expand)
in
val fun_ext0 = prove_store("fun_ext0",
e0
(rpt strip_tac >> 
 strip_assume_tac l >> pop_assum (K all_tac) >>
 assume_tac rel2fun >>
 first_x_assum (qsspecl_then [‘R’] assume_tac) >>
 qby_tac ‘isFun(R)’ 
 >-- (rw[Fun_expand] >> arw[] >> 
     rpt strip_tac >-- (qexists_tac ‘App(f2,a)’ >> rw[]) >>
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum drule >> 
 pop_assum (strip_assume_tac o uex_expand) >>
 qsuff_tac ‘f1 = f & f2 = f’ >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
 >> (first_x_assum irule >> arw[]))
(form_goal
 “!A B f1:A->B f2. (!a. App(f1,a) = App(f2,a)) ==> f1 = f2”));
end


val fun_ext = prove_store("fun_ext",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 drule fun_ext0 >> arw[])
(form_goal
 “!A B f1:A->B f2. (!a. App(f1,a) = App(f2,a)) <=> f1 = f2”));




local
val l = fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
 “App(f:A->B,a) = b”))] 
(AX1 |> qspecl [‘A’, ‘B’] |> uex_expand)
in
val asR_ex = prove_store("asR_ex",
e0
(rpt strip_tac >> strip_assume_tac l >>
 qexists_tac ‘R’ >> arw[])
(form_goal
 “!A B f:A->B.?R.!a b. Holds(R,a,b) <=> App(f,a) = b”));
end


val asR_def = asR_ex |> spec_all |> ex2fsym0 "asR" ["f"]
                     |> gen_all


val asR_Fun = prove_store("asR_Fun",
e0
(rpt strip_tac >> rw[Fun_expand] >>
 rw[asR_def] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘App(f,a)’ >> rw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B. isFun(asR(f))”));



val _ = new_fun "@" (rel_sort (mk_set "A") (mk_set "C"),
                     [("phi",rel_sort (mk_set "B") (mk_set "C")),
                      ("psi",rel_sort (mk_set "A") (mk_set "B"))])


val oR_def = new_ax 
“!A B phi:A~>B C psi:B~>C a:mem(A) c:mem(C). 
(?b. Holds(phi,a,b) & Holds(psi,b,c)) <=> Holds(psi @ phi,a,c)”

val _ = new_fun "id" (rel_sort (mk_set "A") (mk_set "A"),
                     [("A",set_sort)])

val id_def = new_ax “!A a:mem(A) b. Holds(id(A),a,b) <=> a = b”;


val id_Fun = prove_store("id_Fun",
e0
(strip_tac >> rw[Fun_expand,id_def] >> flip_tac >> rpt strip_tac >>
 arw[] >> qexists_tac ‘a’ >> rw[])
(form_goal
 “!A. isFun(id(A))”));


local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
“Holds(R1:A~>B,a,b)”))] 
(AX1 |> qspecl [‘A’,‘B’]) |> uex_expand
in
val R_EXT = prove_store("R_EXT",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 strip_assume_tac l >>
 qsuff_tac ‘R1 = R & R2= R’ >-- (strip_tac >> arw[]) >> 
 strip_tac >> first_x_assum irule >> arw[]
 )
(form_goal
“!A B R1:A~>B R2. R1 = R2 <=> !a b.Holds(R1,a,b) <=> Holds(R2,a,b)”));
end


val FUN_EXT = prove_store("FUN_EXT",
e0
(rpt strip_tac >> drule Eval_def >> 
 rev_drule Eval_def >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (drule $ iffLR R_EXT >>
      first_x_assum (qspecl_then [‘a’,‘Eval(f2,a)’] assume_tac) >>
      rev_full_simp_tac[]) >>
 irule $ iffRL R_EXT >> rpt strip_tac >>
 arw[])
(form_goal “!A B f1:A~>B f2. isFun(f1) & isFun(f2) ==>
 (f1 = f2 <=> (!a.Eval(f1,a) = Eval(f2,a)))”));


val idL = prove_store("idL",
e0
(rpt strip_tac >> irule $ iffRL R_EXT >> 
 rw[GSYM oR_def,id_def] >> rpt strip_tac >> dimp_tac >> strip_tac
 >-- fs[] >> qexists_tac ‘b’ >> arw[])
(form_goal
 “!A B f:A~>B. id(B) @ f = f”));


val idR = prove_store("idR",
e0
(rpt strip_tac >> irule $ iffRL R_EXT >> 
 rw[GSYM oR_def,id_def] >> rpt strip_tac >> dimp_tac >> strip_tac
 >-- fs[] >> qexists_tac ‘a’ >> arw[])
(form_goal
 “!A B f:A~>B. f @ id(A) = f”));

val Eval_id = prove_store("Eval_id",
e0
(rpt strip_tac >> qspecl_then [‘A’] assume_tac id_Fun >>
 drule $ GSYM Eval_def >> flip_tac >> arw[] >> rw[id_def])
(form_goal
 “!A a.Eval(id(A),a) = a”));



val Thm_2_7_oR_Fun = proved_th $
e0
(rpt strip_tac >> fs[Fun_expand,GSYM oR_def] >> rpt strip_tac (* 2 *)
 >-- (last_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
      last_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
      qexistsl_tac [‘b'’,‘b’] >> arw[]) >>
 first_x_assum irule >> 
 qby_tac ‘b' = b’ >--
 (first_x_assum irule >> qexistsl_tac [‘a’] >> arw[]) >>
 fs[] >> qexists_tac ‘b’ >> arw[])
(form_goal
 “!A B f:A~>B C g:B~>C. isFun(f) & isFun(g) ==> isFun(g @ f)”)

val oR_Fun = Thm_2_7_oR_Fun |> store_as "oR_Fun"

val o_ex = prove_store("o_ex",
e0
(rpt strip_tac >>
 qexists_tac ‘asF(asR(psi) @ asR(phi))’ >> 
 qsspecl_then [‘psi’] assume_tac asR_Fun >>
 qsspecl_then [‘phi’] assume_tac asR_Fun >>
 qby_tac ‘isFun(asR(psi) @ asR(phi))’ 
 >-- (irule oR_Fun >> arw[]) >>
 drule asF_App >> arw[])
(form_goal
 “!A B phi:A->B C psi:B->C. ?f:A->C. 
 !a c. App(f,a) = c <=> Holds(asR(psi) @ asR(phi),a,c)”));

val o_def = o_ex |> spec_all |> ex2fsym0 "o" ["psi","phi"]
                 |> gen_all |> store_as "o_def";

val o_App = prove_store("o_App",
e0
(rpt strip_tac >> flip_tac >> rw[o_def] >>
 rw[GSYM oR_def] >>
 qexists_tac ‘App(f,a)’ >> rw[asR_def])
(form_goal
 “!A B f:A->B C g:B->C a. App(g,(App(f,a))) = App(g o f,a)”));


val asR_oR = prove_store("asR_oR",
e0
(rpt strip_tac >> irule $ iffRL R_EXT >> rpt strip_tac >>
 rw[asR_def] >> rw[o_def])
(form_goal
 “!A B f:A->B C g:B-> C. asR(g) @ asR(f) = asR(g o f)”));


val asR_asF = prove_store("asR_asF",
e0
(rpt strip_tac >> irule $ iffRL R_EXT >>
 rw[asR_def] >> drule asF_App >> arw[])
(form_goal
 “!A B f:A~>B. isFun(f) ==> asR(asF(f)) =f”));


local
val l = fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
 “App(f1:A->B,a) = b”))] 
(AX1 |> qspecl [‘A’, ‘B’] |> uex_expand)
in
val fun_ext0 = prove_store("fun_ext0",
e0
(rpt strip_tac >> 
 strip_assume_tac l >> pop_assum (K all_tac) >>
 assume_tac rel2fun >>
 first_x_assum (qsspecl_then [‘R’] assume_tac) >>
 qby_tac ‘isFun(R)’ 
 >-- (rw[Fun_expand] >> arw[] >> 
     rpt strip_tac >-- (qexists_tac ‘App(f2,a)’ >> rw[]) >>
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum drule >> 
 pop_assum (strip_assume_tac o uex_expand) >>
 qsuff_tac ‘f1 = f & f2 = f’ >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
 >> (first_x_assum irule >> arw[]))
(form_goal
 “!A B f1:A->B f2. (!a. App(f1,a) = App(f2,a)) ==> f1 = f2”));
end



val fun_ext = prove_store("fun_ext",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 drule fun_ext0 >> arw[])
(form_goal
 “!A B f1:A->B f2. (!a. App(f1,a) = App(f2,a)) <=> f1 = f2”));


val asF_o = prove_store("asF_o",
e0
(rpt strip_tac >> irule fun_ext0 >> strip_tac >>
 rw[o_def] >>
 drule asR_asF >> rev_drule asR_asF >> arw[] >>
 qby_tac ‘isFun(g @ f)’ >-- (irule oR_Fun >> arw[]) >>
 drule Eval_def >> arw[] >> drule asF_App >> arw[])
(form_goal
 “!A B f:A~>B C g:B ~> C. 
  isFun(f) & isFun(g) ==>
  asF(g) o asF(f) = asF(g @ f)”));


val Holds_Eval = proved_th $
e0
(rpt strip_tac >> drule Eval_def >>
 first_x_assum (qspecl_then [‘a’,‘Eval(f,a)’] assume_tac) >> fs[])
(form_goal
“!A B f:A~>B. isFun(f) ==> !a.Holds(f,a,Eval(f,a))”)


val Eval_asR = prove_store("Eval_asR",
e0
(rpt strip_tac >> flip_tac >> rw[GSYM asR_def] >>
 qsspecl_then [‘f’] assume_tac asR_Fun >>
 drule Holds_Eval >> arw[])
(form_goal
 “!A B f:A->B a. Eval(asR(f),a) = App(f,a)”));



val asF_asR = prove_store("asF_asR",
e0
(rpt strip_tac >> irule fun_ext0 >> 
 qsspecl_then [‘f’] assume_tac asR_Fun >>
 strip_tac >> drule asF_App >> arw[] >>
 rw[asR_def])
(form_goal
 “!A B f:A->B. asF(asR(f)) =f”));


val asR_eq_eq = prove_store("asR_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 once_rw[GSYM asF_asR] >> arw[])
(form_goal
 “!A B f:A->B g. asR(f) = asR(g) <=> f = g”));



val App_asF_Eval = prove_store("App_asF_Eval",
e0
(rpt strip_tac >> drule asF_def >> arw[] >>
 drule Holds_Eval >> arw[])
(form_goal
 “!A B f:A~>B. isFun(f) ==> !a.App(asF(f), a) = Eval(f,a)”));


val App_Eval_asR = prove_store("App_Eval_asR",
e0
(rpt strip_tac >> rw[GSYM asR_def] >> irule Holds_Eval >>
 rw[asR_Fun])
(form_goal
 “!A B f:A->B. !a.App(f, a) = Eval(asR(f),a)”));


val Thm_2_7_assoc = prove_store("Thm_2_7_assoc",
e0
(rpt strip_tac >> rw[R_EXT,GSYM oR_def] >> rpt strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘b''’ >> arw[] >> qexists_tac ‘b'’ >> arw[]) >>
 qexists_tac ‘b''’ >> arw[] >> qexists_tac ‘b'’ >> arw[])
(form_goal
“!A B phi:A~>B C psi:B~>C D chi:C~>D. (chi @ psi) @ phi =
 chi @ psi @ phi”));


val Thm_2_7_id = proved_th $
e0
(rpt strip_tac >> rw[R_EXT] >> rpt strip_tac  (* 2 *)
 >-- (rw[GSYM oR_def,id_def] >> dimp_tac >> rpt strip_tac
      >-- arw[] >> qexists_tac ‘a’ >> arw[]) >>
 rw[GSYM oR_def,id_def] >> dimp_tac >> rpt strip_tac 
 >-- fs[] >> qexists_tac ‘b’ >> arw[])
(form_goal
“!A B phi:A~>B. phi @ id(A) = phi & id(B) @ phi = phi”)

val _ = new_fun "op" (rel_sort (mk_set "B") (mk_set "A"),[("R",rel_sort (mk_set "A") (mk_set "B"))])

val op_def = new_ax “!A B R:A~>B a b.Holds(op(R),a,b) <=> Holds(R,b,a)”;



val Inj_R_expand = proved_th $
e0
(rpt strip_tac >> rw[Inj_def,Fun_expand] >> dimp_tac >> strip_tac (* 2 *)
 >-- (arw[] >> rpt strip_tac (* 3  2T*) >>
      first_x_assum irule >> 
      qby_tac ‘isFun(R)’ 
      >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac) >>
      drule Eval_def >> fs[]) >>
 arw[] >> rpt strip_tac (* 3  2 T*) >>
 first_x_assum irule >> qexists_tac ‘Eval(R,x1)’ >> 
 qby_tac ‘isFun(R)’ 
      >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac) >>
 drule Eval_def >> arw[])
(form_goal
“!A B R:A~>B. isInj(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2)==> b1 = b2) &
 (!a1 a2 b. Holds(R,a1,b) & Holds(R,a2,b) ==> a1 = a2)”)

val Surj_R_expand = proved_th $
e0
(rpt strip_tac >> rw[Surj_def,Fun_expand] >> dimp_tac >> strip_tac (* 2 *)
 >-- (arw[] >> rpt strip_tac >>
      qby_tac ‘isFun(R)’ 
      >-- (rw[Fun_expand] >> arw[]) >>
      drule Eval_def >> arw[] >> 
      fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
      arw[]) >>
 arw[] >>
 qby_tac ‘isFun(R)’ 
 >-- (rw[Fun_expand] >> arw[]) >>
 rpt strip_tac >>
 drule Eval_def >> fs[] >> 
 fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
 arw[])
(form_goal
 “!A B R:A~>B. isSurj(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2)==> b1 = b2) &
 (!b. ?a.Holds(R,a,b))”)

val Bij_R_expand = proved_th $
e0
(rpt strip_tac >> rw[Bij_def,Inj_R_expand,Surj_R_expand] >>
 rpt strip_tac >> dimp_tac >-- (rpt strip_tac >>
 arw[]
 >-- (first_x_assum irule >> qexists_tac ‘a’ >> arw[]) >>
 first_x_assum irule >> qexists_tac ‘b’ >> arw[]) >>
 rpt strip_tac >> arw[] (* 3 *)
 >-- (first_x_assum irule >> qexists_tac ‘a’ >> arw[])
 >-- (first_x_assum irule >> arw[] >> qexists_tac ‘b’ >> arw[]) >>
 first_x_assum irule >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!A B R:A~>B. isBij(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2)==> b1 = b2) &
 (!a1 a2 b. Holds(R,a1,b) & Holds(R,a2,b) ==> a1 = a2) &
 (!b. ?a.Holds(R,a,b)) ”)



val Bij_op_inv = proved_th $
e0
(rpt strip_tac >> rw[Bij_R_expand,id_def,R_EXT] >> dimp_tac >> strip_tac
  (* 2 *)
 >-- (rw[op_def,GSYM oR_def] >> rpt strip_tac 
      (* 2 *)
      >-- (dimp_tac >> strip_tac (* 2 *)
           >-- (first_x_assum irule >> qexists_tac ‘b'’ >> arw[]) >>
           arw[] >> last_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
           qexists_tac ‘b'’ >> arw[]) >>
      dimp_tac >> strip_tac (* 2 *)
      >-- (first_x_assum irule >> qexists_tac ‘b'’ >> arw[]) >>
      arw[] >> first_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
      qexists_tac ‘a'’ >> arw[]) >>
 fs[GSYM oR_def] >>
 qby_tac ‘!a b. Holds(phi,a,b) <=> Holds(op(phi),b,a)’ >--
 (rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
  >-- (first_x_assum (qspecl_then [‘a’,‘a’] assume_tac) >> fs[] >>
      qsuff_tac ‘b = b'’ >-- (strip_tac >> arw[]) >>
      first_x_assum (qspecl_then [‘b'’,‘b’] (assume_tac o GSYM)) >>
      fconv_tac (rewr_fconv (eq_sym "mem")) >> arw[] >>
      qexists_tac ‘a’ >> arw[]) >>
  first_x_assum (qspecl_then [‘b’,‘b’] assume_tac) >> fs[] >>
  qsuff_tac ‘a = b'’ >-- (strip_tac >> arw[]) >>
  first_x_assum (qspecl_then [‘b'’,‘a’] (assume_tac o GSYM)) >>
  fconv_tac (rewr_fconv (eq_sym "mem")) >> arw[] >>
  qexists_tac ‘b’ >> arw[])
 >> rpt strip_tac (* 4 *)
 >-- (first_x_assum (qspecl_then [‘a’,‘a’] assume_tac) >> fs[] >>
     qexists_tac ‘b’ >> arw[])
 >-- (fs[] >> rev_full_simp_tac[] >> 
     first_x_assum (qspecl_then [‘b1’,‘b2’] (assume_tac o GSYM)) >> 
     arw[] >> qexists_tac ‘a’ >> arw[]) 
 >-- (fs[] >> rev_full_simp_tac[] >> 
     first_x_assum (qspecl_then [‘a1’,‘a2’] (assume_tac o GSYM)) >> 
     arw[] >> qexists_tac ‘b’ >> arw[])
 >-- (first_x_assum (qspecl_then [‘b’,‘b’] assume_tac) >> fs[] >>
     qexists_tac ‘b'’ >> arw[])
 )
(form_goal
 “!A B phi:A~>B.isBij(phi) <=> op(phi) @ phi = id(A) & phi @ op(phi) = id(B)”)

val Thm_2_7_bij = proved_th $
e0
(rpt strip_tac >> rw[Bij_R_expand,id_def,R_EXT] >> dimp_tac >> strip_tac
  (* 2 *)
 >-- (qexists_tac ‘op(phi)’ >> rw[op_def,GSYM oR_def] >> rpt strip_tac 
      (* 2 *)
      >-- (dimp_tac >> strip_tac (* 2 *)
           >-- (first_x_assum irule >> qexists_tac ‘b'’ >> arw[]) >>
           arw[] >> last_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
           qexists_tac ‘b'’ >> arw[]) >>
      dimp_tac >> strip_tac (* 2 *)
      >-- (first_x_assum irule >> qexists_tac ‘b'’ >> arw[]) >>
      arw[] >> first_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
      qexists_tac ‘a'’ >> arw[]) >>
 fs[GSYM oR_def] >>
 qby_tac ‘!a b. Holds(phi,a,b) <=> Holds(psi,b,a)’ >--
 (rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
  >-- (first_x_assum (qspecl_then [‘a’,‘a’] assume_tac) >> fs[] >>
      qsuff_tac ‘b = b'’ >-- (strip_tac >> arw[]) >>
      first_x_assum (qspecl_then [‘b'’,‘b’] (assume_tac o GSYM)) >>
      fconv_tac (rewr_fconv (eq_sym "mem")) >> arw[] >>
      qexists_tac ‘a’ >> arw[]) >>
  first_x_assum (qspecl_then [‘b’,‘b’] assume_tac) >> fs[] >>
  qsuff_tac ‘a = b'’ >-- (strip_tac >> arw[]) >>
  first_x_assum (qspecl_then [‘b'’,‘a’] (assume_tac o GSYM)) >>
  fconv_tac (rewr_fconv (eq_sym "mem")) >> arw[] >>
  qexists_tac ‘b’ >> arw[])
 >> rpt strip_tac (* 4 *)
 >-- (first_x_assum (qspecl_then [‘a’,‘a’] assume_tac) >> fs[] >>
     qexists_tac ‘b’ >> arw[])
 >-- (fs[] >> rev_full_simp_tac[] >> 
     first_x_assum (qspecl_then [‘b1’,‘b2’] (assume_tac o GSYM)) >> 
     arw[] >> qexists_tac ‘a’ >> arw[]) 
 >-- (fs[] >> rev_full_simp_tac[] >> 
     first_x_assum (qspecl_then [‘a1’,‘a2’] (assume_tac o GSYM)) >> 
     arw[] >> qexists_tac ‘b’ >> arw[])
 >-- (first_x_assum (qspecl_then [‘b’,‘b’] assume_tac) >> fs[] >>
     qexists_tac ‘b'’ >> arw[])
 )
(form_goal
 “!A B phi:A~>B.isBij(phi) <=> ?psi:B~>A. psi @ phi = id(A) & phi @ psi = id(B)”)

val I_ex = prove_store("I_ex",
e0
(strip_tac >> qexists_tac ‘asF(id(A))’ >> rw[])
(form_goal
 “!A. ?i:A->A. i = asF(id(A))”));

val I_def = I_ex |> spec_all |> ex2fsym0 "I" ["A"]
                 |> gen_all |> store_as "I_def";

val I_R = prove_store("I_R",
e0
(rw[I_def] >> rpt strip_tac >>
 qby_tac ‘f = asF(asR(f))’ >-- rw[asF_asR] >>
 once_arw[] >> 
 qsuff_tac ‘asF(asR(f)) o asF(id(A)) = asF(asR(f) @ id(A))’ 
 >-- rw[idR] >>
 irule asF_o >> rw[asR_Fun,id_Fun])
(form_goal
 “!A B f:A->B. f o I(A) = f”));


val I_L = prove_store("I_L",
e0
(rw[I_def] >> rpt strip_tac >>
 qby_tac ‘f = asF(asR(f))’ >-- rw[asF_asR] >>
 once_arw[] >> 
 qsuff_tac ‘asF(id(B)) o asF(asR(f)) = asF(id(B) @ asR(f))’ 
 >-- rw[idL] >>
 irule asF_o >> rw[asR_Fun,id_Fun])
(form_goal
 “!A B f:A->B. I(B) o f = f”));

val App_I = prove_store("App_I",
e0
(rw[I_def] >> rpt strip_tac >>
 qspecl_then [‘A’] assume_tac id_Fun >> 
 drule App_asF_Eval >> arw[Eval_id])
(form_goal
 “!A a. App(I(A),a) = a”));


val rfs =  rev_full_simp_tac;

val INJ_asR = prove_store("INJ_asR",
e0
(rpt strip_tac >> rw[INJ] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[Inj_def,asR_Fun] >> fs[App_Eval_asR]) >>
 fs[Inj_def,GSYM App_Eval_asR] >> first_x_assum drule >>
 arw[])
(form_goal
 “!A B f:A->B. INJ(f) <=> isInj(asR(f))”));


val SURJ_asR = prove_store("SURJ_asR",
e0
(rpt strip_tac >> rw[SURJ] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[Surj_def,asR_Fun] >> fs[App_Eval_asR]) >>
 fs[Surj_def,GSYM App_Eval_asR])
(form_goal
 “!A B f:A->B. SURJ(f) <=> isSurj(asR(f))”));


val BIJ_asR = prove_store("BIJ_asR",
e0
(rw[BIJ,INJ_asR,SURJ_asR,Bij_def])
(form_goal
 “!A B f:A->B. BIJ(f) <=> isBij(asR(f))”));







val Bij_op_Fun = prove_store("Bij_op_Fun",
e0
(rw[Bij_def,op_def,Inj_def,Surj_def] >> rpt strip_tac >>
 drule Eval_def >> rw[Fun_expand,op_def] >> rpt strip_tac
 (* 2 *) 
 >-- (arw[] >> flip_tac >> arw[]) >>
 rfs[] >> first_x_assum irule >> arw[])
(form_goal
 “!A B f:A~>B. isBij(f) ==> isFun(op(f))”));

val BIJ_INV_ex = prove_store("BIJ_INV_ex",
e0
(rpt gen_tac >> strip_tac >> rw[I_def] >>
 qsuff_tac ‘asF(asR(f)) o asF(op(asR(f))) = asF(id(B)) &
            asF(op(asR(f))) o asF(asR(f)) = asF(id(A))’
 >-- rw[asF_asR] >>
 fs[BIJ_asR] >> drule $ iffLR Bij_op_inv >>
 drule Bij_op_Fun >> 
 qsuff_tac
 ‘asF(asR(f)) o asF(op(asR(f))) = asF(asR(f) @ op(asR(f))) &
  asF(op(asR(f))) o asF(asR(f)) = asF(op(asR(f)) @ asR(f))’
 >-- arw[] >>
 strip_tac >> irule asF_o >> arw[asR_Fun])
(form_goal
 “!A B f:A->B. BIJ(f) ==> f o asF(op(asR(f))) = I(B) & asF(op(asR(f))) o f = I(A)”));



val Tab_def = define_pred
“!A B R TR p:TR~>A q:TR~>B.isTab(R,p,q) <=> 
 isFun(p) & isFun(q) & (!x y. Holds(R,x,y) <=> ?r. Eval(p,r) = x & Eval(q,r) = y) & !r s. Eval(p,r) = Eval(p,s) & Eval(q,r) = Eval(q,s) ==> r = s”;



val AX1 = new_ax
“!A B:set.?!R:A~>B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)”;

val AX2 = new_ax “!A B R:A~>B.?TR p:TR~>A q:TR~>B. isFun(p) & isFun(q) & (!x y. Holds(R,x,y) <=> ?r. Eval(p,r) = x & Eval(q,r) = y) & !r s. Eval(p,r) = Eval(p,s) & Eval(q,r) = Eval(q,s) ==> r = s”;


local
val lemma = fVar_Inst [("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "A"))],“~(a:mem(A) = a)”))] (AX1 |> qspecl [‘A’,‘A’])
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma)
in
val Thm_2_2 = prove_store("Thm_2_2",
e0
(strip_assume_tac AX0 >> strip_assume_tac lemma' >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 >>
 qexists_tac ‘TR’ >> strip_tac >>
 by_tac “!a b. ~Holds(R:A~>A,a:mem(A),b:mem(A))”
 >-- (rpt strip_tac >> pop_assum (K all_tac) >> pop_assum (K all_tac) >>
      once_arw[] >> ccontra_tac >> fs[]) >>
 suffices_tac “Holds(R:A~>A,Eval(p:TR~>A,a'),Eval(q:TR~>A,a':mem(TR)))”
 >-- arw[] >>
 pop_assum (K all_tac) >> arw[] >> qexists_tac ‘a'’ >> rw[])
(form_goal
“?Empty. !a:mem(Empty).F”));
end


local
val lemma = fVar_Inst [("P",([("y",mem_sort (mk_set "A")),("z",mem_sort (mk_set "A"))],“y = a0:mem(A) & z = a0”))] (AX1 |> qspecl [‘A’,‘A’])
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma)
in
val Thm_2_3 = prove_store("Thm_2_3",
e0
(x_choosel_then ["A","a0"] assume_tac AX0 >>
 strip_assume_tac lemma' >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 >>
 qby_tac ‘Holds(R,a0,a0)’ >--
 (pop_assum (K all_tac) >> pop_assum (K all_tac) >> arw[]) >>
 pop_assum mp_tac >> once_arw[] >> strip_tac  >>
 qexistsl_tac [‘TR’,‘r’] >>
 strip_tac >> first_x_assum irule >> arw[] >>
 first_x_assum $ (irule o iffLR) >> arw[] >>
 qexists_tac ‘x'’ >> rw[])
(form_goal
“?ONE x:mem(ONE). !x':mem(ONE). x' = x”));
end



val ONE_def = Thm_2_3 |> eqT_intro |> iffRL |> ex2fsym "1" []
                      |> C mp (trueI []) |> gen_all
                      |> store_as "ONE_def";

val dot_def = ONE_def |> eqT_intro |> iffRL |> ex2fsym "dot" []
                      |> C mp (trueI []) |> gen_all
                      |> store_as "dot_def";

val ONE = mk_fun "1" [];

val dot = mk_fun "dot" [];

local
val lemma =
(fVar_Inst [("P",([("a",mem_sort (mk_set "A")),("b",mem_sort ONE)],“a = a:mem(A)”))] (AX1 |> qspecl [‘A’,‘1’]))
val lemma' = uex_expand lemma
in
val Thm_2_3_5 = proved_th $
e0
(strip_tac >> rw[uex_def “?!f:A~>1.isFun(f)”,R_EXT] >>
 strip_assume_tac lemma' >> qexists_tac ‘R’ >> rw[Fun_def] >> strip_tac (* 2 *)
 >-- (strip_tac >> rw[uex_def “?!y:mem(1).Holds(R,x,y)”] >>
      qexists_tac ‘dot’ >> once_rw[dot_def] >>
      arw[] >> strip_tac >> rw[]) >>
 strip_tac >> strip_tac >> rw[GSYM R_EXT] >> first_x_assum irule >>
 strip_tac >> first_x_assum (qspecl_then [‘a’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 pop_assum (K all_tac) >> pop_assum mp_tac >> once_rw[dot_def] >>
 rpt strip_tac >> arw[])
(form_goal
“!A.?!f:A~>1. isFun(f)”);
end

val Thm_2_3_5_expand =
    Thm_2_3_5 |> spec_all |> uex_expand |> gen_all
              |> store_as "Thm_2_3_5_expand";

val To1_def =
    Thm_2_3_5_expand
        |> spec_all |> eqT_intro |> iffRL
        |> ex2fsym "To1" ["A"]
        |> C mp (trueI []) |> gen_all
        |> store_as "To1_def";



val Thm_2_4_R_ver = prove_store("Thm_2_4_R_ver",
e0
(rpt strip_tac >> qspecl_then [‘1’,‘A’,‘R’] strip_assume_tac AX2 >>
 qexistsl_tac [‘TR’,‘q’] >>
 once_arw[] >> strip_tac (* 2 *)
 >-- (rw[Inj_def] >> arw[] >> rpt strip_tac >>
        first_x_assum irule >>
        arw[] >> once_rw[dot_def] >> rw[]) >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘r’ >> arw[]) >>
 qexists_tac ‘b’ >> arw[] >> once_rw[dot_def] >> rw[])
(form_goal
“!A R:1 ~> A.?B i:B~>A. isInj(i) & !a:mem(A).Holds(R,dot,a) <=> ?b. a = Eval(i,b)”));


local
val l0 = (fVar_Inst [("P",([("a",mem_sort ONE),("b",mem_sort (mk_set "A"))],“a = a:mem(1) & P(b:mem(A))”))] (AX1 |> qspecl [‘1’,‘A’])) |> gen_all
val uth = uex_def “?!R:1~>A. !a. Holds(R, dot, a) <=> P(a)”
in
val Rel_Pred1 = prove_store("Rel_Pred1",
e0
(assume_tac l0 >> strip_tac >>
 first_x_assum (qspecl_then [‘A’] assume_tac) >>
 first_assum (fn th => assume_tac (uex_def $ concl th)) >> fs[] >>
 rw[uth] >> qexists_tac ‘R’ >> once_arw[] >> rw[] >>
 rpt strip_tac >> first_x_assum irule >> once_rw[dot_def] >> arw[] >>
 rpt strip_tac >> rw[])
(form_goal
“!A. ?!R:1~>A.!a:mem(A). Holds(R,dot,a) <=> P(a)”));
end




local
val lemma = mp (uex_ex (concl $ spec_all Rel_Pred1)) (spec_all Rel_Pred1)
in
val Thm_2_4 = prove_store("Thm_2_4",
e0
(assume_tac Thm_2_4_R_ver >> strip_tac >>
 strip_assume_tac lemma >>
 first_x_assum (qspecl_then [‘A’,‘R’] strip_assume_tac) >>
 qexistsl_tac [‘B’,‘i’] >> fs[])
(form_goal
“!A.?B i:B~>A. isInj(i) & !a:mem(A).P(a) <=> ?b. a = Eval(i,b)”));
end



local
val lemma = mp (uex_ex (concl $ spec_all Rel_Pred1)) (spec_all Rel_Pred1)
in
val SPECI_THM = prove_store("SPECI_THM",
e0
(strip_tac >> qspecl_then [‘A’] strip_assume_tac Thm_2_4 >>
 qexistsl_tac [‘B’,‘asF(i)’] >> fs[App_Eval_asR] >>
 drule $ iffLR Inj_def >> fs[] >>
 drule asR_asF >> arw[] >> fs[INJ_asR])
(form_goal
“!A.?B i:B->A. INJ(i) & !a:mem(A).P(a) <=> ?b. a = App(i,b)”));
end


val Tab_Fun = prove_store("Tab_Fun",
e0
(rpt strip_tac >> fs[Tab_def])
(form_goal
“!A B R:A~>B TR p:TR~>A q:TR~>B.isTab(R,p,q) ==>
 isFun(p) & isFun(q)”));

val Tab_Eval_Rel = prove_store("Tab_Eval_Rel",
e0
(rpt strip_tac >> fs[Tab_def] >>
 qexists_tac ‘r’ >> arw[])
(form_goal
“!A B R:A~>B TR p:TR~>A q:TR~>B.isTab(R,p,q) ==>
 (!r x y. Eval(p,r) = x & Eval(q,r) = y ==> Holds(R,x,y))”));


val Tab_mem_R = prove_store("prove_store",
e0
(rpt strip_tac >> fs[Tab_def] >>
 qexists_tac ‘r’ >> rw[])
(form_goal
 “!A B R:A~>B TR p q. isTab(R,p:TR~>A,q) ==> !r:mem(TR). Holds(R,Eval(p,r),Eval(q,r))”));

val Tab_prop1 = prove_store("Tab_prop1",
e0
(rpt strip_tac >> fs[Tab_def])
(form_goal
“!A B R:A~>B TR p:TR~>A q:TR~>B.
 isTab(R,p,q) ==>
 (!x y. Holds(R,x,y) <=> ?r:mem(TR).Eval(p,r) = x & Eval(q,r) = y)”));


val Tab_prop2 = prove_store("Tab_prop2",
e0
(rpt strip_tac >> fs[Tab_def] >> first_x_assum irule >> arw[])
(form_goal
“!A B R:A~>B TR p:TR~>A q:TR~>B.
 isTab(R,p,q) ==>
 (!r s. Eval(p,r) = Eval(p,s) & Eval(q,r) = Eval(q,s) ==> r = s)”));


local
val lemma = fVar_Inst [("P",([("a",mem_sort (mk_set "T1")),("b",mem_sort (mk_set "T2"))],“Eval(p1:T1~>A,a) = Eval(p2:T2~>A,b) & Eval(q1:T1~>B,a) = Eval(q2:T2~>B,b)”))] (AX1 |> qspecl [‘T1’,‘T2’])
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma)
in
val Thm_2_5 = prove_store("Thm_2_5",
e0
(rpt strip_tac >> x_choose_then "B0" strip_assume_tac lemma' >>
 qexists_tac ‘B0’ >> rw[Bij_def] >>
 qby_tac ‘isFun(B0)’ >--
 (rw[Fun_def] >> strip_tac >>
  rw[uex_def “?!y:mem(T2).Holds(B0:T1~>T2,x,y)”] >>
  arw[] >> rev_drule Tab_mem_R >>
  first_x_assum (qspecl_then [‘x’] assume_tac) >>
  drule Tab_prop1 >> fs[] >>
  qexists_tac ‘r’ >> arw[] >> drule Tab_prop2 >>
  rpt strip_tac >> first_x_assum irule >> arw[]) >>
 rw[Inj_def,Surj_def] >> arw[] >> strip_tac (* 2 *)
 >-- (rev_drule Tab_prop2 >> rpt strip_tac >> first_x_assum irule >>
      drule Eval_def >>
      first_assum (qspecl_then [‘x1’,‘Eval(B0,x1)’] assume_tac) >>
      first_x_assum (qspecl_then [‘x2’,‘Eval(B0,x2)’] assume_tac) >>
      first_assum (qspecl_then [‘x1’,‘Eval(B0,x1)’] assume_tac) >>
      first_assum (qspecl_then [‘x2’,‘Eval(B0,x2)’] assume_tac) >>
      fs[]) >>
 (*Surj*)
 strip_tac >>
 fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
 drule $ GSYM Eval_def >> arw[] >>
 drule Tab_mem_R >> first_x_assum (qspecl_then [‘y’] assume_tac) >>
 rev_drule Tab_prop1 >> fs[] >>
 qexists_tac ‘r’ >> arw[])
(form_goal
“!A B R:A~>B T1 p1:T1~>A q1:T1~>B T2 p2:T2~>A q2:T2~>B.isTab(R,p1,q1) & isTab(R,p2,q2) ==> ?b:T1 ~>T2.isBij(b)”));
end


local
val lemma = fVar_Inst [("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],“T”))] (AX1 |> qspecl [‘A’,‘B’])
in
val T_uex = dimp_mp_l2r lemma (uex_def $ concl lemma) |> rewr_rule []
                        |> gen_all
end

val T_ex = proved_th $
e0
(assume_tac T_uex >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘A’,‘B’] strip_assume_tac) >>
 qexists_tac ‘R’ >> arw[] >> rpt strip_tac >> rw[])
(form_goal
“!A B. ?T0:A~>B. !a b. Holds(T0,a,b)”)

val Cross_ex = proved_th $
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] strip_assume_tac T_ex >>
 qspecl_then [‘A’,‘B’,‘T0’] strip_assume_tac AX2 >>
 qexistsl_tac [‘TR’,‘p’,‘q’] >> fs[] >> rpt strip_tac >> rw[])
(form_goal
 “!A B. ?AxB p1:AxB ~>A p2:AxB ~>B.isFun(p1) & isFun(p2) &
  (!x:mem(A) y:mem(B). ?r:mem(AxB).Eval(p1,r) = x & Eval(p2,r) = y) &
   !r s. Eval(p1,r) = Eval(p1,s) & Eval(p2,r) = Eval(p2,s) ==> r = s
  ”)



val Cross_def =
    Cross_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "*" ["A","B"]
             |> C mp (trueI []) |> gen_all
             |> store_as "Cross_def";

val pr1_def =
   Cross_def |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "pr1" ["A","B"]
             |> C mp (trueI []) |> gen_all
             |> store_as "pr1_def";

val pr2_def =
   pr1_def |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "pr2" ["A","B"]
             |> C mp (trueI []) |> gen_all
             |> store_as "pr2_def";

val SetPr_def = define_pred
“!A B AxB p1:AxB~>A p2:AxB~>B. 
 SetPr(p1,p2) <=>
 !X f:X~>A g:X~>B.isFun(f) & isFun(g) ==> ?!fg: X~>AxB.isFun(fg) & p1 @ fg = f & p2 @ fg = g”;


fun Cross A B = mk_fun "*" [A,B];

val pr12_Fun = prove_store("pr12_Fun",
e0
(strip_tac >> strip_tac >>
 qspecl_then [‘A’,‘B’] strip_assume_tac pr2_def >>
 arw[])
(form_goal
“!A B. isFun(pr1(A,B)) & isFun(pr2(A,B))”));



val oR_Eval = prove_store("oR_Eval",
e0
(rpt strip_tac >> 
 qby_tac ‘isFun(g @ f)’ >-- (irule oR_Fun >> arw[]) >> 
 drule $ GSYM Eval_def >> arw[] >>
 rw[GSYM oR_def] >> qexists_tac ‘Eval(f,a)’ >>
 rev_drule $ GSYM Eval_def >>
 first_x_assum (qspecl_then [‘a’,‘Eval(f,a)’] assume_tac) >> fs[] >>
 qpick_x_assum ‘isFun(g)’ assume_tac >>
 drule Holds_Eval >> arw[])
(form_goal
 “!A B f:A~>B C g:B~>C a:mem(A). isFun(f) & isFun(g) ==> 
  Eval(g,Eval(f,a)) = Eval(g @ f,a)”));



val Thm_2_8_SetPr = prove_store("Thm_2_8_SetPr",
e0
(rpt strip_tac >> rw[SetPr_def] >> rpt strip_tac >>
 rw[uex_def “?!fg:X~> A * B.isFun(fg) & pr1(A,B) @ fg = f & pr2(A,B) @ fg = g”] >>
 strip_assume_tac $
 uex_expand $ 
 fVar_Inst 
 [("P",([("x",mem_sort (mk_set "X")),
        ("ab",mem_sort (Cross (mk_set"A") (mk_set "B")))],
  “Eval(pr1(A,B),ab) = Eval(f:X~>A,x) & 
   Eval(pr2(A,B),ab) = Eval(g:X~>B,x)”))] (AX1 |> qspecl [‘X’,‘A * B’]) >>
 qexists_tac ‘R’ >> 
 qspecl_then [‘A’,‘B’] strip_assume_tac pr2_def >>
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> 
  rpt strip_tac (* 2 *) >-- 
  (first_x_assum (qspecl_then [‘Eval(f,a)’,‘Eval(g,a)’] assume_tac) >>
   arw[]) >>
  first_x_assum irule >> arw[]) >> arw[] >>
 qby_tac ‘pr1(A, B) @ R = f & pr2(A, B) @ R = g’ >--
 (arw[R_EXT,GSYM oR_def] >> rpt strip_tac (* 2 *) 
  >-- (assume_tac Eval_def >> 
       first_assum (qspecl_then [‘A * B’,‘A’,‘pr1(A,B)’] assume_tac) >>
       first_x_assum drule >>
       first_x_assum (qspecl_then [‘X’,‘A’,‘f’] assume_tac) >>
       first_x_assum drule >> arw[] >>
       dimp_tac >> strip_tac (* 2 *) >-- arw[] >>
       first_x_assum 
        (qspecl_then [‘Eval(f,a)’,‘Eval(g,a)’] strip_assume_tac) >>
       qexists_tac ‘r’ >> arw[]) >>
 assume_tac Eval_def >> 
 first_assum (qspecl_then [‘A * B’,‘B’,‘pr2(A,B)’] assume_tac) >>
 first_x_assum drule >>
 first_x_assum (qspecl_then [‘X’,‘B’,‘g’] assume_tac) >>
 first_x_assum drule >> arw[] >>
 dimp_tac >> strip_tac (* 2 *) >-- arw[] >>
 first_x_assum 
  (qspecl_then [‘Eval(f,a)’,‘Eval(g,a)’] strip_assume_tac) >>
 qexists_tac ‘r’ >> arw[]) >> arw[] 
 (*last subgoal*)
 >>
 rpt strip_tac >> first_x_assum irule >> 
 drule Eval_def >> arw[] >> pop_assum (K all_tac) >>
 rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (once_arw[] >>
     qby_tac ‘Eval(pr1(A, B), Eval(fg', a)) = Eval(pr1(A,B) @ fg',a) & 
              Eval(pr2(A, B), Eval(fg', a)) = Eval(pr2(A,B) @ fg',a)’
     >-- (strip_tac >> irule oR_Eval >> arw[]) >>
     arw[]) >>
 first_x_assum irule >> arw[] >> strip_tac >> 
 fconv_tac (rewr_fconv (eq_sym "mem")) (* 2 *)
 >-- (qpick_x_assum ‘pr1(A, B) @ fg' = f’ (assume_tac o GSYM) >>
 once_arw[] >> irule oR_Eval >> arw[]) >>
 qpick_x_assum ‘pr2(A, B) @ fg' = g’
      (assume_tac o GSYM) >>
 once_arw[] >> irule oR_Eval >> arw[])
(form_goal
“!A B. SetPr(pr1(A,B),pr2(A,B))”));


val isPr_def = define_pred
“!A B AxB p1:AxB->A p2:AxB->B. isPr(p1,p2) <=>
 (!X f:X->A g:X->B. ?!fg:X->AxB. p1 o fg = f & p2 o fg = g)”;

val p1_ex = prove_store("p1_ex",
e0
(rpt strip_tac >> qexists_tac ‘asF(pr1(A,B))’ >> rw[])
(form_goal
 “!A B. ?p1. p1 = asF(pr1(A,B))”));


val p2_ex = prove_store("p2_ex",
e0
(rpt strip_tac >> qexists_tac ‘asF(pr2(A,B))’ >> rw[])
(form_goal
 “!A B. ?p2. p2 = asF(pr2(A,B))”));



val p1_def = p1_ex |> spec_all |> ex2fsym0 "p1" ["A","B"]
                   |> gen_all |> store_as "p1_def";


val p2_def = p2_ex |> spec_all |> ex2fsym0 "p2" ["A","B"]
                   |> gen_all |> store_as "p2_def";

val asR_eq_eq = prove_store("asR_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 once_rw[GSYM asF_asR] >> arw[])
(form_goal
 “!A B f:A->B g. asR(f) = asR(g) <=> f = g”));


val Pr_ex = prove_store("Pr_ex",
e0
(rw[isPr_def] >> rpt strip_tac >>
 qspecl_then [‘A’,‘B’] assume_tac Thm_2_8_SetPr >>
 fs[SetPr_def] >> 
 first_x_assum (qsspecl_then [‘asR(f)’,‘asR(g)’] assume_tac)>>
 fs[asR_Fun] >>
 pop_assum (strip_assume_tac o uex_expand) >>
 uex_tac >> qexists_tac ‘asF(fg)’ >>
 rw[p1_def,p2_def] >> rpt strip_tac (* 3 *)
 >-- (qsuff_tac 
      ‘asF(pr1(A, B)) o asF(fg) = asF(pr1(A,B) @ fg)’ 
     >-- arw[asF_asR] >>
     irule asF_o >> arw[pr12_Fun])
 >-- (qsuff_tac 
      ‘asF(pr2(A, B)) o asF(fg) = asF(pr2(A,B) @ fg)’ 
     >-- arw[asF_asR] >>
     irule asF_o >> arw[pr12_Fun]) >>
 irule $ iffLR asR_eq_eq >> 
 drule asR_asF >> arw[] >> first_x_assum irule >>
 rw[asR_Fun] >>
 qpick_x_assum ‘asF(pr1(A, B)) o fg' = f’
 (assume_tac o GSYM) >>
 qpick_x_assum ‘asF(pr2(A, B)) o fg' = g’
 (assume_tac o GSYM) >>
 arw[GSYM asR_oR] >>
 qsuff_tac ‘asR(asF(pr1(A, B))) = pr1(A,B) & 
            asR(asF(pr2(A, B))) = pr2(A,B)’ 
 >-- (rpt strip_tac >> arw[]) >>
 strip_tac >> irule asR_asF >> rw[pr12_Fun])
(form_goal
 “!A B. isPr(p1(A,B),p2(A,B))”));


val Pa_def = rewr_rule[isPr_def] Pr_ex
                     |> spec_all |> uex_expand
                     |> ex2fsym0 "Pa" ["f","g"]
                     |> qgen ‘g’ |> qgen ‘B’ |> gen_all
                     |> store_as "Pa_def";

val p12_of_Pa =
    Pa_def |> spec_all |> conjE1
           |> qgen ‘g’ |> qgen ‘B’ |> gen_all
           |> store_as "p12_of_Pa";

val p1_of_Pa = p12_of_Pa |> spec_all |> conjE1
                         |> qgen ‘g’ |> qgen ‘B’ |> gen_all
                         |> store_as "p1_of_Pa";


val p2_of_Pa = p12_of_Pa |> spec_all |> conjE2
                         |> qgen ‘g’ |> qgen ‘B’ |> gen_all
                         |> store_as "p2_of_Pa";

val is_Pa = Pa_def |> spec_all |> conjE2
                   |> qgen ‘g’ |> qgen ‘B’ |> gen_all
                   |> store_as "is_Pa";


val SetEz_def = define_pred
“!A B f:A~>B g:A~>B E e:E~>A. SetEz(f,g,e) <=>
 isFun(f) & isFun(g) & isFun(e) & f @ e = g @ e & !X x:X~>A.isFun(x) & f @ x = g @ x ==> ?!x0:X~>E. isFun(x0) & x = e @ x0”;


val Inj_Fun = prove_store("Inj_Fun",
e0
(rw[Inj_def] >> rpt strip_tac >> arw[])
(form_goal
 “!A B f:A~>B. isInj(f) ==> isFun(f)”));


val Inj_lcancel = prove_store("Inj_lcancel",
e0
(rpt strip_tac >> fs[Inj_def] >>
 irule $ iffRL FUN_EXT >> arw[] >> strip_tac >> 
 qsuff_tac ‘Eval(m,Eval(f,a)) = Eval(m,Eval(g,a))’ >--
 (strip_tac >> first_x_assum irule >> arw[]) >>
 qby_tac ‘Eval(m, Eval(f, a)) = Eval(m @ f,a) &
          Eval(m, Eval(g, a)) = Eval(m @ g,a)’
 >-- (strip_tac >> irule oR_Eval >> arw[]) >>
 arw[])
(form_goal
 “!A B m:A~>B.isInj(m) ==>
  !X f:X~>A g:X~>A. isFun(f) & isFun(g) & m @ f = m @ g ==> f = g”));



local
val lemma =
fVar_Inst [("P",([("a",mem_sort (mk_set "A"))],“Eval(f:A~>X,a) = Eval(g:A~>X,a)”))] (Thm_2_4|> qspecl [‘A’]) |> gen_all
val lemma1 = 
fVar_Inst [("P",([("a0",mem_sort (mk_set "X")),("a0'",mem_sort (mk_set "E"))],“Eval(e:E~>A,a0') = Eval(x:X~>A,a0)”))] (AX1|> qspecl [‘X’,‘E’])
|> uex_expand
in
val Thm_2_9_Eqlz = proved_th $
e0
(rpt strip_tac >> rw[SetEz_def] >>
 qspecl_then [‘A’,‘B’,‘f’,‘g’]
  (x_choosel_then ["E","e"] strip_assume_tac) lemma >>
 qexistsl_tac [‘E’,‘e’] >> arw[] >> 
 drule Inj_Fun >> arw[] >> rpt strip_tac >--
 (irule $ iffRL FUN_EXT >> rpt strip_tac 
 >-- (irule oR_Fun >> arw[])
 >-- (irule oR_Fun >> arw[]) >>
 first_x_assum (qspecl_then [‘Eval(e,a)’] assume_tac) >>
 qsuff_tac
 ‘Eval(f, Eval(e, a)) = Eval(f @ e, a) & 
  Eval(g, Eval(e, a)) = Eval(g @ e, a)’ 
 >-- (rpt strip_tac >> fs[] >> qexists_tac ‘a’ >> rw[]) >>
 strip_tac >> irule oR_Eval >> arw[]) >>
 rw[uex_def “?!x0:X~>E. isFun(x0) & x = e @ x0”] >>
 strip_assume_tac lemma1 >>
 qexists_tac ‘R’ >> 
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> rpt strip_tac >--
  (fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
  last_x_assum $ assume_tac o iffLR >>
  first_x_assum irule >> 
  qsuff_tac ‘Eval(f,Eval(x,a)) = Eval(f @ x,a) & 
             Eval(g,Eval(x,a)) = Eval(g @ x,a)’
  >-- (strip_tac >> fs[]) >>
  strip_tac (* 2 *) >> irule oR_Eval >> arw[]) >>
  fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 arw[] >> 
 qby_tac ‘x = e @ R’ >--
 (drule Eval_def >> fs[] >>
  qby_tac ‘isFun(e @ R)’ >-- (irule oR_Fun >> arw[]) >>
  irule (iffRL FUN_EXT) >>
  arw[] >> strip_tac >>
  qby_tac ‘Eval(e @ R,a) = Eval(e,Eval(R,a))’
  >-- (irule $ GSYM oR_Eval >> arw[]) >>
  arw[] >> last_x_assum (qspecl_then [‘a’,‘Eval(R,a)’] assume_tac) >>
  fs[]) >> arw[] >>
 rpt strip_tac >> irule Inj_lcancel >> arw[] >>
 qexistsl_tac [‘A’,‘e’] >> arw[])
(form_goal
“!A B f:A~>B g:A~>B.isFun(f) & isFun(g) ==> ?E e:E~>A.SetEz(f,g,e)”)
end


val isEq_def = define_pred
“!A B f:A->B g E e:E->A. 
      isEq(f,g,e) <=> 
      f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0”

val isEq_ex = prove_store("isEq_ex",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’,‘asR(f)’,‘asR(g)’]
 assume_tac Thm_2_9_Eqlz >>
 fs[asR_Fun,SetEz_def] >>
 qexistsl_tac [‘E’,‘asF(e)’] >> rw[isEq_def] >>
 rpt strip_tac (* 2 *)
 >-- (irule $ iffLR asR_eq_eq >> rw[GSYM asR_oR] >>
      drule asR_asF >> arw[]) >>
 uex_tac >>
 first_x_assum (qsspecl_then [‘asR(a)’] assume_tac) >>
 rfs[asR_Fun,asR_oR] >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘asF(x0)’ >> rpt strip_tac (* 2 *)
 >-- (irule $ iffLR asR_eq_eq >> 
     arw[] >> 
     qsuff_tac ‘asF(e) o asF(x0) = asF(e @ x0)’ 
     >-- (rpt strip_tac >> arw[] >> irule $ GSYM asR_asF >>
         irule oR_Fun >> arw[]) >>
     irule asF_o >> arw[]) >>
 irule $ iffLR asR_eq_eq >> drule asR_asF >> arw[] >>
 first_x_assum irule >> 
 rw[asR_Fun] >> 
 qby_tac ‘asR(a) = asR(asF(e) o a0')’
 >-- (qpick_x_assum ‘asR(a) = e @ x0’ (K all_tac) >> arw[]) >>
 qpick_x_assum ‘asR(a) = e @ x0’ (K all_tac) >>
 arw[GSYM asR_oR] >> rev_drule asR_asF >> arw[])
(form_goal
 “!A B f:A->B g. ?E e:E->A.isEq(f,g,e)”));



local
val lemma =
fVar_Inst [("P",([("b",mem_sort (mk_set "B"))],“?a:mem(A).Eval(f:A~>B,a) = b”))] (Thm_2_4|> qspecl [‘B’]) 
val lemma1 = 
fVar_Inst [("P",([("x",mem_sort (mk_set "A")),("y",mem_sort (mk_set "s"))],“Eval(f:A~>B,x) = Eval(m:s~>B,y)”))] (AX1|> qspecl [‘A’,‘s’]) |> uex_expand
in
val Thm_2_10 = proved_th $
e0
(rpt strip_tac >> 
 x_choosel_then ["s","m"] strip_assume_tac lemma >>
 x_choose_then "e" strip_assume_tac lemma1 >>
 qexistsl_tac [‘s’,‘e’,‘m’] >> 
 arw[] >>
 qby_tac ‘isFun(e)’ >--
 (rw[Fun_expand] >> arw[] >> rpt strip_tac (* 2 *)
  >-- (last_x_assum $ irule o iffLR >> qexists_tac ‘a’ >> rw[]) >>
  fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 qby_tac ‘isSurj(e)’ >--
 (arw[Surj_def] >> strip_tac >> drule Eval_def >> fs[] >> 
  fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
  arw[] >> qexists_tac ‘y’ >> rw[]) >> arw[] >>
 qby_tac ‘isFun(m @ e)’ >-- (irule oR_Fun >> arw[] >>
 fs[Inj_def]) >>
 irule $ iffRL FUN_EXT >> arw[] >> strip_tac >>
 qpick_x_assum ‘isFun(e)’ assume_tac >> drule Eval_def >> fs[] >>
 last_x_assum (qspecl_then [‘a’,‘Eval(e,a)’] assume_tac) >> fs[] >>
 irule oR_Eval >> arw[] >> fs[Inj_def])
(form_goal
“!A B f:A~>B. isFun(f) ==> ?M e:A~>M m:M~>B. f = m @ e & isSurj(e) & isInj(m)”)
end





local
val lemma =
fVar_Inst [("P",([("b",mem_sort (mk_set "B"))],“?a:mem(A).Eval(f:A~>B,a) = b”))] (Thm_2_4|> qspecl [‘B’]) 
val lemma1 = 
fVar_Inst [("P",([("x",mem_sort (mk_set "A")),("y",mem_sort (mk_set "s"))],“Eval(f:A~>B,x) = Eval(m:s~>B,y)”))] (AX1|> qspecl [‘A’,‘s’]) |> uex_expand
in
val Thm_2_10 = proved_th $
e0
(rpt strip_tac >> 
 x_choosel_then ["s","m"] strip_assume_tac lemma >>
 x_choose_then "e" strip_assume_tac lemma1 >>
 qexistsl_tac [‘s’,‘e’,‘m’] >> 
 arw[] >>
 qby_tac ‘isFun(e)’ >--
 (rw[Fun_expand] >> arw[] >> rpt strip_tac (* 2 *)
  >-- (last_x_assum $ irule o iffLR >> qexists_tac ‘a’ >> rw[]) >>
  fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 qby_tac ‘isSurj(e)’ >--
 (arw[Surj_def] >> strip_tac >> drule Eval_def >> fs[] >> 
  fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
  arw[] >> qexists_tac ‘y’ >> rw[]) >> arw[] >>
 qby_tac ‘isFun(m @ e)’ >-- (irule oR_Fun >> arw[] >>
 fs[Inj_def]) >>
 qby_tac ‘f = m @ e’
 >-- 
 (irule $ iffRL FUN_EXT >> arw[] >> strip_tac >>
 qpick_x_assum ‘isFun(e)’ assume_tac >> drule Eval_def >> fs[] >>
 last_x_assum (qspecl_then [‘a’,‘Eval(e,a)’] assume_tac) >> fs[] >>
 irule oR_Eval >> arw[] >> fs[Inj_def]) >>
 arw[] >> rpt strip_tac >>
 
 )
(form_goal
“!A B f:A~>B. isFun(f) ==> ?M e:A~>M m:M~>B. f = m @ e & isSurj(e) & isInj(m) & 
 !M1 e1:A~>M1 m1. f = m1 @ e1 & isSurj(e1) & isInj(m1) ==>
  ?i:M ~> M1 j:M1~>M. isFun(i) & isFun(j) & 
  i @ j = id(M1) & j @ i = id(M)”)
end

val INJ_SURJ_fac = prove_store("INJ_SURJ_fac",
e0
()
(form_goal
 “!A B f:A->B. ?M e:A->M m:M->B. ?f = m o e ”));
