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



(*Thm_2_3_5*)
val To1_fun_uex = prove_store("To1_fun_uex",
e0
(strip_tac >> uex_tac >> qexists_tac ‘asF(To1(A))’ >> rw[] >>
 strip_tac >> irule is_asF >> rw[To1_Fun] >> rw[dot_def] >>
 rpt strip_tac >> 
 qspecl_then [‘A’] assume_tac To1_Fun >>
 drule Eval_def >> arw[dot_def]
 )
(form_goal
 “!A. ?!f:A~>1. T”));
