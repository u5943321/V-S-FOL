

(*
fun mk_foralls nsl f = 
    case nsl of 
        [] => f
      | (h as (n,s)) :: t =>
        mk_forall n s (mk_foralls t f)

fun define_pred f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse 
                raise simple_fail
                      "formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_fvar l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = new_pred P (List.map dest_var args)
        val l' = mk_pred P args
        val f' = mk_foralls bvs (mk_dimp l' r)
    in mk_thm(essps,[],f')
    end 

*)


(*
fun sspecl tl th = 
    let val (b,vs) = strip_forall $ concl th
        val ars = List.filter (fn (n,s) => not (on_ground o fst o dest_sort o snd $ (n,s))) vs
        val env = match_tl essps (List.map mk_var ars) tl emptyvd
        val tl' = List.map (inst_term env) (List.map mk_var vs)
    in specl tl' th
    end


fun sspecl_then tl (ttac: thm_tactic): thm_tactic = 
    fn th => ttac (sspecl tl th)

val qsspecl_then = qterml_tcl sspecl_then

*)



(*
fun store_as name th = 
let val _ = store_thm(name, th)
in th
end

*)

(*
local
fun delete'(set,mem) = HOLset.delete(set,mem) handle _ => set
in
fun filter_cont ct = 
    HOLset.foldr 
        (fn (ns,set) => 
            case HOLset.find 
                     (fn (vn,vs) => HOLset.member(fvs vs,ns)) set of 
                SOME _ => delete'(set,ns)
              | NONE => set) ct ct
end

fun ex2fsym fsym strl th = 
    let val th' = spec_all th
        val (ct,asl) = (cont th',ant th')
        val (hyp,conc) = dest_imp (concl th')
        val inputvars0 = filter_cont (cont th') 
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) essps 
                                   (List.map (dest_var o (parse_term_with_cont ct)) strl)
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val inputvl = List.map (parse_term_with_cont ct) strl
        val ((n,s),b) = dest_exists conc
        val _ = new_fun fsym (s,List.map dest_var inputvl)
        val fterm = mk_fun fsym inputvl
        val b' = substf ((n,s),fterm) b
    in mk_thm (ct,asl,mk_imp hyp b')
    end

*)




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
fun uex_expand th = rewr_rule [uex_def $ concl th] th



val _ = new_sort "ob" [] 
val _ = new_sort "ar" [("A",mk_sort "ob" []),("B",mk_sort "ob" [])]
val _ = EqSorts := "ar" :: (!EqSorts)
val ob_sort = mk_sort "ob" [];
fun ar_sort A B = mk_sort "ar" [A,B];

val _ = new_fun "1" (mk_sort "ob" [],[]);
val ONE = mk_fun "1" [];
val _ = new_fun "To1" (mk_sort "ar" [mk_var ("A",ob_sort),ONE],[("A",ob_sort)]);
val _ = new_fun "0" (mk_sort "ob" [],[]);
val ZERO = mk_fun "0" [];
val _ = new_fun "From0" (mk_sort "ar" [ZERO,mk_var ("A",ob_sort)],[("A",ob_sort)]);


val _ = new_fun "*" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun Po A B = mk_fun "*" [A,B];
val _ = new_fun "+" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun coPo A B = mk_fun "+" [A,B];
val _ = new_fun "Exp" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun Exp A B = mk_fun "Exp" [A,B];

fun mk_ob name = mk_var (name,ob_sort);
fun mk_ar name dom cod = mk_var (name,ar_sort dom cod);
val _ = new_fun "Pa" (ar_sort (mk_ob "X") (Po (mk_ob "A") (mk_ob "B")),
 [("f",ar_sort (mk_ob "X") (mk_ob "A")),("g",ar_sort (mk_ob "X") (mk_ob "B"))]);

val _ = new_fun "o" (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])],[("f",mk_sort "ar" [mk_var("B",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])]),("g",mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("B",mk_sort "ob" [])])])


val _ = new_fun "id" 
       (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("A",mk_sort "ob" [])],
        [("A",mk_sort "ob" [])])

val _ = new_sort_infix "ar" "->"


(*
fun new_ax f = 
    let
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end
 
fun store_ax (name,f) = store_as name (new_ax f)
*)

val idL = store_ax("idL", “!B A f:B->A. id(A) o f = f”);

val idR = store_ax("idR",“!A B f:A->B. f o id(A) = f”);

val o_assoc = store_ax("o_assoc",“!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f”);


val is1_def = define_pred
“!ONE. is1(ONE) <=> !X.?!f:X->ONE.T”

(*
val _ = new_pred "is1" [("ONE",ob_sort)]

val is1_def = store_ax("is1_def",“!ONE. is1(ONE) <=> !X.?!f:X->ONE.T”)

*)

val ONE_ex = store_ax("ONE_ex",“?ONE.is1(ONE)”)

fun ex2fsym0 name args th = th |> eqT_intro |> iffRL |> ex2fsym name args
                               |> C mp (trueI [])
                    
val ONE_def = ex2fsym0 "1" [] ONE_ex |> store_as "ONE_def"

val ONE_prop = ONE_def |> rewr_rule [is1_def]
                       |> store_as "ONE_prop"

(*why rewr_rule with is1_def loops? it thought is1 is fVar notpred  TODO*)

val To1_def = ONE_prop |> spec_all |> uex_expand |> ex2fsym0 "To1" ["X"] |> gen_all |> store_as "To1_def"

(*val _ = new_pred "is0" [("ZERO",ob_sort)] *)

val is0_def = 
define_pred “!ZERO.is0(ZERO) <=> !X.?!f:ZERO ->X. T”

(* store_ax("is0_def",“!ZERO.is0(ZERO) <=> !X.?!f:ZERO ->X. T”) *)



val ZERO_ex = store_ax("ZERO_ex",“?ZERO.is0(ZERO)”)

val ZERO_def = ex2fsym0 "0" [] ZERO_ex |> store_as "ZERO_def"

val ZERO_prop = ZERO_def |> conv_rule (once_depth_fconv no_conv (rewr_fconv (spec_all is0_def))) |> store_as "ZERO_prop"

val From0_def = ZERO_prop |> spec_all |> uex_expand |> ex2fsym0 "From0" ["X"] |> gen_all |> store_as "From0_def"


val isPr_def = define_pred“!A B AB p1:AB->A p2:AB->B. isPr(p1,p2) <=>
   !X f:X->A g:X->B.?!fg:X->AB. p1 o fg = f & p2 o fg = g”

(*
val _ = new_pred "isPr" [("p1",ar_sort (mk_ob "AB") (mk_ob "A")),
                         ("p2",ar_sort (mk_ob "AB") (mk_ob "B"))]

val isPr_def = store_ax("isPr_def",“!A B AB p1:AB->A p2:AB->B. isPr(p1,p2) <=>
   !X f:X->A g:X->B.?!fg:X->AB. p1 o fg = f & p2 o fg = g”)
*)


val isPr_ex = store_ax("isPr_ex",“!A B.?AB p1:AB->A p2:AB->B.isPr(p1,p2)”);

val Po_def = isPr_ex |> spec_all |> ex2fsym0 "*" ["A","B"] |> gen_all |> store_as "Po_def"

val p1_def = Po_def |> spec_all |> ex2fsym0 "p1" ["A","B"] |> gen_all |> store_as "p1_def"

val p2_def = p1_def |> spec_all |> ex2fsym0 "p2" ["A","B"] |> gen_all |> store_as "p2_def"

val Pa_def = p2_def |> rewr_rule[isPr_def] |> spec_all
                    |> uex_expand 
                    |> ex2fsym0 "Pa" ["f","g"] |> gen_all
                    |> store_as "Pa_def"


val iscoPr_def = define_pred
“!A B AB i1:A->AB i2:B->AB. iscoPr(i1,i2) <=>
   !X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g”

(*
val _ = new_pred "iscoPr" [("i1",ar_sort (mk_ob "A") (mk_ob "AB")),
                           ("i2",ar_sort (mk_ob "B") (mk_ob "AB"))]

val iscoPr_def = store_ax("iscoPr_def",“!A B AB i1:A->AB i2:B->AB. iscoPr(i1,i2) <=>
   !X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g”);
*)


val iscoPr_ex = store_ax("iscoPr_ex",“!A B.?AB i1:A->AB i2:B->AB.iscoPr(i1,i2)”);

val coPo_def = iscoPr_ex |> spec_all |> ex2fsym0 "+" ["A","B"] |> gen_all |> store_as "coPo_def";

val i1_def = coPo_def |> spec_all |> ex2fsym0 "i1" ["A","B"] |> gen_all |> store_as "i1_def";

val i2_def = i1_def |> spec_all |> ex2fsym0 "i2" ["A","B"] |> gen_all |> store_as "i2_def";

val coPa_def = i2_def |> rewr_rule[iscoPr_def] |> spec_all
                      |> uex_expand 
                      |> ex2fsym0 "coPa" ["f","g"]
                      |> gen_all
                      |> store_as "coPa_def";


(*TODO: if ispr i.e. formula variable, then will loop*)


val isEq_def = define_pred
“!A B f:A->B g E e:E->A. 
      isEq(f,g,e) <=> 
      f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0”


(*
val _ = new_pred "isEq" 
                 [("f",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("g",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("e",ar_sort (mk_ob "E") (mk_ob "A"))];

val isEq_def = store_ax("isEq_def",
“!A B f:A->B g E e:E->A. 
      isEq(f,g,e) <=> 
      f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0”)
*) 


val isEq_ex = store_ax("isEq_ex",“!A B f:A->B g:A->B.?E e:E->A.isEq(f,g,e)”)


(*

val Eo_Ea_def = isEq_ex |> spec_all |> ex2fsym0 "Eo" ["f","g"]
|> ex2fsym0 "Ea" ["f","g"] |> gen_all         


val Ea_eqn = Eo_Ea_def |> rewr_rule [isEq_def] |> spec_all |> conjE1
|>   gen_all

val Eia_def = Eo_Ea_def |> rewr_rule [isEq_def] |> spec_all |> conjE2
|> spec_all |> undisch |> uex_expand |> ex2fsym0 "Eia" ["f","g","a"]
|> disch_all |> gen_all

val Eia_eqn = Eia_def |> spec_all |> undisch |> conjE1 |> disch_all 
|> gen_all



(*

EQ_fsym "Ea" [assume “f1:A->B = f2”,assume “g1:A->B = g2”]
 
 BA(g2 : ar(A, B))(g1 : ar(A, B))(f2 : ar(A, B))(f1 : ar(A, B))
   1.f1 = f2
   2.g1 = g2
   3.Ea(f1, g1) o Eia(f1, g1, Ea(f2, g2)) = Ea(f2, g2)
   ----------------------------------------------------------------------
   f2 o Ea(f1, g1) = g2 o Ea(f1, g1)

*)


val Eo_Ea_CONG = prove_store("Eo_Ea_CONG",
e0
(rpt strip_tac >>
 assume_tac Eia_def >>
 qsuff_tac
 ‘Eia(f1, g1, Ea(f2, g2)) o Eia(f2, g2, Ea(f1, g1)) = 
 Eia(f1,g1,Ea(f1,g1)) & 
 id(Eo(f1,g1))  = 
 Eia(f1,g1,Ea(f1,g1))’
 >-- (strip_tac >> arw[]) >>
 strip_tac >--
 (first_x_assum (qsspecl_then [‘f1’,‘g1’,‘Ea(f1,g1)’] assume_tac) >>
 pop_assum mp_tac >> 
 once_rw[Ea_eqn] >> rw[] >> strip_tac >>
 first_x_assum irule >> 
 rw[GSYM o_assoc] >>
 qby_tac ‘(Ea(f1, g1) o Eia(f1, g1, Ea(f2, g2))) = Ea(f2, g2)’
 >-- (irule $ GSYM Eia_eqn >> pop_assum (K all_tac) >>
     arw[Ea_eqn]) >>
 qpick_x_assum ‘Ea(f1, g1) = Ea(f1, g1) o Eia(f1, g1, Ea(f1, g1))’
 (K all_tac) >> arw[] >>
 irule Eia_eqn >> 
 qsuff_tac
 ‘f1 o Ea(f1, g1) = g1 o Ea(f1, g1)’
 >-- arw[] >> rw[Ea_eqn]) >>
 first_x_assum (qsspecl_then [‘f1’,‘g1’,‘Ea(f1,g1)’] assume_tac) >>
 pop_assum mp_tac >> 
 once_rw[Ea_eqn] >> rw[] >> strip_tac >>
 first_x_assum irule >> 
 rw[idR])
(form_goal
 “!A B f1:A->B g1 f2 g2. f1 = f2 & g1 = g2 ==>
  Eia(f1,g1,Ea(f2,g2)) o Eia(f2,g2,Ea(f1,g1)) = id(Eo(f1,g1)) ”));


rastt "Eia(i1(1,1),i2(1,1),id(1))"


*)

val Eqa_def = 
    isEq_def |> iffLR 
             |> spec_all |> undisch |> conjE2 
             |> spec_all |> undisch |> uex_expand
             |> conj_all_assum |> disch_all
             |> ex2fsym "Eqa" ["f","g","e","a"]
             |> gen_all
             |> store_as "Eqa_def"



val iscoEq_def = define_pred
“!A B f:A->B g cE ce:B -> cE. 
      iscoEq(f,g,ce) <=> 
      ce o f = ce o g & 
      !X x:B->X. x o f = x o g ==>
      ?!x0:cE->X. x = x0 o ce”

(*
val _ = new_pred "iscoEq" 
                 [("f",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("g",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("ce",ar_sort (mk_ob "B") (mk_ob "cE"))]

val iscoEq_def = store_ax("iscoEq_def",
“!A B f:A->B g cE ce:B -> cE. 
      iscoEq(f,g,ce) <=> 
      ce o f = ce o g & 
      !X x:B->X. x o f = x o g ==>
      ?!x0:cE->X. x = x0 o ce”)

*)

val iscoEq_ex = store_ax("iscoEq_ex",“!A B f:A->B g:A->B.?cE ce:B->cE.iscoEq(f,g,ce)”);

val coEqa_def = 
    iscoEq_def |> iffLR 
               |> spec_all |> undisch |> conjE2 
               |> spec_all |> undisch |> uex_expand
               |> conj_all_assum |> disch_all
               |> ex2fsym "coEqa" ["f","g","ce","x"]
               |> store_as "coEqa_def"
(*TodO tidy the conjs to imp here*)


(*
e that given any pair of objects A, B there exists an
object BA and a mapping A × BA→
e
B with the property that for any object X and any
mapping A × X →
f
B there is a unique mapping X →
h
BA such that (A × h)e = f. This
universal mapping property is partly expressed by the following diagram.
*)



val isExp_def = define_pred
“!A B A2B ev:A * A2B -> B.
         isExp(ev) <=> !X f:A * X->B. ?!h:X->A2B. ev o Pa(p1(A,X), h o p2(A,X)) = f”


(*
val _ = new_pred "isExp" 
 [("ev",ar_sort (Po (mk_ob "A") (mk_ob "A2B")) (mk_ob "B"))]

val isExp_def =
 store_ax("isExp_def",“!A B A2B ev:A * A2B -> B.
         isExp(ev) <=> !X f:A * X->B. ?!h:X->A2B. ev o Pa(p1(A,X), h o p2(A,X)) = f”)

*)


(*example here : we cannot get function for eqlz, because the inputs are a pair of ars, and we need to produce an object first. But here the input are objects, we can produce an object from the objects first, the exp, and then have ev(A,B)*)

val isExp_ex = store_ax("isExp_ex",“!A B. ?A2B ev:A * A2B->B. isExp(ev)”);

val Exp_def = isExp_ex |> spec_all 
                       |> ex2fsym0 "Exp" ["A","B"] |> gen_all
                       |> store_as "Exp_def"

val Ev_def = Exp_def |> spec_all |> rewr_rule[isExp_def]
                     |> ex2fsym0 "Ev" ["A","B"]
                     |> gen_all
                     |> store_as "Ev_def"

val Tp_def = Ev_def |> spec_all |> uex_expand 
                    |> ex2fsym0 "Tp" ["f"] |> gen_all
                    |> store_as "Tp_def"


val N_ex = store_ax("N_ex",“?N O:1->N SUC:N->N.
 !X x0:1->X t:X->X.?!x:N->X. x o O = x0 & x o SUC = t o x”)

val N_def = N_ex |> ex2fsym0 "N" [] |> store_as "N_def";

val O_def = N_def |> ex2fsym0 "O" [] |> store_as "O_def";

val SUC_def = O_def |> ex2fsym0 "SUC" [] |> store_as "SUC_def";

val Nind_def = SUC_def |> spec_all |> uex_expand
                       |> ex2fsym0 "Nind" ["x0","t"]
                       |> gen_all
                       |> store_as "Nind_def"

val WP = store_ax("WP",“!A B f:A->B g.~(f = g) ==> ?a:1->A. ~(f o a = g o a)”);


(*mono does not need "is" version becuase it does not induce any function*)
val _ = new_pred "Mono" [("f",ar_sort (mk_ob "A") (mk_ob "B"))]

val Mono_def = store_ax("Mono_def",“!A B f:A->B. Mono(f) <=> !X g:X->A h. f o g = f o h ==> g = h”);

val _ = new_pred "Epi" [("f",ar_sort (mk_ob "A") (mk_ob "B"))]

val Epi_def = store_ax("Epi_def",“!A B f:A->B. Epi(f) <=> !X g:B->X h. g o f = h o f ==> g = h”);

val NONZERO_EL = store_ax("NONZERO_EL",“!X.~(is0(X)) ==>?x:1->X.T”);

val AC = store_ax("AC",“!A B a:1->A f:A->B. ?g:B->A. f o g o f = f”);

val INC_FAC = store_ax("INC_FAC",“!A B f:1->A + B. (?f0:1->A.i1(A,B) o f0 = f) |(?f0:1->B.i2(A,B) o f0 = f)”);

val DISTI_EL = store_ax("DISTI_EL",“?X x1:1->X x2. ~(x1 = x2)”);

val AX8 = DISTI_EL;

val FALSE_ex = prove_store ("FALSE_ex",
e0
(qexists_tac ‘i1(1,1)’ >> rw[])
(form_goal
 “?f. i1(1,1) = f”)
);

val FALSE_def = ex2fsym0 "FALSE" [] FALSE_ex 
                         |> store_as "FALSE_def"

val TRUE_ex = prove_store ("TRUE_ex",
e0
(qexists_tac ‘i2(1,1)’ >> rw[])
(form_goal
 “?f. i2(1,1) = f”)
);

val TRUE_def = ex2fsym0 "TRUE" [] TRUE_ex 
                        |> store_as "TRUE_def";


val Tp1_ex = prove_store("Tp1_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(f o p1(A,1))’ >> rw[])
(form_goal
“!A B f:A->B.?tpf:1->Exp(A,B).Tp(f o p1(A,1)) = tpf”));

val Ev_of_Tp = prove_store("Ev_of_Tp",
e0
(rpt strip_tac >> rw[Tp_def])
(form_goal
 “!A B X f:A * X ->B. 
  Ev(A,B) o Pa(p1(A,X),Tp(f) o p2(A,X)) = f”));

val Tp_eq = prove_store("Tp_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (once_rw[GSYM Ev_of_Tp] >> arw[]) >> arw[])
(form_goal
 “!A B X f:A * X ->B g:A * X ->B.Tp(f) = Tp(g) <=> f = g”));

val is_Tp = prove_store("is_Tp",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘B’,‘X’,‘f’] (assume_tac o conjE2) Tp_def>>
 first_x_assum irule >> arw[])
(form_goal
 “!A B X f:A * X ->B h:X-> Exp(A,B). 
  Ev(A,B) o Pa(p1(A,X),h o p2(A,X)) = f ==> h = Tp(f)”));

val Ev_eq_eq = prove_store("Ev_eq_eq",
e0
(rpt strip_tac >> 
 qsuff_tac ‘f = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X))) & 
  g = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X)))’
 >-- (rpt strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Tp >> first_x_assum accept_tac) >>
 irule is_Tp >> rw[])
(form_goal
 “!A B X f g. Ev(A,B) o Pa(p1(A,X),f o p2(A,X)) = 
              Ev(A,B) o Pa(p1(A,X),g o p2(A,X)) ==> f = g”));

val is_Pa = Pa_def |> spec_all |> conjE2 |> gen_all
                   |> store_as "is_Pa";

val to_P_component = prove_store("to_Pr_component",
e0
(rpt strip_tac >> irule is_Pa >> rw[])
(form_goal
 “!A B X f:X->A * B.  f = Pa(p1(A,B) o f,p2(A,B) o f)”));

val to_P_eq = prove_store("to_P_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f = Pa(p1(A,B) o g,p2(A,B) o g) &
            g = Pa(p1(A,B) o g,p2(A,B) o g)’ >--
 (strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Pa >> arw[]) >> once_rw[to_P_component])
(form_goal
 “!A B X f:X->A * B g:X->A * B. p1(A,B) o f = p1(A,B) o g &
 p2(A,B) o f = p2(A,B) o g ==> f = g”));

val is_coPa = coPa_def |> spec_all |> conjE2
                       |> gen_all
                       |> store_as "is_coPa";

val from_coP_component = prove_store("from_coP_component",
 e0
(rpt strip_tac >> irule is_coPa >> rw[])
(form_goal
 “!A B X f:A + B ->X g:A + B->X. f = coPa(f o i1(A,B),f o i2(A,B))”));


val from_coP_eq = prove_store("from_coP_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f = coPa(g o i1(A,B),g o i2(A,B)) &
            g = coPa(g o i1(A,B),g o i2(A,B))’ >--
 (strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >--
 (irule is_coPa >> arw[]) >> once_rw[from_coP_component])
(form_goal
 “!A B X f:A + B-> X g:A + B->X. f o i1(A,B) = g o i1(A,B) & f o i2(A,B) = g o i2(A,B) ==> f = g”));


val i12_of_coPa = coPa_def |> spec_all |> conjE1
                           |> gen_all 
                           |> store_as "i12_of_coPa";

val i1_of_coPa = i12_of_coPa |> spec_all |> conjE1
                             |> gen_all 
                             |> store_as "i1_of_coPa";


val i2_of_coPa = i12_of_coPa |> spec_all |> conjE2
                             |> gen_all 
                             |> store_as "i2_of_coPa";
 
val p12_of_Pa = Pa_def |> spec_all |> conjE1
                       |> gen_all
                       |> store_as "p12_of_Pa";

                       
val p1_of_Pa = p12_of_Pa |> spec_all |> conjE1
                         |> gen_all 
                         |> store_as "p1_of_Pa";

val p2_of_Pa = p12_of_Pa |> spec_all |> conjE2
                         |> gen_all 
                         |> store_as "p2_of_Pa";

 

val i1_ne_i2_1 = prove_store ("i1_ne_i2",
e0
(ccontra_tac >> 
 x_choosel_then ["X","x1","x2"] assume_tac DISTI_EL >>
 qsuff_tac ‘x1 = x2’ >-- arw[] >>
 qby_tac ‘coPa(x1,x2) o i1(1,1) = x1 &
          coPa(x1,x2) o i2(1,1) = x2’ >--
 rw[i12_of_coPa] >>
 pop_assum (assume_tac o GSYM) >> 
 qpick_x_assum ‘~(x1 = x2)’ (K all_tac) >> 
 once_arw[] >> pop_assum (K all_tac) >> arw[])
(form_goal
 “~(i1(1,1) = i2(1,1))”)
)

val to1_unique = prove_store("to1_unique",
e0
(rpt strip_tac >>
 qspecl_then [‘X’,‘f’] assume_tac To1_def >>
 qspecl_then [‘X’,‘g’] assume_tac To1_def >> 
 arw[])
(form_goal
 “!X f:X->1 g:X->1. f = g”));

val one_to_one_id = prove_store("one_to_one_id",
e0
(strip_tac >>
 qspecl_then [‘1’,‘f’,‘id(1)’] assume_tac to1_unique >>
 first_x_assum accept_tac)
(form_goal
 “!f:1->1. f = id(1)”))

val prop_5_lemma = prove_store("prop_5_lemma",
e0
(rpt strip_tac >> 
 ccontra_tac >> 
 qsuff_tac ‘i1(1,1) = i2(1,1)’ >-- rw[i1_ne_i2_1] >>
 qby_tac
 ‘coPa(i1(1,1) o To1(A),i2(1,1) o To1(B)) o i1(A, B) o x0 =   coPa(i1(1,1) o To1(A), i2(1,1) o To1(B)) o i2(A, B) o x0'’
 >-- arw[] >> 
 fs[GSYM o_assoc,i12_of_coPa] >>
 fs[o_assoc] >> pop_assum mp_tac >>
 once_rw[one_to_one_id] >> rw[idR])
(form_goal
 “!A B x0:1->A x0':1->B. ~(i1(A,B) o x0 = i2(A,B) o x0')”));

val i1_i2_disjoint = prove_store("i1_i2_disjoint",
e0
(rw[prop_5_lemma])
(form_goal
 “!X t:1->X. ~(i1(X,X) o t = i2(X,X) o t)”));

(*
val i1_ne_i2 = prove_store("i1_ne_i2",
e0
(strip_tac >> ccontra_tac >> 
 qbirule WP)
(form_goal
 “!X. ~(is0(X)) ==> ~(i1(X,X) = i2(X,X))”)); 

maybe todo
*)

val is0_expand = 
  iff_trans (is0_def |> spec_all) (uex_def “?!f:ZERO->X.T” |> rewr_rule [] |> forall_iff ("X",ob_sort)) |> gen_all

val from_zero_unique = prove_store("from_zero_unique",
e0
(rpt strip_tac >> fs[is0_expand] >>
 first_x_assum $ qspecl_then [‘X’] strip_assume_tac >>
 first_assum $ qspecl_then [‘f’] strip_assume_tac >>
 first_assum $ qspecl_then [‘g’] strip_assume_tac >>
 arw[])
(form_goal
 “!ZERO. is0(ZERO) ==> !X f:ZERO->X g. f = g”));

val no_Epi_from_zero = prove_store("no_Epi_from_zero",
e0
(rpt strip_tac >>
 ccontra_tac >> 
 qsuff_tac ‘i1(1,1) = i2(1,1)’ >-- rw[i1_ne_i2_1] >>
 qsuff_tac ‘i1(1,1) o To1(B) = i2(1,1) o To1(B)’ >--
 (strip_tac >> 
  qby_tac ‘?b:1->B.T’ >-- 
  (irule NONZERO_EL >> arw[]) >> 
  pop_assum strip_assume_tac >>
  qby_tac ‘i1(1, 1) o To1(B) o b = i2(1, 1) o To1(B) o b’ 
  >-- arw[GSYM o_assoc] >>
  pop_assum mp_tac >> once_rw[one_to_one_id] >> 
  rw[idR]) >>
 fs[Epi_def] >> first_x_assum irule >>
 irule from_zero_unique >> arw[])
(form_goal
“!A B f:A->B. Epi(f) ==>
 ~is0(B) ==> ~is0(A)”));

val ZERO_no_MEM = prove_store("ZERO_no_MEM",
 e0
(ccontra_tac >> pop_assum strip_assume_tac >>
 strip_assume_tac DISTI_EL >>
 qsuff_tac ‘x1 = x2’ >-- arw[] >>
 qby_tac ‘x1 = x1 o To1(0) o f & 
          x2 = x2 o To1(0) o f’
 >-- (once_rw[one_to_one_id] >> rw[idR]) >>
 qpick_x_assum ‘~(x1 = x2)’ (K all_tac) >>
 once_arw[] >> 
 rw[GSYM o_assoc] >>
 qsuff_tac ‘x1 o To1(0) = x2 o To1(0)’
 >-- (pop_assum (K all_tac) >> strip_tac >> arw[]) >>
 irule from_zero_unique >> rw[ZERO_def]
 )
(form_goal
 “~(?f:1->0.T)”));

val not_to_zero = prove_store("not_to_ZERO",
e0
(rpt strip_tac >> ccontra_tac >> drule NONZERO_EL >>
 pop_assum strip_assume_tac >> 
 suffices_tac ``?f:1->0.T``
 >-- (disch_tac >> fs[ZERO_no_MEM]) >>
 qexists_tac ‘f o x’ >> rw[])
(form_goal
 “!A f:A->0.is0(A)”));


val to_zero_zero = prove_store("to_ZERO_ZERO",
e0
(rpt strip_tac >> 
 qsuff_tac ‘?g:A->0.T’ >-- 
 (strip_tac >> 
  qspecl_then [‘A’,‘g’] accept_tac not_to_zero) >>
  fs[is0_expand] >> 
 first_x_assum (qspecl_then [‘0’] strip_assume_tac) >>
 qexists_tac ‘f' o f’ >> rw[]
 )
(form_goal
 “!A B f:A->B.is0(B) ==>is0(A)”));

fun try_done tac (G,fl,l) = 
    case tac (G,fl,l) of 
        ([],pf) => ([],pf)
       | _ => ([(G,fl,l):goal],sing I)

val non_zero_pinv = prove_store("non_zero_pinv",
e0
(rpt strip_tac >> 
 drule NONZERO_EL >> pop_assum strip_assume_tac >>
 qspecl_then [‘A’,‘B’,‘x’,‘f’] accept_tac AC)
(form_goal
 “!A.~is0(A) ==>!B f:A->B.?g:B->A. f o g o f = f”));

val Mono_pinv_post_inv = prove_store("Mono_pinv_post_inv",
e0
(rpt strip_tac >> fs[Mono_def] >> first_x_assum irule >>
 arw[idR])
(form_goal
 “!A B f:A->B. Mono(f) ==> !g:B->A. 
 f o g o f = f ==> g o f = id(A)”));

 
val Epi_pinv_pre_inv = prove_store("Epi_pinv_pre_inv",
e0
(rpt strip_tac >> fs[Epi_def] >> first_x_assum irule >>
 arw[idL,o_assoc])
(form_goal
 “!A B f:A->B. Epi(f) ==> !g:B->A. 
 f o g o f = f ==> f o g = id(B)”));

val Mono_no_zero_post_inv = prove_store("Mono_no_zero_post_inv",
e0
(rpt strip_tac >> drule non_zero_pinv >>
 drule Mono_pinv_post_inv >>
 first_x_assum (qspecl_then [‘B’,‘f’] strip_assume_tac) >>
 first_x_assum drule >>
 qexists_tac ‘g’ >> arw[]
 )
(form_goal
 “!A B f:A->B. Mono(f) ==> ~is0(A) ==>
  ?g:B->A. g o f = id(A)”));


val Epi_no_zero_pre_inv = prove_store("Epi_no_zero_pre_inv",
e0
(rpt strip_tac >> drule non_zero_pinv >>
 drule Epi_pinv_pre_inv >>
 first_x_assum (qspecl_then [‘B’,‘f’] strip_assume_tac) >>
 first_x_assum drule >>
 qexists_tac ‘g’ >> arw[]
 )
(form_goal
 “!A B f:A->B. Epi(f) ==> ~is0(A) ==>
  ?g:B->A. f o g = id(B)”));

val inc_inc_iso = prove_store("inc_inc_iso",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 cases_on “is0(X)” >> cases_on “is0(Y)” >>
 strip_tac >>
 try_done (irule from_zero_unique >> arw[]) (* 4 *)
 >-- (qspecl_then [‘Y’,‘X’,‘h2’] assume_tac to_zero_zero >>
      first_x_assum drule >> fs[])
 >-- (qspecl_then [‘X’,‘Y’,‘h1’] assume_tac to_zero_zero >>
      first_x_assum drule >> fs[])
 >-- (qby_tac ‘?b'. b' o b = id(Y)’ >--
      (irule Mono_no_zero_post_inv >> arw[]) >>
      pop_assum strip_assume_tac >> 
      qsuff_tac ‘b' o (b o h1) o h2 = id(Y)’ >--
      arw[GSYM o_assoc,idL] >>
      arw[]) >>
 qby_tac ‘?a'. a' o a = id(X)’ >--
 (irule Mono_no_zero_post_inv >> arw[]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac ‘a' o (a o h2) o h1 = id(X)’ >--
 arw[GSYM o_assoc,idL] >>
 arw[]
 )
(form_goal
 “!X A a:X->A Y b:Y->A h1:X->Y h2:Y->X. 
  Mono(a)& Mono(b) & b o h1 = a & a o h2 = b ==> 
  h1 o h2 = id(Y) & h2 o h1 = id(X)”));

(*
val parallel_P_o = prove_store("parallel_P_o",
e0
()
(form_goal
 “!”));
*)

val zero_no_MEM = prove_store("zero_no_MEM",
e0
(rpt strip_tac >> ccontra_tac >>
 pop_assum strip_assume_tac >>
 fs[is0_expand] >> assume_tac ZERO_no_MEM >>
 qsuff_tac ‘?f0:1->0.T’ >-- fs[] >>
 first_x_assum (qspecl_then [‘0’] strip_assume_tac) >>
 qexists_tac ‘f' o f’ >> rw[])
(form_goal
 “!zero. is0(zero) ==> ~(?f:1->zero.T)”));



val FUN_EXT = prove_store("FUN_EXT",
e0
(repeat strip_tac >> ccontra_tac >> drule WP >> 
 pop_assum strip_assume_tac >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >> 
 fs[])
(form_goal
 “!A B f:A->B g. (!a:1->A. f o a = g o a) ==> f = g”));


val prop_2_half2 = prove_store("prop_2_half2",
e0
(rpt strip_tac >> cases_on “is0(Y)” (* 2 *) >--
 (qby_tac ‘is0(X)’ >--
  (ccontra_tac >> 
   qsuff_tac ‘?y:1->Y.T’ >-- 
   (rw[] >> irule zero_no_MEM >> arw[]) >>
   drule NONZERO_EL >>
   pop_assum strip_assume_tac >>
   first_x_assum (qspecl_then [‘a o x’,‘x’] assume_tac) >>
   fs[] >> qexists_tac ‘xb'’ >> rw[]) >>
  fs[is0_expand] >>
  first_assum (qspecl_then [‘Y’] strip_assume_tac) >>
  qexists_tac ‘f’ >> 
  first_assum (qspecl_then [‘A’] strip_assume_tac) >>
  first_assum (qspecl_then [‘b o f’] strip_assume_tac) >>
  first_assum (qspecl_then [‘a’] strip_assume_tac) >>
  fs[]) >>
 drule Mono_no_zero_post_inv >> first_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘g o a’ >> irule FUN_EXT >>
 strip_tac >> 
 first_assum (qspecl_then [‘a o a'’,‘a'’] assume_tac) >>
 fs[] >> pop_assum (assume_tac o GSYM) >> arw[o_assoc] >>
 qby_tac ‘b o g o b o xb' = b o (g o b) o xb'’
 >-- rw[o_assoc] >>
 arw[idL])
(form_goal
 “!X A a:X->A. Mono(a) ==> !Y b:Y->A. Mono(b) ==>
  (!x:1->A xb:1->X. a o xb = x ==> ?xb':1->Y. b o xb' = x)
  ==> ?h:X->Y. b o h = a”));

val prop_2_coro_subo = prove_store("prop_2_coro_subo",
e0
(rpt strip_tac >>
 qby_tac ‘?h1. b o h1 = a’ 
 >-- (irule prop_2_half2 >> arw[] >> rpt strip_tac >>
      first_assum (qspecl_then [‘xb’] strip_assume_tac) >>
      qexists_tac ‘y’ >> fs[]) >>
 qby_tac ‘?h2. a o h2 = b’ 
 >-- (irule prop_2_half2 >> arw[] >> rpt strip_tac >>
      first_assum (qspecl_then [‘xb’] strip_assume_tac) >>
      qexists_tac ‘x'’ >> fs[]) >>
 pop_assum_list (map_every strip_assume_tac) >>
 qexistsl_tac [‘h1’,‘h2’] >> arw[] >>
 irule inc_inc_iso >> qexistsl_tac [‘A’,‘a’,‘b’] >> arw[])
(form_goal
 “!X A a:X->A.Mono(a) ==> 
  !Y b:Y->A. Mono(b) & 
             (!y:1->Y. ?x:1->X.a o x = b o y) & 
             (!x:1->X. ?y:1->Y.a o x = b o y) ==> 
  ?h1:X->Y h2:Y->X. 
    b o h1 = a & a o h2 = b & 
    h1 o h2 = id(Y) & h2 o h1 = id(X)”));

val _ = new_pred "areiso" [("A",ob_sort),("B",ob_sort)]

val areiso_def = store_ax("areiso_def",
“!A B. areiso(A,B) <=> ?f:A->B g:B->A. f o g = id(B) & g o f = id(A)”)

val prop_2_coro = prove_store("prop_2_coro",
e0
(repeat strip_tac >> rw[areiso_def] >>
 rev_drule prop_2_coro_subo >>
 first_x_assum (qspecl_then [‘Y’,‘b’] assume_tac) >>
 rev_full_simp_tac[] >>
 qexistsl_tac [‘h1’,‘h2’] >> arw[])
(form_goal
 “!X A a:X->A. Mono(a) ==>
  !Y b:Y->A. Mono(b) & 
  (!y:1->Y. ?x:1->X.a o x = b o y) & 
  (!x:1->X.?y:1->Y.a o x = b o y) ==> areiso(X,Y)”));

val Epi_has_section = prove_store("Epi_has_section",
e0
(rpt strip_tac >> cases_on “is0(B)” 
 >-- (fs[is0_expand] >> 
      first_assum (qspecl_then [‘B’] strip_assume_tac) >>
      first_assum (qspecl_then [‘A’] strip_assume_tac) >>
      qexists_tac ‘f'’ >>
      arw[]) >>
 drule no_Epi_from_zero >> first_assum drule >>
 drule NONZERO_EL >> pop_assum strip_assume_tac >>
 qspecl_then [‘A’,‘B’,‘x’,‘e’] strip_assume_tac AC >>
 drule Epi_pinv_pre_inv >> first_assum drule >>
 qexists_tac ‘g’ >> arw[])
(form_goal
 “!A B e:A->B. Epi(e) ==>?s0:B->A. e o s0 = id(B)”));

val Eq_equality = isEq_def |> iffLR |> strip_all_and_imp
                           |> conjE1 |> disch_all
                           |> gen_all
                           |> store_as "Eq_equality";


val coEq_equality = iscoEq_def |> iffLR |> strip_all_and_imp
                               |> conjE1 |> disch_all
                               |> gen_all
                               |> store_as "coEq_equality";

val isEq_expand = 
    isEq_def 
        |> rewr_rule[uex_def “?!a0:X->E.a = (e:E->A) o a0”]
        |> store_as "isEq_expand";


val iscoEq_expand = 
    iscoEq_def 
        |> rewr_rule[uex_def “?!x0:cE->X.x = x0 o (ce:B->cE)”]
        |> store_as "iscoEq_expand";

val coEq_of_equal = prove_store("coEq_of_equal",
e0
(rpt strip_tac >> rw[iscoEq_expand,idR] >> rpt strip_tac >>
 qexists_tac ‘x’ >> rw[] >> rpt strip_tac >> arw[])
(form_goal
 “!A B f:A->B.iscoEq(f,f,id(B))”));

val is_Eqa = Eqa_def|> strip_all_and_imp |> conjE2
                    |> disch_all |> gen_all
                    |> store_as "is_Eqa"

val is_coEqa = coEqa_def|> strip_all_and_imp |> conjE2
                        |> disch_all |> gen_all
                        |> store_as "is_coEqa" 


val Eqa_Mono = prove_store("Eqa_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qsuff_tac
 ‘h = Eqa(f,g,e,e o h) & g' = Eqa(f,g,e,e o h)’
 >-- (strip_tac >> once_arw[] >> rw[]) >> 
 strip_tac (* 2 *)
 >>(irule is_Eqa >> drule Eq_equality >>
     arw[GSYM o_assoc]))
(form_goal
 “!A B f:A->B g:A->B E e:E->A.isEq(f,g,e) ==> Mono(e)”));


val coEqa_Epi = prove_store("coEqa_Epi",
e0
(rpt strip_tac >> rw[Epi_def] >> rpt strip_tac >>
 qsuff_tac
 ‘h = coEqa(f,g,ce,h o ce) & g' = coEqa(f,g,ce,h o ce)’
 >-- (strip_tac >> once_arw[] >> rw[]) >> 
 strip_tac (* 2 *)
 >>(irule is_coEqa >> drule coEq_equality >> arw[o_assoc]))
(form_goal
 “!A B f:A->B g:A->B cE ce:B->cE.
   iscoEq(f,g,ce) ==> Epi(ce)”));

val via_Eq = prove_store("via_Eq",
e0
(rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
 drule Eq_equality >> arw[GSYM o_assoc])
(form_goal
 “!A B f:A->B g:A->B E e:E->A. isEq(f,g,e) ==>!X h:X->A h0. e o h0 = h ==>
  f o h = g o h”));


val via_coEq = prove_store("via_coEq",
e0
(rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
 drule coEq_equality >> arw[o_assoc])
(form_goal
 “!A B f:A->B g:A->B cE ce:B->cE. iscoEq(f,g,ce) ==>
  !X h:B->X h0. h0 o ce = h ==>
  h o f = h o g”));

val Eq_def_imp = Eqa_def |> strip_all_and_imp |> split_assum
                      |> disch “f:A->B o a:X->A = g o a”
                      |>gen_all
                      |> disch_all |> gen_all

val coEq_def_imp = coEqa_def |> strip_all_and_imp |> split_assum
                      |> disch “x:B->X o f:A->B = x o g”
                      |>gen_all
                      |> disch_all |> gen_all

val via_Eq_iff = prove_store("via_Eq_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule via_Eq >> qexistsl_tac [‘E’,‘e’,‘h0’] >> arw[])>>
 drule Eq_def_imp >> first_x_assum drule >> 
 qexists_tac ‘Eqa(f,g,e,h)’ >> 
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B g:A->B E e:E->A. isEq(f,g,e) ==>
  !X h:X->A.(?h0. e o h0 = h) <=>
  f o h = g o h”));


val via_coEq_iff = prove_store("via_coEq_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule via_coEq >> 
      qexistsl_tac [‘cE’,‘ce’,‘h0’] >> arw[])>>
 drule coEq_def_imp >> first_x_assum drule >> 
 qexists_tac ‘coEqa(f,g,ce,h)’ >> 
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B g:A->B cE ce:B->cE. iscoEq(f,g,ce) ==>
  !X h.(?h0:cE->X. h0 o ce = h) <=>
  h o f = h o g”));


val Pa_distr = proved_th $
e0
(rpt strip_tac >> irule is_Pa >>
 rw[GSYM o_assoc,p12_of_Pa])
(form_goal
“!A B X a1:X ->A a2:X->B X0 x:X0->X. Pa(a1,a2) o x = 
Pa(a1 o x,a2 o x) ”)

val Pa_eq_eq = prove_store("Pa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘p1(A,B) o Pa(f1, g1) = p1(A,B) o Pa(f2, g2) &
          p2(A,B) o Pa(f1, g1) = p2(A,B) o Pa(f2, g2)’
 >-- arw[] >>
 fs[p12_of_Pa])
(form_goal
 “!A X f1:X->A f2:X->A B g1:X->B g2:X->B. 
  Pa(f1,g1) = Pa(f2,g2) <=> f1 = f2 & g1 = g2”));


val coPa_eq_eq = prove_store("coPa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘coPa(f1, g1) o i1(A,B) = coPa(f2, g2) o i1(A,B) &
          coPa(f1, g1) o i2(A,B) = coPa(f2, g2) o i2(A,B)’
 >-- arw[] >>
 fs[i12_of_coPa])
(form_goal
 “!A X f1:A ->X f2:A ->X B g1:B ->X  g2:B->X. 
  coPa(f1,g1) = coPa(f2,g2) <=> f1 = f2 & g1 = g2”));

val Thm1_case1_comm_condition_left = prove_store(
"Thm1_case1_comm_condition_left",
e0
(rpt strip_tac >> rw[Pa_distr,idL] >> dimp_tac >> strip_tac
 >-- arw[] >>
 fs[Pa_eq_eq])
(form_goal
 “!B f:N->B g:1->B. Pa(id(N),f) o O = Pa(O,g) <=> f o O = g”));
 
val Thm1_case1_comm_condition_right = prove_store(
"Thm1_case1_comm_condition_right",
e0
(rpt strip_tac >> 
 rw[Pa_distr,o_assoc,p1_of_Pa,idL,idR,Pa_eq_eq])
(form_goal
 “!B f:N->B h:N * B ->B.
 Pa(SUC o p1(N,B),h) o Pa(id(N),f) = Pa(id(N),f) o SUC <=>
 h o Pa(id(N),f) = f o SUC”));

val Thm1_case1_comm_condition = prove_store(
"Thm1_case1_comm_condition",
e0
(rpt strip_tac >> 
 rw[Thm1_case1_comm_condition_left,
 Thm1_case1_comm_condition_right] >> dimp_tac >> strip_tac >> arw[])
(form_goal
 “!B f0:N->B g:1->B h:N * B -> B. f0 o O = g & f0 o SUC = h o Pa(id(N),f0) <=>
 Pa(id(N),f0) o O = Pa(O,g) &
 Pa(SUC o p1(N,B),h) o Pa(id(N),f0) = Pa(id(N),f0) o SUC”));

val uex_tac:tactic = fn (ct,asl,w) =>
    let val th = uex_def w
        val w' = snd $ dest_dimp $ concl th
    in ([(ct,asl,w')],(sing (dimp_mp_r2l th)))
    end

val comm_with_SUC_id = prove_store("comm_with_SUC_id",
e0
(qspecl_then [‘N’,‘SUC’,‘O’] strip_assume_tac Nind_def >>
 rpt strip_tac >>
 qsuff_tac ‘f = Nind(O,SUC) & id(N) = Nind(O,SUC)’
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[idL,idR])
(form_goal
 “!f:N->N. f o O = O & f o SUC = SUC o f ==> f = id(N)”));

val is_Nind = Nind_def |> spec_all |> conjE2
                       |> gen_all
                       |> store_as "is_Nind"

val Thm1_case_1 = prove_store("Thm1_case_1",
e0
(rpt strip_tac >> uex_tac >> 
 abbrev_tac “Nind(Pa(O,g:1->B),Pa(SUC o p1(N,B),h:N * B->B)) = f'” >>
 abbrev_tac “p2(N,B) o f':N->N * B = f” >>
 qby_tac ‘p1(N,B) o f' = id(N)’ >--
 (irule comm_with_SUC_id >> 
  qpick_x_assum ‘Nind(Pa(O, g), Pa(SUC o p1(N, B), h)) = f'’
  (assume_tac o GSYM) >> arw[] >>
  rw[o_assoc,Nind_def,p1_of_Pa] >> 
  rw[GSYM o_assoc,p1_of_Pa]) >>
 qby_tac ‘f' = Pa(id(N),f)’ >--
 (once_rw[to_P_component] >> rw[p12_of_Pa] >> arw[]) >>
 qexists_tac ‘f’ >>
 qby_tac ‘f' o O = Pa(O,g) & 
  f' o SUC = Pa(SUC o p1(N, B), h) o f'’ 
 >-- (qpick_x_assum 
     ‘Nind(Pa(O, g), Pa(SUC o p1(N, B), h)) = f'’
     (assume_tac o GSYM) >> once_arw[] >>
     rw[Nind_def]) >>
 qby_tac ‘f o O = g & f o SUC = h o Pa(id(N), f)’
 >-- (qpick_x_assum ‘p2(N, B) o f' = f’ (assume_tac o GSYM)>>
      once_arw[] >> rw[o_assoc] >> once_arw[] >>
      rw[GSYM o_assoc,p2_of_Pa] >>
      pop_assum (K all_tac) >>
      pop_assum (K all_tac) >> arw[]) >>
 once_arw[] >> rw[] >>
 rpt strip_tac >> 
 qsuff_tac ‘Pa(id(N), f'') = Pa(id(N), f)’ 
 >-- rw[Pa_eq_eq] >>
 qsuff_tac ‘Pa(id(N), f'') = f'’ >-- arw[] >>
 qsuff_tac ‘Pa(id(N), f'') = 
  Nind(Pa(O, g), Pa(SUC o p1(N, B), h))’ >-- arw[] >>
 irule is_Nind >> 
 rw[Pa_distr,p1_of_Pa,o_assoc,idL,idR] >> once_arw[] >>
 rw[])
(form_goal
 “!B g:1->B h:N * B -> B. ?!f:N->B. f o O = g & f o SUC = h o Pa(id(N),f)”));

val Tp1_ex = prove_store("Tp1_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(f o p1(A,1))’ >> rw[])
(form_goal
 “!A B f:A->B. ?tpf:1->Exp(A,B).Tp(f o p1(A,1)) = tpf”)
);

val Tp1_def = Tp1_ex |> spec_all |> ex2fsym0 "Tp1" ["f"] 
                     |> gen_all |> store_as "Tp1_def"; 

fun Tp1 f = mk_fun "Tp1" [f] 


val Tp0_ex = prove_store("Tp0_ex",
e0
(rpt strip_tac >> qexists_tac ‘Ev(X,Y) o Pa(id(X),f o To1(X))’ >>
 rw[])
(form_goal
 “!X Y f:1->Exp(X,Y).?tp0:X->Y. Ev(X,Y) o Pa(id(X),f o To1(X)) = tp0”));

val Tp0_def = 
    Tp0_ex |> spec_all |> ex2fsym0 "Tp0" ["f"] |> gen_all
           |> store_as "Tp0_def"


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
 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))

val rflip_tac =
fconv_tac 
 (rand_fconv no_conv 
 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))


val Tp1_Tp0_inv = prove_store("Tp1_Tp0_inv",
e0
(rpt strip_tac >> rw[GSYM Tp1_def,GSYM Tp0_def] >>
 fconv_tac (rewr_fconv (eq_sym "ar")) >> irule is_Tp >>
 rw[o_assoc,Pa_distr,idL] >>
 once_rw[To1_def] >> rw[])
(form_goal
 “!X Y f:1-> Exp(X,Y). Tp1(Tp0(f)) = f”));



val Ev_of_Tp_el = prove_store("Ev_of_Tp_el",
e0
(rpt strip_tac >>
 assume_tac Ev_of_Tp >> 
 first_x_assum (qspecl_then [‘A’,‘B’,‘X’,‘f’] assume_tac) >>
 qby_tac 
 ‘Pa(a, Tp(f) o x) = Pa(p1(A, X), Tp(f) o p2(A, X)) o Pa(a,x)’ >--
 (irule to_P_eq >> rw[p12_of_Pa] >> 
  rw[p12_of_Pa,GSYM o_assoc] >> rw[o_assoc,p12_of_Pa]) >>
 arw[GSYM o_assoc])
(form_goal
 “!A B X f:A * X ->B P a:P->A x: P ->X. 
  Ev(A,B) o Pa(a, Tp(f) o x) = f o Pa(a,x)”));

val Tp0_Tp1_inv = prove_store("Tp0_Tp1_inv",
e0
(rpt strip_tac >> rw[GSYM Tp1_def,GSYM Tp0_def] >>
 rw[Ev_of_Tp_el,o_assoc,p1_of_Pa,idR])
(form_goal
 “!X Y f:X->Y. Tp0(Tp1(f)) = f”));

val Thm1_comm_eq_left = prove_store(
"Thm1_comm_eq_left",
e0
(rpt strip_tac >> 
 qby_tac ‘Pa(p1(A,1), Tp(f) o O o p2(A,1)) = 
 Pa(p1(A,N),Tp(f) o p2(A,N)) o Pa(p1(A,1),O o p2(A,1))’
 >-- rw[Pa_distr,o_assoc,p12_of_Pa] >>
 dimp_tac >> strip_tac (* 2 *) >--
 (qsuff_tac ‘f o Pa(p1(A, 1), O o p2(A, 1)) = 
                 Ev(A,B) o Pa(p1(A,1),(Tp(f) o O) o p2(A,1)) &
             g o p1(A, 1) = 
                 Ev(A,B) o Pa(p1(A,1),Tp1(g) o p2(A,1))’
 >-- (strip_tac >> fs[]) >>
 strip_tac (* 2 *)
 >-- (rw[o_assoc] >> arw[] >>
      rw[GSYM o_assoc,Ev_of_Tp]) >>
 rw[GSYM Tp1_def,Ev_of_Tp]) >>
 rw[GSYM Tp1_def] >> irule is_Tp >> 
 rw[o_assoc] >> arw[GSYM o_assoc,Ev_of_Tp])
(form_goal
 “!A B f: A * N ->B g:A->B. 
  Tp(f) o O = Tp1(g) <=> f o Pa(p1(A,1),O o p2(A,1)) = g o p1(A,1)”));

val Pa_p1_p2 = prove_store("Pa_p1_p2",
e0
(rpt strip_tac >>
 fconv_tac (rewr_fconv (eq_sym "ar")) >>
 irule is_Pa >> rw[idR])
(form_goal
 “!A B. Pa(p1(A,B),p2(A,B)) = id(A * B)”));

val flip_tac = 
fconv_tac (rewr_fconv (eq_sym "ar"));

val Thm1_comm_eq_right = prove_store("Thm1_comm_eq_right",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘Tp(h o l) o Pa(id(N),Tp(f)) = Tp(h o Pa(id(A * N),f)) & 
  Tp(f o Pa(p1(A,N), SUC o p2(A,N))) = Tp(f) o SUC’
 >-- (strip_tac >> dimp_tac >> strip_tac (* 2 *)
      >-- arw[] >>
      irule $ iffLR Tp_eq >> arw[] >>
      qpick_x_assum
      ‘Tp((h o l)) o Pa(id(N), Tp(f)) =
       Tp(h o Pa(id(A * N), f))’
      (assume_tac o GSYM) >> arw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Tp >> 
  qby_tac
  ‘Pa(p1(A, N), (Tp((h o l)) o Pa(id(N), Tp(f))) o p2(A, N))=
   Pa(p1(A,N * Exp(A,B)), Tp(h o l) o p2(A,N * Exp(A,B))) o 
   Pa(p1(A,N),Pa(id(N),Tp(f)) o p2(A,N))’ >-- 
  (irule to_P_eq >> 
   rw[p12_of_Pa,o_assoc] >> rw[GSYM o_assoc,p12_of_Pa] >>
   rw[p12_of_Pa,o_assoc]) >>
  once_arw[] >> rw[GSYM o_assoc,Ev_of_Tp] >>
  rw[o_assoc] >>
  qsuff_tac
  ‘l o Pa(p1(A, N), Pa(id(N), Tp(f)) o p2(A, N)) = 
   Pa(id(A * N), f)’ >--
  (strip_tac >> arw[]) >>
  irule to_P_eq >> rw[p12_of_Pa] >>
  pop_assum (K all_tac) >>
  pop_assum (assume_tac o GSYM) >> arw[] >>
  rw[p12_of_Pa,GSYM o_assoc] >>
  rw[o_assoc,p12_of_Pa,Pa_distr,Ev_of_Tp,idL,idR] >>
  rw[Pa_p1_p2]) >>
 flip_tac >> irule is_Tp >>
 qby_tac
 ‘Pa(p1(A, N), (Tp(f) o SUC) o p2(A, N)) = 
  Pa(p1(A, N), Tp(f) o p2(A,N)) o Pa(p1(A,N),SUC o p2(A,N))’
 >-- (irule to_P_eq >> rw[GSYM o_assoc,p12_of_Pa] >>
      rw[o_assoc,p12_of_Pa]) >>
 arw[GSYM o_assoc,Ev_of_Tp]
 )
(form_goal
 “!A B f:A * N ->B h: (A * N) * B ->B l . 
Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l
 ==>
 (h o Pa(id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N)) <=>
 Tp(h o l) o Pa(id(N),Tp(f)) = Tp(f) o SUC)”));

val Thm1_comm_eq_condition = prove_store(
"Thm1_comm_eq_condition",
e0
(rpt strip_tac >> drule Thm1_comm_eq_right >>
 once_arw[] >> rw[GSYM Thm1_comm_eq_left])
(form_goal
 “!A B f: A * N ->B g:A->B h: (A * N) * B -> B l.
 Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l ==>
 (f o Pa(p1(A,1),O o p2(A,1)) = g o p1(A,1) & 
  h o Pa(id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N)) <=>
  Tp(f) o O = Tp1(g) & Tp(h o l) o Pa(id(N),Tp(f)) = Tp(f) o SUC)
  ”));


val Thm1 = prove_store("Thm1",
e0
(rpt strip_tac >>
 uex_tac >>
 abbrev_tac “Tp(g:A->B o p1(A,1)) = g'” >>
 abbrev_tac “Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l” >>
 abbrev_tac “Tp(h:(A * N) * B->B o l:A * N * Exp(A,B) -> (A * N) * B) = h'” >>
 qspecl_then [‘Exp(A,B)’,‘g'’,‘h'’] (assume_tac o uex_expand) Thm1_case_1 >>
 pop_assum (x_choose_then "fb" strip_assume_tac) >>
 qabbrev_tac ‘Ev(A,B) o Pa(p1(A,N),fb o p2(A,N)) = f’ >>
 qby_tac ‘Tp(f) = fb’ >--
 (flip_tac >> irule is_Tp >> arw[]) >>
 qexists_tac ‘f’ >>
 qspecl_then [‘A’,‘B’,‘f’,‘g’] assume_tac
 Thm1_comm_eq_condition >>
 first_x_assum drule >> once_arw[] >>
 qby_tac
 ‘Tp(f) o O = Tp1(g) & 
  Tp((h o l)) o Pa(id(N), Tp(f)) = Tp(f) o SUC’
 >-- arw[GSYM Tp1_def] >>
 arw[] >> strip_tac >>
 qspecl_then [‘A’,‘B’,‘f'’,‘g’] assume_tac
 Thm1_comm_eq_condition >>
 first_x_assum drule >> once_arw[] >>
 rpt strip_tac >>
 irule $ iffLR Tp_eq >> arw[] >> first_x_assum irule >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 qpick_x_assum ‘Tp(f') o O = Tp1(g)’ 
 (assume_tac o GSYM) >> arw[] >> fs[GSYM Tp1_def])
(form_goal
 “!A B g:A->B h:(A * N) * B ->B. 
 ?!f:A * N ->B.
   f o Pa(p1(A,1),O o p2(A,1)) = g o p1(A,1) & 
  h o Pa(id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N))”));

val PRE_ex = 
 Thm1_case_1 |> specl (List.map rastt ["N","O","p1(N,N)"])
             |> uex_expand |> rewr_rule[p1_of_Pa]
             |> store_as "PRE_ex";

val PRE_def = PRE_ex |> ex2fsym0 "PRE" []
                     |> store_as "PRE_def";


val rfs = rev_full_simp_tac

val post_inv_Mono = prove_store("post_inv_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qby_tac
 ‘i o m o g = i o m o h’ >-- arw[] >>
 rfs[GSYM o_assoc] >> fs[idL])
(form_goal
 “!A B m:A->B i:B->A. i o m = id(A) ==> Mono(m)”));


val pre_inv_Epi = prove_store("pre_inv_Epi",
e0
(rpt strip_tac >> rw[Epi_def] >> rpt strip_tac >>
 qby_tac
 ‘g o e o i = h o e o i’ >-- arw[GSYM o_assoc] >>
 rfs[idR])
(form_goal
 “!A B e:A->B i:B->A. e o i = id(B) ==> Epi(e)”));

val _ = new_pred "Iso" [("f",ar_sort (mk_ob "A") (mk_ob "B"))]

val Iso_def = store_ax("Iso_def",
“!A B f:A->B. Iso(f) <=> ?f':B->A. f' o f = id(A) & f o f' = id(B)”);

val to_zero_Iso = prove_store("to_zero_Iso",
e0
(rpt strip_tac >> rw[Iso_def] >>
 drule to_zero_zero >> fs[is0_def] >> 
 first_assum 
  (qspecl_then [‘X’] $ strip_assume_tac o uex_expand)>>
 first_assum 
  (qspecl_then [‘A’] $ strip_assume_tac o uex_expand) >>
 last_assum 
  (qspecl_then [‘X’] $ strip_assume_tac o uex_expand) >>
 last_assum 
  (qspecl_then [‘A’] $ strip_assume_tac o uex_expand) >>
 qexists_tac ‘f''''’ >>
 once_arw[] >> rw[])
(form_goal
 “!X. is0(X) ==> !A f:A->X. Iso(f)”));

val Mono_Epi_Iso = prove_store("Mono_Epi_Iso",
e0
(rpt strip_tac >> 
 cases_on “is0(B)” >--
 (drule to_zero_Iso >> arw[]) >>
 drule no_Epi_from_zero >> first_x_assum drule >>
 drule NONZERO_EL >> pop_assum strip_assume_tac >>
 qspecl_then [‘A’,‘B’,‘x’,‘a’] strip_assume_tac AC >>
 rw[Iso_def] >> drule Mono_pinv_post_inv >>
 first_x_assum drule >>
 drule Epi_pinv_pre_inv >> first_x_assum drule >>
 qexists_tac ‘g’ >> arw[])
(form_goal
 “!A B a:A->B. Mono(a) & Epi(a) ==> Iso(a)”));

val DISTI_endo_2 = prove_store("DISTI_endo_2",
e0
(ccontra_tac >> fs[coPa_eq_eq] >>
 fs[i1_ne_i2_1])
(form_goal
 “~(coPa(i1(1,1),i2(1,1)) = coPa(i2(1,1),i1(1,1)))”))

val Thm2_1 = prove_store("Thm2_1",
e0
(strip_tac >> ccontra_tac >>
 qsuff_tac ‘!X t:X->X. t = id(X)’
 >-- (strip_tac >> 
      first_assum 
      (qspecl_then [‘1+1’,‘coPa(i1(1,1),i2(1,1))’] 
      assume_tac) >>
      first_x_assum 
      (qspecl_then [‘1+1’,‘coPa(i2(1,1),i1(1,1))’] 
      assume_tac) >> 
      qby_tac
      ‘coPa(i1(1,1),i2(1,1)) = coPa(i2(1,1),i1(1,1))’
      >-- arw[] >>
      fs[DISTI_endo_2]) >>
 rpt strip_tac >> irule FUN_EXT >> strip_tac >> 
 qby_tac ‘SUC o O = O’ >--
 (qby_tac ‘PRE o SUC o n = PRE o O’ >-- arw[] >>
  assume_tac $ conjE1 PRE_def >> 
  fs[GSYM o_assoc] >> fs[idL]) >>
 qspecl_then [‘X’,‘t’,‘a’] (strip_assume_tac o conjE1) 
 Nind_def >>
 rw[idL] >>
 qby_tac ‘t o a = t o Nind(a, t) o O’ 
 >-- arw[] >>
 fs[GSYM o_assoc] >> 
 qpick_x_assum ‘Nind(a, t) o SUC = t o Nind(a, t)’
 (assume_tac o GSYM) >> arw[] >>
 rw[o_assoc] >> arw[])
(form_goal
 “!n:1->N. ~(SUC o n = O)”));


val Thm2_2 = prove_store("Thm2_2",
e0
(irule post_inv_Mono >>
 qexists_tac ‘PRE’ >> rw[PRE_def])
(form_goal
 “Mono(SUC)”));

val Thm2_3_alt' = prove_store("Thm2_3_alt'",
e0
(rpt strip_tac >> irule Mono_Epi_Iso >>
 arw[] >> irule pre_inv_Epi >>
 qexists_tac ‘Nind(z,s)’ >> irule comm_with_SUC_id >>
 rw[o_assoc,Nind_def] >> arw[GSYM o_assoc])
(form_goal
 “!A a:A->N. Mono(a) ==>
  !s:A->A z:1->A.a o s = SUC o a & a o z = O ==>
  Iso(a)”));

val _ = new_pred "isPb"
  [("f",ar_sort (mk_ob "X") (mk_ob "Z")),
   ("g",ar_sort (mk_ob "Y") (mk_ob "Z")),
   ("p",ar_sort (mk_ob "P") (mk_ob "X")),
   ("q",ar_sort (mk_ob "P") (mk_ob "Y"))];

val isPb_def = store_ax("isPb_def",
“!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y.
 isPb(f, g, p, q) <=> f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v”);

val isPb_expand = isPb_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : A -> P. p:P->X o a = u & q:P->Y o a = v”) |> store_as "isPb_expand";

val Eqa_eqn = Eqa_def |> spec_all |> undisch |> conjE1
                      |> disch_all |> gen_all
                      |> store_as "Eqa_eqn";


val coEqa_eqn = coEqa_def |> spec_all |> undisch |> conjE1
                      |> disch_all |> gen_all
                      |> store_as "coEqa_eqn";

val isPb_ex = prove_store("isPb_ex",
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
 drule Eqa_Mono >> fs[Mono_def] >>
 first_x_assum irule >>
 irule to_P_eq >> arw[p12_of_Pa])
(form_goal
 “!X Z f:X->Z Y g:Y->Z. ?P p:P->X q. isPb(f,g,p,q)”));

val Pb_Mono_Mono = prove_store("Pb_Mono_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 drule $ iffLR isPb_expand >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘f o p o h = g o q o h’ >--
 (strip_tac >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘g' = a & h = a’ >-- 
 (strip_tac >> arw[]) >> strip_tac >> 
 first_x_assum irule >> arw[] >>
 fs[Mono_def] >> first_x_assum irule >> 
 qpick_x_assum ‘f o p = g o q’ (assume_tac o GSYM) >>
 arw[GSYM o_assoc] >> arw[o_assoc]) >>
 arw[GSYM o_assoc])
(form_goal
 “!X Z f:X->Z Y g:Y->Z P p:P->X q:P->Y. 
  isPb(f,g,p,q) ==> Mono(g) ==> Mono(p)”));

val surj_Epi = prove_store("surj_Epi",
e0
(rpt strip_tac >> rw[Epi_def] >> rpt strip_tac >>
 irule FUN_EXT >> strip_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[GSYM o_assoc])
(form_goal
 “!A B f:A->B. (!b:1->B.?b0:1->A. f o b0 = b) ==> Epi(f)”));

fun qgenl l th = 
    case l of [] => th
             |h :: t => qgen h (qgenl t th)

val isPb_equality = 
    isPb_expand |> spec_all |> iffLR
                |> undisch |> conjE1
                |> disch_all 
                |> qgenl [‘X’,‘Z’,‘f’,‘Y’,‘g’,‘P’,‘p’,‘q’]
                |> store_as "isPb_equality"

val ind_fac = prove_store("ind_fac",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘N’,‘SUC o a’,‘A’,‘a’] strip_assume_tac 
 isPb_ex>> 
 drule isPb_equality >> 
 qsuff_tac ‘Iso(p)’ 
 >-- (rw[Iso_def] >> strip_tac >> qexists_tac ‘q o f'’ >>
      qpick_x_assum ‘(SUC o a) o p = a o q’ 
       (assume_tac o GSYM) >>
      arw[GSYM o_assoc] >> arw[o_assoc,idR]) >>
 irule Mono_Epi_Iso >> strip_tac (* 2 *)
 >-- (irule surj_Epi >> strip_tac >>
      qby_tac ‘?sn0. SUC o a o b = a o sn0’
      >-- (first_x_assum irule >> qexists_tac ‘b’ >> rw[]) >>
      drule $ iffLR isPb_expand >> 
      pop_assum strip_assume_tac >>
      fs[GSYM o_assoc] >> first_x_assum drule >>
      pop_assum strip_assume_tac >>
      qexists_tac ‘a'’ >> arw[]) >>
 irule Pb_Mono_Mono >>
 qexistsl_tac [‘A’,‘q’,‘N’,‘SUC o a’,‘a’] >> arw[])
(form_goal
 “!A a:A->N. Mono(a) & 
  (!n:1->N. (?n0:1->A. n = a o n0) ==> (?sn0. SUC o n = a o sn0)) ==> ?t:A->A. a o t = SUC o a”));

val Thm2_3' = prove_store("Thm2_3'",
e0
(rpt strip_tac >> irule Thm2_3_alt' >>
 arw[] >> strip_tac (* 2 *)
 >-- (qexists_tac ‘O0’ >> rw[]) >>
 irule ind_fac >> arw[])
(form_goal
 “!A a:A->N. (Mono(a) & (!n:1->N. (?n0:1->A. n = a o n0) ==>
 ?sn0. SUC o n = a o sn0) & ?O0:1->A. O = a o O0) ==> Iso(a)”));

val coEq_of_equal_post_inv = prove_store(
"coEq_of_equal_post_inv",
e0
(rpt strip_tac >> 
 qby_tac ‘iscoEq(f, f, e) & id(B) o f = id(B) o f’
 >-- arw[] >>
 drule coEqa_def >> 
 qexists_tac ‘coEqa(f,f,e,id(B))’ >> 
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B cE e:B->cE. iscoEq(f,f,e) ==>
  ?e':cE->B. e' o e = id(B)”));

val Thm3_A_zero_I_zero = prove_store(
"Thm3_A_zero_I_zero",
e0
(rpt strip_tac >> 
 qsuff_tac ‘~(?t:1->I0.T)’ >--
 (strip_tac >> ccontra_tac >> drule NONZERO_EL >> rfs[]) >>
 ccontra_tac >> 
 pop_assum strip_assume_tac >>
 qsuff_tac ‘i1(B,B) o q' o t = i2(B,B) o q' o t’ >--
 rw[i1_i2_disjoint] >>
 drule Eq_equality >>
 qby_tac ‘i1(B, B) o f = i2(B, B) o f’ >--
 (fs[is0_expand] >>
 first_x_assum (qspecl_then [‘B +B’] strip_assume_tac) >>
 fs[]) >> fs[] >>
 drule coEq_of_equal_post_inv >> 
 pop_assum strip_assume_tac >>
 qby_tac ‘e' o (k' o i1(B, B)) o q' =
          e' o (k' o i2(B, B)) o q'’ >-- arw[] >>
 rfs[GSYM o_assoc,idL])
(form_goal
 “!A. is0(A) ==>
  !B f:A->B R' k':B + B -> R'.
  iscoEq(i1(B,B) o f,i2(B,B) o f,k') ==>
  !I0 q':I0->B. isEq(k' o i1(B,B),k' o i2(B,B),q') ==>
  is0(I0)”));

val Thm3_case_zero = prove_store("Thm3_case_zero",
e0
(rpt strip_tac >>
 irule to_zero_Iso >> irule Thm3_A_zero_I_zero >>
 qexistsl_tac [‘A’,‘B’,‘f’,‘q'’,‘R'’,‘k'’] >> arw[])
(form_goal
 “!A B f:A->B. is0(A) ==>
 !R' k':B + B ->R'. iscoEq(i1(B,B) o f, i2(B,B) o f,k') ==>
 !I0 q':I0->B. isEq(k' o i1(B,B), k' o i2(B,B),q') ==> 
 !R k:R->A * A. isEq(f o p1(A,A),f o p2(A,A),k) ==>
 !I' q:A->I'.iscoEq(p1(A,A) o k, p2(A,A) o k,q) ==>
 !h:I'->I0. q' o h o q = f ==> Iso(h)”));


val o_Mono_imp_Mono = prove_store("o_Mono_imp_Mono",
e0
(rpt strip_tac >> fs[Mono_def] >> rpt strip_tac >> 
 first_x_assum irule >> arw[o_assoc])
(form_goal “!A B f:A->B C m:B->C. Mono(m o f) ==> Mono(f)”)
);


val o_Epi_imp_Epi = prove_store("o_Epi_imp_Epi",
e0
(rpt strip_tac >> fs[Epi_def] >> rpt strip_tac >> 
 first_x_assum irule >> arw[GSYM o_assoc])
(form_goal “!A B f:A->B C e:C->A. Epi(f o e) ==> Epi(f)”)
);

val Thm3_case_non_zero = prove_store("Thm3_case_non_zero",
e0
(rpt strip_tac >> irule Mono_Epi_Iso >> 
 drule Eqa_Mono >> rev_drule Eqa_Mono >>
 drule coEqa_Epi >> rev_drule coEqa_Epi >>
 qby_tac ‘~(is0(I0))’ >--
 (ccontra_tac >> 
  qsuff_tac ‘is0(A)’ >-- fs[] >>
  match_mp_tac to_zero_zero (* TODO: find out why match mp can do but irule cannot *) >>
  qexistsl_tac [‘I0’,‘h o q’] >> arw[]) >>
 strip_tac (* 2 *) >--
 (qsuff_tac ‘Epi(h o q)’ >-- 
  (strip_tac >> drule o_Epi_imp_Epi >> arw[]) >>
  rw[Epi_def] >> rpt strip_tac >>
 drule Mono_no_zero_post_inv >> first_x_assum drule >>
 pop_assum (x_choose_then "qi" assume_tac) >>
 qby_tac ‘?w.w o k' = coPa(h' o qi,g o qi)’ >--
 (irule $ iffRL via_coEq_iff >>
  qexistsl_tac [‘A’,‘i1(B, B) o f’,‘i2(B, B) o f’] >>
  arw[i12_of_coPa,GSYM o_assoc] >> 
  qsuff_tac
  ‘(h' o qi) o q' o h o q = h' o (qi o q') o h o q &
   (g o qi) o q' o h o q = g o (qi o q') o h o q’
  >--(strip_tac >> rfs[idL]) >>
  rw[o_assoc]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘coPa(h' o qi,g o qi) o i1(B,B) o q' = h' &
 coPa(h' o qi,g o qi) o i2(B,B) o q' = g &
 coPa(h' o qi,g o qi) o i1(B,B) o q' = 
 coPa(h' o qi,g o qi) o i2(B,B) o q'’ >--
 (strip_tac >> rfs[]) >> rpt strip_tac (* 3 *) >--
 (arw[i1_of_coPa,GSYM o_assoc] >> arw[o_assoc,idR]) >--
 (arw[i2_of_coPa,GSYM o_assoc] >> arw[o_assoc,idR]) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 rw[o_assoc] >> rev_drule Eq_equality >>
 fs[o_assoc]) >>
 qsuff_tac ‘Mono(q' o h)’
 >-- (strip_tac >> match_mp_tac o_Mono_imp_Mono >>
      qexistsl_tac [‘B’,‘q'’] >> arw[]) >>
 qby_tac ‘?t.q o t = id(I')’ >--
 (irule Epi_no_zero_pre_inv >> arw[]) >>
 pop_assum strip_assume_tac >> 
 rw[Mono_def] >> rpt strip_tac >>
 qby_tac ‘?w.k o w = Pa(t o h',t o g)’ >--
 (irule $ iffRL via_Eq_iff >> 
  qexistsl_tac [‘B’,‘f o p1(A, A)’,‘f o p2(A, A)’] >>
  arw[o_assoc,p12_of_Pa] >> 
  qby_tac
  ‘(q' o h o q) o t o h' = q' o h o (q o t) o h' & 
   (q' o h o q) o t o g = q' o h o (q o t) o g’ >--
  rw[o_assoc] >>
  qpick_x_assum ‘q' o h o q = f’ (assume_tac o GSYM) >>
  arw[] >> fs[idR,idL,o_assoc]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac ‘q o p1(A,A) o Pa(t o h', t o g) = h' &
            q o p2(A,A) o Pa(t o h', t o g) = g &
            q o p1(A,A) o Pa(t o h', t o g) = 
            q o p2(A,A) o Pa(t o h', t o g)’ >--
 (rpt strip_tac >> rfs[]) >> rpt strip_tac (* 3 *)
 >-- (arw[p1_of_Pa] >> arw[GSYM o_assoc,idL])
 >-- (arw[p2_of_Pa] >> arw[GSYM o_assoc,idL]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 drule coEq_equality >> fs[GSYM o_assoc])
(form_goal
 “!A B f:A->B. ~(is0(A)) ==>
 !R' k':B + B ->R'. iscoEq(i1(B,B) o f, i2(B,B) o f,k') ==>
 !I0 q':I0->B. isEq(k' o i1(B,B), k' o i2(B,B),q') ==> 
 !R k:R->A * A. isEq(f o p1(A,A),f o p2(A,A),k) ==>
 !I' q:A->I'.iscoEq(p1(A,A) o k, p2(A,A) o k,q) ==>
 !h:I'->I0. q' o h o q = f ==> Iso(h)”));


val unique_h_lemma = prove_store("unique_h_lemma",
e0
(rpt strip_tac >> qexists_tac ‘h’ >> strip_tac >>
 dimp_tac >> strip_tac >> rfs[])
(form_goal 
“!A B f:A->B C q:A->C D g:D->B k:A->D h:C->D.
 (!k'. g o k' = f <=> k' = k) &
 (!h'. h' o q = k <=> h' = h) ==>
 (?h:C->D. !h0. g o h0 o q = f <=> h0 = h)”));


val Eqa_def_alt = prove_store("Eqa_def_alt",
e0
(rpt strip_tac >> drule Eq_def_imp >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 dimp_tac >> strip_tac (* 2 *) >--
 (first_x_assum irule >> flip_tac >> 
 first_x_assum accept_tac) >>
 once_arw[] >> rw[] )
(form_goal
 “!A B f:A->B g:A->B E e:E->A.
 isEq(f,g,e) ==>
 !X a:X->A. f o a = g o a ==> 
 !a0:X->E. e o a0 = a <=> a0 = Eqa(f,g,e,a) ”));


val coEqa_def_alt = prove_store("coEqa_def_alt",
e0
(rpt strip_tac >> drule coEq_def_imp >> 
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 dimp_tac >> strip_tac (* 2 *) >--
 (first_x_assum irule >> flip_tac >> 
 first_x_assum accept_tac) >>
 once_arw[] >> rw[] )
(form_goal
 “!A B f:A->B g:A->B cE ce:B->cE.
 iscoEq(f,g,ce) ==>
 !X x:B->X. x o f = x o g ==> 
 !x0:cE->X. x0 o ce = x <=> x0 = coEqa(f,g,ce,x) ”));

val Thm3_h_exists = prove_store("Thm3_h_exists",
e0
(rpt strip_tac >> match_mp_tac unique_h_lemma >>
 qexistsl_tac
 [‘Eqa(k' o i1(B,B),k' o i2(B,B),q',f)’,
  ‘coEqa(p1(A,A) o k,p2(A,A) o k,q,
        Eqa(k' o i1(B,B),k' o i2(B,B),q',f))’] >>
 rpt strip_tac 
 >-- (rev_drule Eqa_def_alt >>
      first_x_assum irule >>
      rev_drule coEq_equality >> fs[o_assoc]) >>
 drule coEqa_def_alt >> first_x_assum irule >>
 drule Eq_equality >>
 rev_drule Eqa_Mono >> fs[Mono_def] >>
 first_x_assum irule >>
 qsuff_tac
 ‘q' o Eqa((k' o i1(B, B)), (k' o i2(B, B)), q', f) = f’ 
 >-- (strip_tac >> arw[GSYM o_assoc]) >>
 rev_drule Eqa_def_alt >> 
 first_x_assum (qspecl_then [‘A’,‘f’] assume_tac) >> 
 rev_drule coEq_equality >> fs[o_assoc])
(form_goal 
“!A B f:A->B.
 !R' k':B + B->R'. iscoEq(i1(B,B) o f,i2(B,B) o f,k') ==>
 !I0 q':I0->B. isEq(k' o i1(B,B), k' o i2(B,B),q') ==>
 !R k:R->A * A. isEq(f o p1(A,A),f o p2(A,A),k) ==>
 !I' q:A->I'.iscoEq(p1(A,A) o k, p2(A,A) o k,q) ==>
 ?h:I' ->I0.!h0. q' o h0 o q = f <=> h0 = h”));

val Thm3_without_assume_exists = prove_store(
"Thm3_without_assume_exists",
e0
(rpt strip_tac >>
 drule Thm3_h_exists >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘h’ >>
 qby_tac ‘q' o h o q = f’ >-- arw[] >>
 cases_on “is0(A)” (* 3 *) >-- 
 (qspecl_then [‘A’,‘B’,‘f’] assume_tac Thm3_case_zero >>
  first_x_assum drule >> strip_tac >> 
  first_x_assum drule >> first_x_assum drule >>
  first_x_assum drule >> first_x_assum drule >>
  dimp_tac >> strip_tac >> rfs[] >> 
  first_x_assum irule >> 
  first_x_assum (qspecl_then [‘h’] assume_tac) >>
  fs[]) >>
 qspecl_then [‘A’,‘B’,‘f’] assume_tac Thm3_case_non_zero >>
  first_x_assum drule >> strip_tac >> 
  first_x_assum drule >> first_x_assum drule >>
  first_x_assum drule >> first_x_assum drule >>
  dimp_tac >> strip_tac >> rfs[] >> 
  first_x_assum irule >> 
  first_x_assum (qspecl_then [‘h’] assume_tac) >>
  fs[])
(form_goal
 “!A B f:A->B.
 !R' k':B + B->R'. iscoEq(i1(B,B) o f,i2(B,B) o f,k') ==>
 !I0 q':I0->B. isEq(k' o i1(B,B), k' o i2(B,B),q') ==>
 !R k:R->A * A. isEq(f o p1(A,A),f o p2(A,A),k) ==>
 !I' q:A->I'.iscoEq(p1(A,A) o k, p2(A,A) o k,q) ==>
 ?h:I' ->I0.!h0. q' o h0 o q = f & Iso(h) <=> h0 = h”));

val Iso_Mono = prove_store("Iso_Mono",
e0
(rw[Iso_def,Mono_def] >> rpt strip_tac >> 
 qsuff_tac ‘f' o f o g = f' o f o h’ 
 >-- (arw[GSYM o_assoc,idL]) >> arw[])
(form_goal “!A B f:A->B.Iso(f) ==> Mono(f)”));


val o_Mono_Mono = prove_store("o_Mono_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 fs[o_assoc,Mono_def] >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal 
“!A B f:A->B. Mono(f) ==> !C g:B->C. Mono(g) ==>
 Mono(g o f)”));

val Mono_o_Iso_Mono = prove_store("Mono_o_Iso_Mono",
e0
(rpt strip_tac >> irule o_Mono_Mono >> 
 drule Iso_Mono >> arw_tac[])
(form_goal “!X A i:X->A.Iso(i) ==> !B f:A->B. Mono(f) ==> Mono(f o i)”));

val Mono_Epi_fac = prove_store("Mono_Epi_fac",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘B + B’,‘i1(B,B) o f’,‘i2(B,B) o f’]
 (x_choosel_then ["R'","k'"] assume_tac) iscoEq_ex >>
 qspecl_then [‘B’,‘R'’,‘k' o i1(B,B)’,‘k' o i2(B,B)’]
 (x_choosel_then ["I0","q'"] assume_tac) isEq_ex >> 
 qspecl_then [‘A * A’,‘B’,‘f o p1(A,A)’,‘f o p2(A,A)’]
 (x_choosel_then ["R","k"] assume_tac) isEq_ex >>
 qspecl_then [‘R’,‘A’,‘p1(A,A) o k’,‘p2(A,A) o k’]
 (x_choosel_then ["I'","q"] assume_tac) iscoEq_ex >> 
 drule Thm3_without_assume_exists >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qby_tac ‘q' o h o q = f & Iso(h)’ >-- arw[] >>
 rev_drule Eqa_Mono >> drule coEqa_Epi >>
 qexistsl_tac [‘I'’,‘q' o h’,‘q’] >> arw[o_assoc] >>
 irule Mono_o_Iso_Mono >> arw[])
(form_goal
 “!A B f:A->B. ?X m:X->B e:A->X. Epi(e) & Mono(m) & f = m o e”)); 

val Epi_surj = prove_store("Epi_surj",
e0
(rpt strip_tac >>
 drule Epi_has_section >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘s0 o b’ >> fs[GSYM o_assoc,idL])
(form_goal “!A B f:A->B. Epi(f) ==> (!b:1->B. ?b0:1->A. f o b0 = b)”));

val Thm4 = prove_store("Thm4",
e0
(rpt strip_tac >> 
 abbrev_tac 
 “Ev(X,1+1) o Pa(p1(X,J),ss:J->Exp(X,1+1) o p2(X,J)) = s0” >>
 abbrev_tac “i2(1,1) o To1(X * J) = i2t” >>
 qspecl_then [‘X * J’,‘1 + 1’,‘s0’,‘i2t’]
 (x_choosel_then ["E","k"] assume_tac) isEq_ex >>
 qspecl_then [‘E’,‘X’,‘p1(X,J) o k’]
 (x_choosel_then ["U","a","q"] strip_assume_tac)
 Mono_Epi_fac >> qexistsl_tac [‘U’,‘a’] >> arw[] >> 
 strip_tac >> 
 qby_tac ‘!j:1->J. Ev(X,1+1) o Pa(x,ss o j) = i2(1,1) <=>
 s0 o Pa(x,j) = i2(1,1)’ >--
 (strip_tac >>
  qsuff_tac ‘Ev(X,1+1) o Pa(x,ss o j) = s0 o Pa(x,j)’
  >-- (strip_tac >> arw[]) >>
  last_x_assum (assume_tac o GSYM) >> arw[o_assoc] >>
  qsuff_tac 
  ‘Pa(x, ss o j) = Pa(p1(X, J), (ss o p2(X, J))) o Pa(x, j)’
  >-- (strip_tac >> arw[]) >>
  irule to_P_eq >> rw[p12_of_Pa] >>
  rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc, p12_of_Pa]) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *) >--
 (drule Epi_surj >> 
 first_x_assum 
 (qspecl_then [‘x0’] $ x_choose_then "xb" assume_tac) >>
 qexists_tac ‘p2(X,J) o k o xb’ >>
 qby_tac ‘Pa(x,p2(X,J) o k o xb) = k o xb’ >--
 (irule to_P_eq >> rw[p12_of_Pa] >> arw[GSYM o_assoc] >>
  arw[o_assoc]) >>
 drule Eq_equality >>
 qby_tac ‘i2t o k o xb = i2(1,1)’ >--
 (qpick_x_assum ‘i2(1, 1) o To1(X * J) = i2t’
  (assume_tac o GSYM) >> once_arw[] >>
  rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) >>
 arw[]>> arw[GSYM o_assoc] >> arw[o_assoc]) >>
 qexists_tac ‘q o Eqa(s0,i2t,k,Pa(x,j))’ >>
 qpick_x_assum ‘p1(X, J) o k = a o q’ (assume_tac o GSYM) >>
 arw[GSYM o_assoc] >> 
 qby_tac ‘k o Eqa(s0, i2t, k, Pa(x, j)) = Pa(x,j)’
 >-- (flip_tac >> irule Eqa_eqn >> arw[] >>
      qpick_x_assum ‘i2(1, 1) o To1(X * J) = i2t’
      (assume_tac o GSYM) >> arw[o_assoc] >> 
      once_rw[one_to_one_id] >> rw[idR]) >>
 arw[o_assoc,p1_of_Pa]
 )
(form_goal
 “!J X ss:J-> Exp(X,1+1).
  ?U a:U->X. Mono(a) & 
   !x:1->X.
   (?x0. x = a o x0) <=>
   ?j:1->J. Ev(X,1+1) o Pa(x,ss o j) = i2(1,1)”));


val from_one_Mono = prove_store("from_one_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qspecl_then [‘X'’] strip_assume_tac To1_def >> arw[])
(form_goal
 “!X f:1->X.Mono(f)”));

val Mono_disjoint_coPa_Mono = prove_store
("Mono_disjoint_coPa_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 irule FUN_EXT >> strip_tac >>
 qspecl_then [‘A’,‘B’,‘g o a'’] assume_tac INC_FAC >>
 qspecl_then [‘A’,‘B’,‘h o a'’] assume_tac INC_FAC >>
 pop_assum_list (map_every strip_assume_tac) (* 4 *)
 >-- (*case 1, use a is mono, both via a*)
 (qsuff_tac ‘f0 = f0'’ >-- (strip_tac >> fs[]) >>
  fs[Mono_def] >> first_x_assum irule >>
  qsuff_tac ‘coPa(a,b) o i1(A,B) o f0 = 
             coPa(a,b) o i1(A,B) o f0'’
  >-- rw[GSYM o_assoc,i1_of_coPa] >>
  arw[] >> arw[GSYM o_assoc])
 >-- (*case 2, h via a, g via b, contradiction*)
 (qsuff_tac ‘a o f0 = b o f0'’ >-- arw[] >>
  qsuff_tac ‘coPa(a,b) o i1(A,B) o f0 = 
             coPa(a,b) o i2(A,B) o f0'’
  >-- rw[GSYM o_assoc,i12_of_coPa] >>
  arw[] >> rw[GSYM o_assoc] >> arw[])
 >-- (*case 3, h via b, g via a, contradiction*)
 (qsuff_tac ‘a o f0' = b o f0’ >-- arw[] >>
  qsuff_tac ‘coPa(a,b) o i1(A,B) o f0' = 
             coPa(a,b) o i2(A,B) o f0’
  >-- rw[GSYM o_assoc,i12_of_coPa] >>
  arw[] >> rw[GSYM o_assoc] >> arw[]) >>
 (*case 4, both via b, use b mono*)
 qsuff_tac ‘f0 = f0'’ >-- (strip_tac >> fs[]) >>
 fs[Mono_def] >> last_x_assum irule >>
 qsuff_tac ‘coPa(a,b) o i2(A,B) o f0 = 
            coPa(a,b) o i2(A,B) o f0'’
 >-- rw[GSYM o_assoc,i2_of_coPa] >>
 arw[] >> arw[GSYM o_assoc])
(form_goal
 “!A X a:A->X.Mono(a) ==>
  !B b:B->X. Mono(b) ==>
  (!a0:1->A b0:1->B. ~(a o a0 = b o b0)) ==>
  Mono(coPa(a,b))”));

val Thm5_lemma_1 = prove_store("Thm5_lemma_1",
e0
(rpt strip_tac >> 
 qby_tac ‘~(is0(A + 1))’ 
 >-- (ccontra_tac >> drule zero_no_MEM >>
      qby_tac ‘?f:1->A +1 . T’ 
      >-- (qexists_tac ‘i2(A,1)’ >> rw[]) >> fs[]) >>
 qby_tac ‘Mono(coPa(a,x))’
 >-- (irule Mono_disjoint_coPa_Mono >>
      arw[from_one_Mono] >> rpt strip_tac >>
      once_rw[one_to_one_id] >> arw[idR]) >>
 drule Mono_no_zero_post_inv >> first_x_assum drule >>
 pop_assum (x_choose_then "u" assume_tac) >>
 qexists_tac ‘coPa(i1(1,1) o To1(A),i2(1,1)) o u’ >>
 rw[o_assoc] >>
 qby_tac ‘u o coPa(a, x) o i2(A,1) = id(A + 1) o i2(A,1)’
 >-- arw[GSYM o_assoc] >>
 qby_tac ‘u o coPa(a, x) o i1(A,1) = id(A + 1) o i1(A,1)’
 >-- arw[GSYM o_assoc] >>
 fs[i12_of_coPa,idL,idR])
(form_goal
 “!A X a:A->X.Mono(a) ==>
  !x:1->X. (!x0:1->A. ~(a o x0 = x)) ==>
  ?phi:X->1+1. phi o x = i2(1,1) & phi o a = i1(1,1) o To1(A)”));


val Thm5_constructions = prove_store("Thm5_constructions",
e0
(rpt strip_tac >>
 qexists_tac ‘Tp(i1(1,1) o To1(A * 1))’ >> rw[] >> 
 qexists_tac 
 ‘Tp(Ev(X, 1 + 1) o
  Pa(a o p1(A, Exp(X, 1 + 1)), p2(A, Exp(X, 1 + 1))))’ >>
 rw[] >> rpt strip_tac >>
 qexists_tac 
 ‘Ev(X, 1 + 1) o Pa(p1(X, L), u o p2(X, L))’ >>
 rw[] >> rpt strip_tac >>
 qspecl_then [‘E’,‘X’,‘p1(X,L) o k’] 
 assume_tac Mono_Epi_fac >>
 first_x_assum accept_tac)
(form_goal 
“!A X a:A->X.Mono(a) ==> 
 ?j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 &
 ?a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 &
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 ?ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub & 
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 ?A' a':A'->X q:E->A'.Epi(q) & Mono(a') & p1(X,L) o k = a' o q”));

val Thm5_Mono = prove_store("Thm5_Mono",
e0
(rpt strip_tac >> 
 qby_tac
 ‘(j0 o To1 (Exp(X,1+1))) o u = a2 o u’
 >-- (rev_drule Eq_equality >> arw[]) >>
 qby_tac
 ‘Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1))) =
  Ev(A,1+1) o Pa(p1(A,Exp(X,1+1)), a2 o p2(A,Exp(X,1+1)))’
 >-- (qpick_x_assum
      ‘Tp(Ev(X, 1 + 1) o Pa(a o p1(A, Exp(X, 1 + 1)), p2(A, Exp(X, 1 + 1)))) = a2’ (assume_tac o GSYM) >>
     arw[] >> rw[Ev_of_Tp]) >>
 qby_tac
 ‘Pa(p1(A, Exp(X, 1 + 1)),a2 o p2(A, Exp(X, 1 + 1))) o 
  Pa(p1(A,L),u o p2(A,L)) =
  Pa(p1(A,L), a2 o u o p2(A,L))’
 >-- (irule to_P_eq >> rw[p12_of_Pa] >>
      rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc,p12_of_Pa]) >>
 qby_tac
 ‘!x:1->X.(?x0: 1-> A.a o x0 = x) ==>
  !t: 1 -> Exp(X,1+1).
   (?t0:1 -> L. u o t0 = t) ==>
   Ev(X,1+1) o Pa(x,t) = i1(1,1)’
 >-- (rpt strip_tac >>
      qby_tac 
      ‘Pa(a o x0,u o t0) = 
       Pa(a o p1(A, Exp(X, 1 + 1)), p2(A, Exp(X, 1 + 1))) o
       Pa(p1(A,L), u o p2(A,L)) o Pa(x0,t0)’ >--
      (irule to_P_eq >> rw[p12_of_Pa] >>
       rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc,p12_of_Pa] >>
       qby_tac
       ‘a o p1(A, Exp(X, 1 + 1)) o Pa(p1(A, L), (u o p2(A, L))) o Pa(x0, t0) =  a o (p1(A, Exp(X, 1 + 1)) o Pa(p1(A, L), (u o p2(A, L)))) o Pa(x0, t0)’ >-- rw[o_assoc] >>
       arw[p12_of_Pa]) >>
      qpick_x_assum ‘a o x0 = x’
      (assume_tac o GSYM) >> 
      qpick_x_assum ‘u o t0 = t’
      (assume_tac o GSYM) >> once_arw[] >> 
      once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >>
      qby_tac
      ‘(Ev(A, 1 + 1) o Pa(p1(A, Exp(X, 1 + 1)), a2 o p2(A, Exp(X, 1 + 1)))) o Pa(p1(A, L), u o p2(A, L)) =
       Ev(A, 1 + 1) o Pa(p1(A, Exp(X, 1 + 1)), a2 o p2(A, Exp(X, 1 + 1))) o Pa(p1(A, L), u o p2(A, L))’ >-- rw[o_assoc]>>
      arw[] >>
      qpick_x_assum ‘(j0 o To1(Exp(X, 1 + 1))) o u = a2 o u’
      (assume_tac o GSYM)  >>
      arw[GSYM o_assoc] >> 
      qby_tac
      ‘Pa(p1(A, L), ((j0 o To1(Exp(X, 1 + 1))) o u) o p2(A, L)) = Pa(p1(A,1),j0 o p2(A,1)) o Pa(p1(A,L),(To1(Exp(X,1+1)) o u) o p2(A,L))’ 
      >-- (irule to_P_eq >> rw[p12_of_Pa] >>
           rw[GSYM o_assoc,p12_of_Pa] >>
           rw[o_assoc,p12_of_Pa]) >>
      fs[o_assoc] >>
      qpick_x_assum ‘Tp(i1(1, 1) o To1(A * 1)) = j0’
      (assume_tac o GSYM) >> arw[GSYM o_assoc,Ev_of_Tp] >>
      rw[o_assoc]>> once_rw[one_to_one_id] >> rw[idR]) >>
qby_tac 
 ‘!x:1 -> X. 
  (?xb: 1 -> A'. a' o xb = x) ==>
  ?t: 1-> Exp(X,1+1). (?t0:1-> L.u o t0 = t) &
  Ev(X,1+1) o Pa(x,t) = i2(1,1)’
>-- (rpt strip_tac >> 
     qby_tac ‘?x0:1 -> E. q o x0 = xb’
     >-- (drule Epi_surj >> 
          first_x_assum $ qspecl_then [‘xb’] accept_tac) >>
     pop_assum strip_assume_tac >>
     qexists_tac ‘u o p2(X,L) o k o x0’ >>
     strip_tac (* 2 *) >--
     (qexists_tac ‘p2(X,L) o k o x0’ >> rw[]) >>
     qby_tac 
     ‘Pa(x, u o p2(X,L) o k o x0) = 
      Pa(p1(X,L), u o p2(X,L)) o
      Pa(x:1->X,p2(X,L) o k o x0)’
     >-- (irule to_P_eq >> rw[p12_of_Pa] >>
          rw[GSYM o_assoc,p12_of_Pa] >> 
          rw[o_assoc,p12_of_Pa]) >>
     once_arw[] >> drule Eq_equality >> 
     rw[GSYM o_assoc] >> once_arw[] >>
     qby_tac ‘x = p1(X,L) o k o x0’ 
     >-- (rw[GSYM o_assoc] >> arw[] >> arw[o_assoc]) >>
     once_arw[] >> rw[o_assoc,GSYM to_P_component] >>
     arw[GSYM o_assoc] >>
     rw[o_assoc] >> once_rw[one_to_one_id] >>
     rw[idR]) >>
qby_tac 
 ‘!x:1->X. (~((?x0:1->A. a o x0 = x) &
             ?x0:1->A'. a' o x0 = x))’ 
>-- (rpt strip_tac >> ccontra_tac >>
     pop_assum strip_assume_tac >>
     qsuff_tac ‘i1(1,1) = i2(1,1)’ >-- rw[i1_ne_i2_1] >>
     qby_tac ‘?xb : 1 -> A'. a' o xb = x’ 
     >-- (qexists_tac ‘x0'’ >> arw[]) >>
     first_x_assum drule >> 
     pop_assum strip_assume_tac >> 
     qby_tac ‘?x0 : 1 -> A. a o x0 = x’ 
     >-- (qexists_tac ‘x0’ >> arw[]) >>
     first_x_assum drule >> 
     pop_assum strip_assume_tac >> 
     first_x_assum $ qspecl_then [‘t’] assume_tac >>
     qby_tac ‘?(t0 : 1 -> L). u o t0 = t’ 
     >-- (qexists_tac ‘t0’ >> arw[]) >>
     first_x_assum drule >> fs[]) >> 
irule Mono_disjoint_coPa_Mono >> arw[] >>
rpt strip_tac >> ccontra_tac >>
qsuff_tac
‘((?x0 :1->A. a o x0 = a' o b0) &
   ?(x0 :1->A'). a' o x0 = a' o b0)’ >-- arw[] >>
strip_tac (* 2 *)
>-- (qexists_tac ‘a0’ >> arw[]) >>
qexists_tac ‘b0’ >> arw[] )
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) & Mono(a') & p1(X,L) o k = a' o q ==> Mono(coPa(a,a'))”));


val Thm5_Epi_ex_xp_a2phi0 = prove_store(
"Thm5_Epi_ex_xp_a2phi0",
e0
(rpt strip_tac >> irule Ev_eq_eq >>
 rw[o_assoc] >> 
 qby_tac
 ‘j0 o To1(Exp(X, 1 + 1)) o phi0 o p2(A, 1) = 
  j0 o (To1(Exp(X, 1 + 1)) o phi0) o p2(A, 1)’ >-- 
 rw[o_assoc] >>
 once_arw[] >> once_rw[one_to_one_id] >> rw[idL] >>
 qby_tac
 ‘Pa(p1(A, 1), a2 o phi0 o p2(A, 1)) = 
  Pa(p1(A,Exp(X,1+1)), a2 o p2(A,Exp(X,1+1))) o 
  Pa(p1(A,1),phi0 o p2(A,1))’
 >-- (irule to_P_eq >> rw[p12_of_Pa] >>
      rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc,p12_of_Pa]) >>
 once_arw[] >> rw[GSYM o_assoc] >> 
 qpick_x_assum ‘Tp(Ev(X, 1 + 1) o Pa(a o p1(A, Exp(X, 1 + 1)), p2(A, Exp(X, 1 + 1)))) = a2’ (assume_tac o GSYM) >>
 once_arw[] >> rw[Ev_of_Tp] >> 
 qpick_x_assum ‘Tp(i1(1, 1) o To1(A * 1)) = j0’
 (assume_tac o GSYM) >> once_arw[] >> rw[Ev_of_Tp] >>
 qpick_x_assum ‘Tp(phi o p1(X, 1)) = phi0’
 (assume_tac o GSYM) >> once_arw[] >>
 rw[Pa_distr,o_assoc,p12_of_Pa] >>
 qby_tac 
 ‘Pa(a o p1(A, 1), Tp((phi o p1(X, 1))) o p2(A, 1)) = 
  Pa(p1(X,1), phi0 o p2(X,1)) o Pa(a o p1(A,1), p2(A,1))’
 >-- (irule to_P_eq >> rw[p12_of_Pa] >>
      rw[GSYM o_assoc,p12_of_Pa] >> 
      rw[o_assoc,p12_of_Pa] >> arw[]) >>
 arw[] >> rw[GSYM o_assoc,Ev_of_Tp] >>
 rw[o_assoc,p12_of_Pa] >> arw[GSYM o_assoc] >>
 rw[o_assoc] >> once_rw[To1_def]>> rw[]
 )
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) ==> Mono(a') ==>
  p1(X,L) o k = a' o q ==> 
 !b:1->X.(~(?b0:1 -> A. a o b0 = b)) ==> 
 !phi. phi o a = i1(1,1) o To1(A) ==> phi o b = i2(1,1) ==>
 !phi0.Tp(phi o p1(X,1)) = phi0 ==>
   a2 o phi0 = (j0 o To1 (Exp(X,1+1))) o phi0”));


val Thm5_Epi_ex_xp = prove_store(
"Thm5_Epi_ex_xp",
e0
(rpt strip_tac >> 
 assume_tac (Thm5_Epi_ex_xp_a2phi0 |> strip_all_and_imp) >>
 qby_tac
 ‘?phi0':1->L. u o phi0' = Tp(phi o p1(X,1))’
 >-- (qexists_tac ‘Eqa(a2,j0 o To1(Exp(X,1+1)),u,phi0)’ >>
      arw[] >> flip_tac >> irule Eqa_eqn >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘ub o Pa(b, phi0') = 
  (i2(1,1) o To1 (X * L)) o Pa(b, phi0')’
 >-- (qby_tac ‘Pa(p1(X,L),u o p2(X,L)) o Pa(b, phi0') = 
               Pa(b, u o phi0')’
      >-- (irule to_P_eq >> rw[p12_of_Pa] >>
           rw[GSYM o_assoc,p12_of_Pa] >> 
           rw[o_assoc,p12_of_Pa]) >>
      qsuff_tac ‘Ev(X,1+1) o Pa(b,phi0) = phi o b’
      >-- (strip_tac >> rw[o_assoc] >>
           once_rw[one_to_one_id] >> rw[idR] >>
           qpick_x_assum 
           ‘Ev(X, 1 + 1) o Pa(p1(X, L), u o p2(X, L)) = ub’
           (assume_tac o GSYM) >>
           arw[o_assoc]) >> 
      qpick_x_assum 
      ‘Tp(phi o p1(X, 1)) = phi0’ (assume_tac o GSYM) >>
      arw[] >> 
      qby_tac ‘Tp(phi o p1(X, 1)) = 
      Tp(phi o p1(X, 1)) o id(1)’ >-- rw[idR] >>
      once_arw[] >> rw[Ev_of_Tp_el,o_assoc,p1_of_Pa]>>
      first_x_assum accept_tac) >>
 qby_tac
 ‘?bp0:1->E.k o bp0 = Pa(b,phi0')’ 
 >-- (qexists_tac 
      ‘Eqa(ub,i2(1,1) o To1(X * L),k,Pa(b, phi0'))’ >>
      flip_tac >> irule Eqa_eqn >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘bp0’ >> irule to_P_eq >>
 rw[p12_of_Pa] >> rw[GSYM o_assoc,p12_of_Pa] >>
 arw[o_assoc,p12_of_Pa])
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) ==> Mono(a') ==>
  p1(X,L) o k = a' o q ==> 
 !b:1->X.(~(?b0:1 -> A. a o b0 = b)) ==> 
 !phi. phi o a = i1(1,1) o To1(A) ==> phi o b = i2(1,1) ==>
 !phi0.Tp(phi o p1(X,1)) = phi0 ==>
   ?xp:1->E. Pa(p1(X,L),u o p2(X,L)) o k o xp = 
  Pa(b,phi0)”));


val Thm5_Epi = prove_store("Thm5_Epi",
e0
(rpt strip_tac >> irule surj_Epi >> strip_tac >>
 cases_on “?b0:1->A. a:A->X o b0 = b” >--
 (pop_assum strip_assume_tac >> 
  qexists_tac ‘i1(A,A') o b0’ >> 
  arw[GSYM o_assoc,i1_of_coPa]) >>
 qsuff_tac ‘?b0':1->A'. a' o b0' = b’ >--
 (strip_tac >> qexists_tac ‘i2(A,A') o b0'’ >>
  arw[GSYM o_assoc,i2_of_coPa]) >>
 rev_drule Thm5_lemma_1 >> 
 qby_tac ‘!x0:1->A. ~(a o x0 = b)’
 >-- (strip_tac >> ccontra_tac >>
      qby_tac ‘?b0.a o b0 = b’ 
      >-- (qexists_tac ‘x0’ >> arw[]) >>
      fs[]) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 abbrev_tac “Tp(phi:X->1+1 o p1(X,1)) = phi0” >>
 assume_tac (strip_all_and_imp Thm5_Epi_ex_xp) >>
 pop_assum strip_assume_tac >> 
 qexists_tac ‘q o xp’ >> 
 qby_tac ‘p1(X,Exp(X,1+1)) o Pa(b,phi0) = b’
 >-- rw[p1_of_Pa] >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 rw[GSYM o_assoc,p1_of_Pa] >> once_arw[] >> rw[])
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) & Mono(a') & p1(X,L) o k = a' o q ==> Epi(coPa(a,a'))”));

val Thm5_Iso = prove_store("Thm5_Iso",
e0
(rpt strip_tac >> irule Mono_Epi_Iso >>
 rev_drule Thm5_Mono >> 
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> 
 qby_tac ‘Mono(coPa(a, a'))’ >--
 (first_x_assum irule >> arw[] >>
  qexists_tac ‘q’ >> arw[]) >> arw[] >>
 rev_drule Thm5_Epi >> 
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> 
 first_x_assum irule >> arw[] >>
 qexists_tac ‘q’ >> arw[])
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) & Mono(a') & p1(X,L) o k = a' o q ==> Iso(coPa(a,a'))”));


val Thm5 = prove_store("Thm5",
e0
(rpt strip_tac >> drule Thm5_constructions >>
 pop_assum strip_assume_tac >>
 qspecl_then 
 [‘Exp(X,1+1)’,‘Exp(A,1+1)’,‘a2’,‘j0 o To1(Exp(X,1+1))’] 
 (x_choosel_then ["L","u"] assume_tac) isEq_ex >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qspecl_then [‘X * L’,‘1+1’,‘ub’,‘i2(1,1) o To1(X * L)’]
 (x_choosel_then ["E","k"] assume_tac) isEq_ex >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["A'","a'","q"] assume_tac) >>
 qexistsl_tac [‘A'’,‘a'’] >> 
 drule Thm5_Iso >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 arw[])
(form_goal
 “!A X a:A->X.Mono(a) ==> 
  ?A' a':A'->X. Mono(a') & Iso(coPa(a,a'))”));


val _ = new_pred "Trans" [("f0",ar_sort (mk_ob "R") (mk_ob "A")),
                          ("f1",ar_sort (mk_ob "R") (mk_ob "A"))];


val Trans_def = store_ax("Trans_def",
“!R A f0:R->A f1:R->A.Trans(f0,f1) <=> !X h0:X->R h1:X->R. f1 o h0 = f0 o h1 ==> ?u:X->R. f0 o u = f0 o h0 & f1 o u = f1 o h1”);


val _ = new_pred "Refl" [("f0",ar_sort (mk_ob "R") (mk_ob "A")),
                         ("f1",ar_sort (mk_ob "R") (mk_ob "A"))]

val Refl_def = store_ax("Refl_def",
“!R A f0:R->A f1. Refl(f0,f1) <=> ?d:A->R. f0 o d = id(A) & f1 o d = id(A)”);



val _ = new_pred "Sym" [("f0",ar_sort (mk_ob "R") (mk_ob "A")),
                        ("f1",ar_sort (mk_ob "R") (mk_ob "A"))];

val Sym_def = store_ax("Sym_def",
“!R A f0:R->A f1. Sym(f0,f1) <=> ?t:R->R. f0 o t = f1 & f1 o t = f0”);


val Thm6_first_sentence = prove_store(
"Thm6_first_sentence",
 e0
(rpt strip_tac >> irule prop_2_coro >>
 qexistsl_tac [‘A * A’,‘Pa(f0,f1)’,‘e’] >>
 drule Eqa_Mono >> arw[] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac 
      ‘Eqa(ce o p1(A,A),ce o p2(A,A),e,Pa(f0, f1) o x)’ >>
      irule Eqa_eqn >> 
      qby_tac
      ‘(ce o p1(A, A)) o Pa(f0, f1) o x = 
       ce o (p1(A, A) o Pa(f0, f1)) o x &
       (ce o p2(A, A)) o Pa(f0, f1) o x =
       ce o (p2(A, A) o Pa(f0, f1)) o x’
      >-- rw[o_assoc] >> arw[p12_of_Pa] >> 
      drule coEq_equality >> arw[GSYM o_assoc]) >>
 first_x_assum 
 (qspecl_then [‘p1(A,A) o e o y’,‘p2(A,A) o e o y’]
  assume_tac) >>
 drule Eq_equality >>
 fs[GSYM o_assoc] >> qexists_tac ‘r’ >> 
 irule to_P_eq >> arw[GSYM o_assoc,p12_of_Pa])
(form_goal
“!R A f0:R->A f1. Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> Mono(Pa(f0,f1)) ==> 
!cE ce:A->cE.iscoEq(f0,f1,ce) ==>
(!a0:1->A a1:1->A. ce o a0 = ce o a1 ==> ?r:1->R. f0 o r = a0 & f1 o r = a1) ==> !E e:E->A * A. isEq(ce o p1(A,A),ce o p2(A,A),e) ==> areiso(R,E)”));


val Mem_of_name_Eqa = prove_store("Mem_of_name_Eqa",
e0
(rpt strip_tac >> drule via_Eq_iff >> arw[] >>
rw[o_assoc] >> once_arw[one_to_one_id] >> rw[idR] >>
qby_tac ‘Tp(psi o p1(R, 1)) = Tp(psi o p1(R, 1)) o id(1)’
>-- rw[idR] >>
once_arw[] >> rw[Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa])
(form_goal 
“!R psi:R-> 1+1 r:1 -> R. 
  !E e. isEq(Ev(R,1+1),i2(1,1) o To1(R * Exp(R,1+1)),e)==>
 (psi o r = i2(1,1) <=> 
  ?r':1->E. e o r' = Pa(r,Tp(psi o p1(R,1))))”));



val Char_ex = prove_store("Char_ex",
e0
(rpt strip_tac >> drule Thm5 >> pop_assum strip_assume_tac >>
 fs[Iso_def] >>
 qexists_tac ‘coPa(i2(1,1) o To1(A),i1(1,1) o To1(A')) o f'’
 >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac 
      ‘(coPa(i2(1,1) o To1(A), i1(1,1) o To1(A')) o f') o a o x0 =  coPa(i2(1,1) o To1(A), i1(1,1) o To1(A')) o (f' o a) o x0’ 
     >-- rw[o_assoc] >>
     qpick_x_assum ‘a o x0 = x’ 
     (assume_tac o GSYM) >> arw[] >>
     qby_tac ‘f' o a = i1(A,A')’
     >-- (qby_tac 
         ‘f' o coPa(a, a') o i1(A,A') = id(A+A') o i1(A,A')’
         >-- (rw[GSYM o_assoc] >> arw[]) >>
         pop_assum mp_tac >> rw[i12_of_coPa,idL]) >>
     once_arw[] >> rw[GSYM o_assoc,i1_of_coPa] >>
     rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) >>
qspecl_then [‘A’,‘A'’,‘f' o x’] strip_assume_tac INC_FAC
>-- (qexists_tac ‘f0’ >>
     qby_tac ‘coPa(a,a') o i1(A, A') o f0 = 
              coPa(a,a') o f' o x’ >-- arw[] >>
     rfs[GSYM o_assoc,i1_of_coPa,idL]) >>
fs[o_assoc] >> pop_assum (assume_tac o GSYM) >> 
fs[] >> fs[GSYM o_assoc,i12_of_coPa] >>
fs[o_assoc] >> 
qpick_x_assum ‘i1(1, 1) o To1(A') o f0 = i2(1, 1)’ mp_tac >>
once_rw[one_to_one_id] >> rw[idR,i1_ne_i2_1])
(form_goal 
“!A X a:A->X. Mono(a) ==> 
 ?phi:X->1 + 1. (!x:1->X.(?x0:1->A.a o x0 = x) <=> phi o x = i2(1,1))”));


val Refl_equiv_to_itself  = prove_store("Refl_equiv_to_itself",
 e0
(rpt strip_tac >> fs[Refl_def] >> 
 qexists_tac ‘d o a’ >> rw[GSYM o_assoc] >> arw[idL])
(form_goal “!R A f0:R->A f1:R->A.Refl(f0:R->A,f1) ==> !a:1->A. ?r:1->R. f0 o r = a & f1 o r = a”));


val equiv_to_same_element = prove_store("equiv_to_same_element",
e0
(rpt strip_tac >> drule Refl_equiv_to_itself >> 
 first_x_assum (qspecl_then [‘a1’] assume_tac) >>
 first_x_assum (qspecl_then [‘a1’] assume_tac) >> rfs[] >>
 qexistsl_tac [‘r'’] >> arw[])
(form_goal 
“!R A f0:R->A f1.Refl(f0,f1) ==> 
 !a0 a1.
(!a':1->A.(?r:1->R.f0 o r = a1 & f1 o r = a') <=> (?r.f0 o r = a0 & f1 o r = a')) ==>
?r:1->R. f0 o r = a0 & f1 o r = a1”));

val Sym_Trans_rel_lemma = prove_store(
"Sym_Trans_rel_lemma",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >-- 
 (fs[Sym_def,Trans_def] >> 
  first_x_assum 
   (qspecl_then [‘1’,‘t o r'’,‘r’] assume_tac) >>
  qby_tac ‘f1 o t o r' = f0 o r’
  >-- (rw[GSYM o_assoc] >> arw[]) >>
  first_x_assum drule >> pop_assum strip_assume_tac >>
  qexists_tac ‘t o u’ >> rw[GSYM o_assoc] >> once_arw[] >>
  once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >> 
  once_arw[] >> rw[]) >> 
 fs[Trans_def] >>
 qpick_x_assum ‘f0 o r'' = f1 o r’
 (assume_tac o GSYM) >>
 first_x_assum drule >> pop_assum strip_assume_tac >> 
 qexists_tac ‘u’ >> arw[])
(form_goal 
“!R A f0:R->A f1.Sym(f0:R->A,f1) & Trans(f0,f1) ==> 
!a:1->A r:1->R. 
((?r':1->R. f0 o r' = f0 o r & f1 o r' = a) <=> 
 (?r'':1->R. f0 o r'' = f1 o r & f1 o r'' = a))”));


val Char_def = Char_ex |> spec_all |> ex2fsym "Char" ["a"]
                       |> gen_all
                       |> store_as "Char_def";



val fac_Char = prove_store("fac_Char",
e0
(rpt strip_tac >> drule Char_def >>
irule FUN_EXT >> strip_tac >> rw[o_assoc] >>
once_rw[one_to_one_id] >> rw[idR] >> 
pop_assum (assume_tac o iffLR) >> first_x_assum irule >>
qexists_tac ‘f o a’ >> rw[GSYM o_assoc] >> once_arw[] >> rw[])
(form_goal 
“!A X m:A->X.Mono(m)==>!P p:P->X f:P->A. m o f = p ==>
Char(m) o p = i2(1,1) o To1(P)”));


val fac_Char_via_any_map = prove_store(
"fac_Char_via_any_map",
e0
(rpt strip_tac >> drule Epi_has_section >> 
 drule Char_def >> 
 first_x_assum (qspecl_then [‘b’] assume_tac) >>
 rfs[] >> qexists_tac ‘s0 o x0’ >>
 qby_tac ‘(m o e) o s0 o x0 = m o (e o s0) o x0’
 >-- rw[o_assoc] >> arw[idL])
(form_goal 
“!A M e:A->M. Epi(e) ==> !B m:M->B.Mono(m) ==>
 !f:A->B. f = m o e ==> 
 !b:1->B.Char(m) o b = i2(1,1) ==>
 ?a:1->A. f o a = b”));

val Pa_o_split = prove_store("Pa_o_split",
e0
(rpt strip_tac >> irule to_P_eq >>
 rw[p12_of_Pa] >> rw[GSYM o_assoc,p12_of_Pa] >>
 rw[o_assoc,p12_of_Pa])
(form_goal
 “!B X f:B->X Y g:X->Y A.Pa(p1(A,B),g:X->Y o f o p2(A,B)) = 
  Pa(p1(A,X), g o p2(A,X)) o Pa(p1(A,B),f o p2(A,B))”));

val o_partial_Ev = prove_store("o_partial_Ev",
e0
(rpt strip_tac >> 
 qby_tac 
 ‘Pa(id(A),To1(A)) o x = Pa(x,id(1))’ 
 >-- (irule to_P_eq >> rw[GSYM o_assoc,p12_of_Pa,idL] >>
      once_rw[one_to_one_id]) >>
 rw[Pa_o_split,GSYM o_assoc,Ev_of_Tp] >>
 rw[o_assoc,Pa_distr,p12_of_Pa,idL] >> 
 once_rw[one_to_one_id] >> rw[idR])
(form_goal 
“!A x:1->A X Y psi:X->Y phi. 
 phi o Pa(x,Tp1(psi)) = 
 Ev(A,1+1) o Pa(p1(A,1),Tp(phi) o Tp1(psi) o p2(A,1)) o 
 Pa(id(A),To1(A)) o x”));


val Thm6_lemma_3 = prove_store("Thm6_lemma_3",
 e0
(rpt strip_tac >> 
abbrev_tac “i2(1,1) o To1(R * Exp(R,1+1)) = t” >>
qspecl_then [‘R * Exp(R,1+1)’,‘1+1’,‘Ev(R,1+1)’,‘t’] assume_tac isEq_ex >>
pop_assum (x_choosel_then ["R'","Psi"] assume_tac) >>
abbrev_tac 
“Pa(h:R->A o p1(R,Exp(R,1+1)),p2(R,Exp(R,1+1))) = h2R” >>
qspecl_then [‘R'’,‘A * Exp(R,1+1)’,‘h2R o Psi’] (x_choosel_then ["M","m","e"] strip_assume_tac) Mono_Epi_fac >>
abbrev_tac “Char(m:M -> A * Exp(R,1+1)) = phi” >> 
qby_tac ‘!x:1->A * Exp(R,1+1). 
         (?x0:1->M. m o x0 = x) <=> phi o x = i2(1,1)’
>-- (drule Char_def >> arw[]) >>
qexists_tac ‘Tp(phi)’ >> strip_tac >> 
qby_tac
‘!r:1->R.
 psi o r = i2(1,1) <=> 
 ?r':1->R'. Psi o r' = Pa(r,Tp1(psi))’
>-- (strip_tac >> rw[GSYM Tp1_def] >> 
     irule Mem_of_name_Eqa >> fs[]) >>
strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
(qby_tac 
 ‘phi o Pa(x,Tp1(psi)) = 
  Ev(A,1+1) o Pa(p1(A,1),Tp(phi) o Tp1(psi) o p2(A,1)) o 
  Pa(id(A),To1(A)) o x’ 
 >-- rw[o_partial_Ev] >>
 rfs[] >>
 drule fac_Char_via_any_map >> first_x_assum drule >>
 first_x_assum drule >> rfs[] >> first_x_assum drule >>
 first_x_assum (qspecl_then [‘Pa(x,Tp1(psi))’] assume_tac)>>
 rfs[] >> qexists_tac ‘p1(R,Exp(R,1+1)) o Psi o a’ >>
 strip_tac (* 2 *)
 >-- (qexists_tac ‘a’ >> irule to_P_eq >>
      rw[p12_of_Pa] >> 
      qby_tac 
      ‘p2(R, Exp(R, 1 + 1)) = p2(A, Exp(R, 1 + 1)) o h2R’
      >-- (qpick_x_assum 
           ‘Pa(h o p1(R, Exp(R, 1 + 1)), p2(R, Exp(R, 1 + 1))) = h2R’ 
           (assume_tac o GSYM) >> arw[p2_of_Pa]) >>
      once_arw[] >>
      qby_tac ‘(p2(A, Exp(R, 1 + 1)) o h2R) o Psi o a = 
      p2(A, Exp(R, 1 + 1)) o (h2R o Psi) o a’
      >-- rw[o_assoc] >> arw[p2_of_Pa]) >>
 qby_tac
 ‘h o p1(R, Exp(R, 1 + 1)) = p1(A, Exp(R, 1 + 1)) o h2R’
 >-- (qpick_x_assum 
      ‘Pa(h o p1(R, Exp(R, 1 + 1)), p2(R, Exp(R, 1 + 1))) = h2R’
      (assume_tac o GSYM) >> once_arw[] >> 
      rw[p1_of_Pa]) >>
 rw[GSYM o_assoc] >> once_arw[] >> 
 qby_tac ‘((p1(A, Exp(R, 1 + 1)) o h2R) o Psi) o a =
 p1(A, Exp(R, 1 + 1)) o (h2R o Psi) o a’ >-- rw[o_assoc] >>
 arw[p1_of_Pa]) >>
rfs[] >> 
qby_tac ‘m o e o r' = h2R o Pa(r, Tp1(psi))’
>-- (rw[GSYM o_assoc] >> 
     qpick_x_assum ‘h2R o Psi = m o e’ (assume_tac o GSYM) >>
     arw[] >> arw[o_assoc]) >>
qby_tac ‘h2R o Pa(r, Tp1(psi)) = Pa(x, Tp1(psi))’
>-- (irule to_P_eq >> rw[GSYM o_assoc,p12_of_Pa] >>
     qpick_x_assum 
     ‘Pa(h o p1(R, Exp(R, 1 + 1)), p2(R, Exp(R, 1 + 1))) = h2R’ (assume_tac o GSYM) >> arw[p12_of_Pa] >>
     arw[o_assoc,p12_of_Pa]) >>
qby_tac ‘phi o h2R o Pa(r, Tp1(psi)) = i2(1,1)’
>-- (qpick_x_assum ‘Char(m) = phi’ (assume_tac o GSYM) >>
     once_arw[] >> drule fac_Char >>
     first_x_assum 
     (qspecl_then [‘1’,‘Pa(x, Tp1(psi))’] assume_tac) >>
     qby_tac ‘To1(1) = id(1)’ 
     >-- (once_rw[one_to_one_id] >> rw[]) >> 
     qsuff_tac ‘Char(m) o Pa(x, Tp1(psi)) = i2(1,1) o To1(1)’
     >-- (once_arw[] >> rw[idR]) >>
     first_x_assum irule >>
     qexists_tac ‘e o r'’>> arw[]) >>
rw[Pa_distr,p12_of_Pa,idL,o_assoc] >> 
once_rw[one_to_one_id] >> rw[idR] >> 
qby_tac 
‘phi o Pa(x,Tp1(psi)) = 
 Ev(A,1+1) o Pa(p1(A,1),Tp(phi) o Tp1(psi) o p2(A,1)) o 
 Pa(id(A),To1(A)) o x’ 
>-- (rw[o_partial_Ev]) >> 
qby_tac ‘(h2R o Psi) o r' =
 h2R o Pa(r, Tp1(psi))’ >-- (arw[o_assoc]) >>
qby_tac 
‘Pa(x, Tp(phi) o Tp1(psi)) = 
 Pa(p1(A, 1), (Tp(phi) o Tp1(psi) o p2(A, 1))) o
               Pa(id(A), To1(A)) o x’
>-- (irule to_P_eq >> rw[p12_of_Pa] >>
     rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc,p12_of_Pa] >>
     once_rw[one_to_one_id] >> rw[idL,idR]) >>
arw[] >> 
qpick_x_assum ‘phi o Pa(x, Tp1(psi)) = Ev(A, 1 + 1) o
               Pa(p1(A, 1), (Tp(phi) o Tp1(psi) o p2(A, 1))) o
               Pa(id(A), To1(A)) o x’
(assume_tac o GSYM) >> arw[] >>
qpick_x_assum ‘h2R o Pa(r, Tp1(psi)) = Pa(x, Tp1(psi))’
(assume_tac o GSYM) >> arw[]
)
(form_goal 
“!R A h:R->A.?hb:Exp(R,1+1)-> Exp(A,1+1). 
!psi:R-> 1+1 x:1->A.
 (Ev(A,1+1) o Pa(p1(A,1),hb o Tp1(psi) o p2(A,1)) o
  Pa(id(A),To1(A)) o x = i2(1,1) <=> 
  ?r:1->R. psi o r = i2(1,1) & h o r = x)”));

val Diag_ex = prove_store("Diag_ex",
e0
(strip_tac >> qexists_tac ‘Pa(id(X),id(X))’ >> rw[])
(form_goal
“!X.?dX:X->X * X. Pa(id(X),id(X)) = dX”));

val Diag_def = Diag_ex |> spec_all |> eqT_intro
                       |> iffRL |> ex2fsym "Diag" ["X"]
                       |> C mp (trueI []) |> gen_all

val Diag_Mono = prove_store("Diag_Mono",
e0
(strip_tac >> rw[Mono_def,GSYM Diag_def] >> 
 rpt strip_tac >> 
 qby_tac ‘p1(A,A) o Pa(id(A), id(A)) o g = 
          p1(A,A) o Pa(id(A), id(A)) o h’ 
 >-- arw[] >> 
 fs[p1_of_Pa,GSYM o_assoc,idL])
(form_goal
 “!A.Mono(Diag(A))”));

val Eq_ex = prove_store("Eq_ex",
e0
(strip_tac >> qexists_tac ‘Char(Diag(X))’ >> rw[])
(form_goal “!X.?eqX:X * X -> 1+1. Char(Diag(X)) = eqX”))

val Eq_def = Eq_ex |> spec_all |> eqT_intro
                   |> iffRL |> ex2fsym "Eq" ["X"]
                   |> C mp (trueI []) |> gen_all
                   |> store_as "Eq_def";


val True_ex = prove_store("True_ex",
e0
(strip_tac >> qexists_tac ‘TRUE o To1(X)’ >> rw[])
(form_goal
“!X. ?tX:X->1+1.TRUE o To1(X) = tX”));

val True_def = True_ex |> spec_all |> eqT_intro 
                       |> iffRL |> ex2fsym "True" ["X"] |> C mp (trueI []) |> gen_all |> store_as "True_def";

val False_ex = prove_store("False_ex",
e0
(strip_tac >> qexists_tac ‘FALSE o To1(X)’ >> rw[])
(form_goal
“!X. ?fX:X->1+1.FALSE o To1(X) = fX”));

val False_def = False_ex |> spec_all |> eqT_intro 
                         |> iffRL |> ex2fsym "False" ["X"] |> C mp (trueI []) |> gen_all |> store_as "False_def";



val fac_Diag_eq = prove_store("fac_Diag_eq",
e0
(rpt strip_tac >> 
 fs[Pa_distr,Pa_eq_eq,idL] >>
 pop_assum_list (map_every (assume_tac o GSYM)) >> fs[])
(form_goal 
“!A x:1->A y:1->A x0:1->A.Pa(id(A),id(A)) o x0 = Pa(y,x) ==> 
 y = x”)); 

val fac_Diag_eq_iff = prove_store("fac_Diag_eq_iff",
e0
(rpt strip_tac >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (irule fac_Diag_eq >> qexists_tac ‘a0’  >>
      arw[Pa_distr,p12_of_Pa]) >>
 qexists_tac ‘p1(A,A) o aa’ >> 
 irule to_P_eq >> arw[Pa_distr,p12_of_Pa,GSYM o_assoc,idL])
(form_goal
 “!A aa:1->A * A.
  (?a0:1->A. aa = Pa(id(A),id(A)) o a0) <=>
  p1(A,A) o aa = p2(A,A) o aa”));

val Char_Diag = prove_store("Char_Diag",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘Pa(a1,a2)’] assume_tac fac_Diag_eq_iff>>
 fs[p12_of_Pa] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 qspecl_then [‘A’] assume_tac Diag_Mono >>
 drule Char_def >> pop_assum (assume_tac o GSYM) >>
 arw[Diag_def] >> 
 fconv_tac 
 (rand_fconv no_conv 
 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))  >>
 rw[])
(form_goal
“!A a1:1->A a2:1->A. Char(Diag(A)) o Pa(a1,a2) = i2(1,1) <=> a1 = a2”));

(*Eq_property same as char_diag_gen*)
val Eq_property = prove_store("Eq_property",
e0
(rpt strip_tac >> rw[GSYM Eq_def] >>
 assume_tac TRUE_def >> 
 qspecl_then [‘X’] assume_tac Diag_Mono >>
 drule Char_def >> dimp_tac >> strip_tac (* 2 *)
 >-- (irule FUN_EXT >> strip_tac >> 
     fs[GSYM True_def,o_assoc,GSYM TRUE_def] >>
     once_rw[one_to_one_id] >> rw[idR,Pa_distr,Char_Diag])>>
 irule FUN_EXT >> strip_tac >> once_rw[GSYM Char_Diag] >>
 qby_tac ‘Char(Diag(X)) o Pa(f, g) o a = True(A) o a’
 >-- arw[GSYM o_assoc] >>
 fs[GSYM TRUE_def,GSYM True_def,Pa_distr] >>
 rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!X A f:A->X g:A->X. 
f = g <=> Eq(X) o Pa(f,g) = True(A)”));

val Thm6_lemma_2 = prove_store("Thm6_lemma_2",
e0
(rpt strip_tac >> 
 rw[Pa_o_split,GSYM o_assoc,Ev_of_Tp] >>
 rw[o_assoc,Pa_distr,idL] >> once_rw[one_to_one_id] >>
 rw[idR,p1_of_Pa] >> rw[Char_Diag])
(form_goal
“!A x:1->A y:1->A. Ev(A,1+1) o 
Pa(p1(A,1),Tp(Char(Diag(A))) o x o p2(A,1))  o Pa(id(A),To1(A)) o y = i2(1,1) <=> y = x”));

val Pa_o_split' = Pa_o_split |> spec_all |> gen_all
                             |> store_as "Pa_o_split'";


val Thm6_g_ev_lemma = prove_store("Thm6_g_ev_lemma",
e0
(rpt strip_tac >> irule Ev_eq_eq >>
 pop_assum (assume_tac o GSYM) >> rw[o_assoc] >>
 qspecl_then [‘R’,‘1’,‘A’,‘a’,‘Exp(R, 1+1)’,
‘Tp((Ev(A, 1 + 1) o
                 Pa(f0 o p1(R, Exp(A, 1 + 1)), p2(R, Exp(A, 1 + 1))))) o
                Tp(Char(Diag(A)))’] assume_tac Pa_o_split' >>
fs[o_assoc] >> rw[Pa_o_split'] >>
rw[GSYM o_assoc,Ev_of_Tp] >> 
rw[o_assoc,Pa_distr,p12_of_Pa] >>
last_x_assum (assume_tac o GSYM) >>
once_arw[] >> rw[GSYM Tp1_def,Ev_of_Tp] >>
rw[o_assoc,Pa_distr,p12_of_Pa]  >>
rw[idL] >>
qsuff_tac ‘p2(R, 1) = To1(A) o f0 o p1(R, 1)’
>-- (strip_tac >> arw[]) >>
once_rw[To1_def] >> rw[])
(form_goal 
“!A a:1->A a':1->A R f0:R->A f1:R->A.
!psi:R->1+1.psi = 
Ev(A,1+1) o Pa(p1(A,1),Tp(Char(Diag(A))) o a o p2(A,1)) o 
Pa(id(A),To1(A)) o f0 ==>
Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o Tp(Char(Diag(A))) o a = 
Tp1(psi)”));



val Bar_def = Thm6_lemma_3 |> spec_all 
                           |> ex2fsym0 "Bar" ["h"]
                           |> gen_all
                           |> store_as "Bar_def"

val Sing_ex = prove_store("Sing_ex",
e0
(strip_tac >> qexists_tac ‘Tp(Char(Diag(A)))’ >> rw[])
(form_goal “!A.?sg. Tp(Char(Diag(A))) = sg”));

val Sing_def = Sing_ex |> spec_all |> ex2fsym0 "Sing" ["A"]
                       |> gen_all
                       |> store_as "Sing_def";


(*Thm6_lemma_2 is sg_def*)
val Thm6_g_ev = prove_store("Thm6_g_ev",
e0
(rpt strip_tac >> 
 abbrev_tac 
 “Ev(A,1+1) o Pa(p1(A,1),Sing(A) o a o p2(A,1)) o Pa(id(A),To1(A)) o f0:R->A = psi” >>
 pop_assum (assume_tac o GSYM) >>
 assume_tac Thm6_g_ev_lemma >> fs[Sing_def] >>
 first_x_assum drule >> 
 qby_tac
 ‘Tp((Ev(A, 1 + 1) o
                 Pa(f0 o p1(R, Exp(A, 1 + 1)), p2(R, Exp(A, 1 + 1))))) o
                Sing(A) o a o p2(A, 1) = 
 (Tp((Ev(A, 1 + 1) o
                 Pa(f0 o p1(R, Exp(A, 1 + 1)), p2(R, Exp(A, 1 + 1))))) o
                Sing(A) o a) o p2(A, 1)’ 
 >-- rw[o_assoc] >>
 last_x_assum (assume_tac o GSYM) >>
 arw[] >>
 qspecl_then [‘A’,‘R’,‘f1’] assume_tac Bar_def >>
 arw[] >>
qsuff_tac ‘!r:1->R. f0 o r = a <=> psi o r = i2(1,1)’
>-- (strip_tac >> arw[]) >>
qpick_x_assum
 ‘Ev(A, 1 + 1) o Pa(p1(A, 1), (Sing(A) o a o p2(A, 1))) o
  Pa(id(A), To1(A)) o f0 = psi’
(assume_tac o GSYM) >>
once_arw[] >> assume_tac Thm6_lemma_2 >>
fs[Sing_def,o_assoc])
(form_goal 
“!R A f0:R->A f1:R->A a:1->A a':1->A. Ev(A,1+1) o 
Pa(p1(A,1),Bar(f1) o 
Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o 
Sing(A) o a o p2(A,1)) o Pa(id(A),To1(A)) o a' = i2(1,1) <=> ?r:1->R. f0 o r = a & f1 o r = a'”));


val Thm6_g_ev' = prove_store("Thm6_g_ev'",
e0
(rpt strip_tac >> 
 assume_tac Thm6_g_ev >> 
 qby_tac
 ‘Pa(a', id(1)) = Pa(id(A), To1(A)) o a'’
 >-- (rw[Pa_distr] >> once_rw[one_to_one_id] >>
     rw[idL]) >>
 arw[])
(form_goal 
“!R A f0:R->A f1:R->A a':1->A a:1->A. Ev(A,1+1) o 
Pa(p1(A,1),
   Bar(f1) o 
   Tp(Ev(A,1+1) o
      Pa(f0 o p1(R,Exp(A,1+1)), p2(R,Exp(A,1+1)))) o 
   Sing(A) o a o p2(A,1)) o Pa(a',id(1)) = 
i2(1,1) <=>
?r:1->R.f0 o r = a & f1 o r = a'”));


val one_to_two_cases = prove_store("one_to_two_cases",
 e0
(rpt strip_tac >> 
 qspecl_then [‘1’,‘1’,‘f’] strip_assume_tac INC_FAC >>(* 2 *)
 pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR] >>
 strip_tac >> arw[])
(form_goal 
“!f:1->1+1. f = i1(1,1) | f = i2(1,1)”));

val one_to_two_eq = prove_store("one_to_two_eq",
e0
(rpt strip_tac >> cases_on “f = i2(1,1)”
 >-- fs[] >>
 fs[] >> 
 qspecl_then [‘f’] strip_assume_tac one_to_two_cases >>
 qspecl_then [‘g’] strip_assume_tac one_to_two_cases >>
 arw[])
(form_goal 
“!f:1->1+1 g:1->1+1. (f = i2(1,1) <=> g = i2(1,1)) ==> f = g”))



val f0g_eq_f1g = prove_store("f0g_eq_f1g",
 e0
(rpt strip_tac >> irule FUN_EXT >> strip_tac >> 
 irule Ev_eq_eq >> irule FUN_EXT >> strip_tac >> 
 irule one_to_two_eq >>
 assume_tac Thm6_g_ev' >>
 qby_tac ‘a' = Pa(p1(A,1) o a',p2(A,1) o a')’ 
 >-- rw[GSYM to_P_component] >>
 pop_assum mp_tac >> once_rw[one_to_one_id] >> strip_tac >>
 once_arw[] >> pop_assum (K all_tac) >>
 fs[o_assoc] >>
 first_assum (qspecl_then [‘R’,‘A’,‘f0’,‘f1’,‘p1(A, 1) o a'’,‘f0 o a’] assume_tac) >> fs[o_assoc]>>
 first_assum (qspecl_then [‘R’,‘A’,‘f0’,‘f1’,‘p1(A, 1) o a'’,‘f1 o a’] assume_tac) >> fs[o_assoc] >> 
 irule Sym_Trans_rel_lemma >> arw[])
(form_goal
“!R A f0:R->A f1:R->A. Sym(f0,f1) & Trans(f0,f1) ==> 
 Bar(f1) o Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)), p2(R,Exp(A,1+1)))) o Sing(A) o f0 = 
  Bar(f1) o Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)), p2(R,Exp(A,1+1)))) o Sing(A) o f1”));


val Thm6_page29_means_just_that = prove_store
("Thm6_page29_means_just_that",
e0
(rpt strip_tac >> 
 qspecl_then [‘R’,‘A’,‘f0’,‘f1’,‘a'’,‘a0’] 
 (assume_tac o GSYM) Thm6_g_ev' >>
 qspecl_then [‘R’,‘A’,‘f0’,‘f1’,‘a'’,‘a1’] 
 (assume_tac o GSYM) Thm6_g_ev' >>
 once_arw[] >>  pop_assum (K all_tac) >>
 pop_assum (K all_tac) >> 
 fs[GSYM o_assoc])
(form_goal
“!A a0:1->A a1:1->A R f0:R->A f1:R->A.
 Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a0 = 
 Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a1 ==>
 !a':1->A.(?r:1->R. f0 o r = a0 & f1 o r = a') <=>
          (?r:1->R. f0 o r = a1 & f1 o r = a')”));


(*TO-DO: let rw be able to solve f <=>f*)
val compose_with_g_eq_equiv = prove_store
("compose_with_g_eq_equiv",
e0
(rpt strip_tac >>
 drule Thm6_page29_means_just_that >>
 irule equiv_to_same_element >> arw[])
(form_goal
“!A a0:1->A a1:1->A R f0:R->A f1:R->A.
 Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a0 = 
  Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a1 ==>
 Refl(f0,f1) ==>
 ?r:1->R. f0 o r = a0 & f1 o r = a1”));



val Thm6_page29_picture = prove_store(
"Thm6_page29_picture",
e0
(rpt strip_tac >>
 qby_tac ‘Sym(f0, f1) & Trans(f0, f1)’ >-- arw[] >> 
 drule f0g_eq_f1g >> 
 abbrev_tac
 “Bar(f1:R->A) o Tp((Ev(A, 1 + 1) o
                Pa(f0 o p1(R, Exp(A, 1 + 1)), p2(R, Exp(A, 1 + 1))))) o
               Sing(A) = l” >>
 fs[GSYM o_assoc] >>  
 qsuff_tac ‘?u. u o ce = l’
 >-- (strip_tac >> pop_assum (assume_tac o GSYM) >> fs[] >>
      arw[o_assoc]) >>
 qexists_tac ‘coEqa(f0,f1,ce,l)’ >> 
 flip_tac >> irule coEqa_eqn >> arw[])
(form_goal
“!R A f0:R->A f1:R->A. Sym(f0,f1) ==> Trans(f0,f1) ==> 
 !cE ce:A->cE. iscoEq(f0,f1,ce) ==>
 !a0:1->A a1:1->A.
 ce o a0 = ce o a1 ==>
  Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a0 = 
  Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a1”));


val Thm6 = prove_store("Thm6",
e0
(rpt strip_tac >> irule Thm6_first_sentence >> 
 qexistsl_tac [‘A’,‘e’,‘f0’,‘f1’,‘cE’,‘ce’] >>
 arw[] >> rpt strip_tac >> irule equiv_to_same_element >>
 arw[] >> irule Thm6_page29_means_just_that >>
 irule Thm6_page29_picture >> arw[] >>
 qexistsl_tac [‘cE’,‘ce’] >> arw[])
(form_goal
“!R A f0:R->A f1:R->A. Mono(Pa(f0,f1)) ==>
 Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> 
 !cE ce:A->cE. iscoEq(f0,f1,ce) ==>
 !E e:E->A * A. isEq(ce o p1(A,A),ce o p2(A,A),e) ==>
 areiso(R,E)”));








val Thm6_first_sentence' = prove_store(
"Thm6_first_sentence",
 e0
(rpt strip_tac >> irule prop_2_coro_subo>>
(* qexistsl_tac [‘A * A’,‘Pa(f0,f1)’,‘e’] >> *)
 drule Eqa_Mono >> arw[] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac 
      ‘Eqa(ce o p1(A,A),ce o p2(A,A),e,Pa(f0, f1) o x)’ >>
      irule Eqa_eqn >> 
      qby_tac
      ‘(ce o p1(A, A)) o Pa(f0, f1) o x = 
       ce o (p1(A, A) o Pa(f0, f1)) o x &
       (ce o p2(A, A)) o Pa(f0, f1) o x =
       ce o (p2(A, A) o Pa(f0, f1)) o x’
      >-- rw[o_assoc] >> arw[p12_of_Pa] >> 
      drule coEq_equality >> arw[GSYM o_assoc]) >>
 first_x_assum 
 (qspecl_then [‘p1(A,A) o e o y’,‘p2(A,A) o e o y’]
  assume_tac) >>
 drule Eq_equality >>
 fs[GSYM o_assoc] >> qexists_tac ‘r’ >> 
 irule to_P_eq >> arw[GSYM o_assoc,p12_of_Pa])
(form_goal
“!R A f0:R->A f1. Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> Mono(Pa(f0,f1)) ==> 
!cE ce:A->cE.iscoEq(f0,f1,ce) ==>
(!a0:1->A a1:1->A. ce o a0 = ce o a1 ==> ?r:1->R. f0 o r = a0 & f1 o r = a1) ==> !E e:E->A * A. isEq(ce o p1(A,A),ce o p2(A,A),e) ==> 
 ?h1 h2. e o h1 = Pa(f0,f1) & Pa(f0,f1) o h2 = e & h1 o h2 = id(E) & h2 o h1 = id(R)”));



val Thm6' = prove_store("Thm6",
e0
(rpt strip_tac >> irule Thm6_first_sentence' >> arw[] >>
 qexistsl_tac [‘cE’,‘ce’] >>
 arw[] >> rpt strip_tac >> irule equiv_to_same_element >>
 arw[] >> irule Thm6_page29_means_just_that >>
 irule Thm6_page29_picture >> arw[] >>
 qexistsl_tac [‘cE’,‘ce’] >> arw[])
(form_goal
“!R A f0:R->A f1:R->A. Mono(Pa(f0,f1)) ==>
 Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> 
 !cE ce:A->cE. iscoEq(f0,f1,ce) ==>
 !E e:E->A * A. isEq(ce o p1(A,A),ce o p2(A,A),e) ==>
 ?h1 h2. e o h1 = Pa(f0,f1) & Pa(f0,f1) o h2 = e & h1 o h2 = id(E) & h2 o h1 = id(R)”));


val iso_isEq_isEq = prove_store("iso_isEq_isEq",
e0
(rpt strip_tac >> rw[isEq_def] >> 
 drule $ iffLR isEq_def >> 
 qby_tac
 ‘f o e o h1 = g o e o h1’ >-- arw[GSYM o_assoc] >>
 rfs[] >> rpt strip_tac >> first_x_assum drule >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum strip_assume_tac >> uex_tac >>
 qexists_tac ‘h2 o a0’ >>
 arw[GSYM o_assoc] >> rpt strip_tac >>
 qby_tac 
 ‘a = e o h1 o a0'’
 >-- arw[GSYM o_assoc] >>
 first_x_assum drule >> arw[] >>
 pop_assum (assume_tac o GSYM) >> arw[GSYM o_assoc,idL])
(form_goal
 “!A B f:A->B g:A->B E e:E->A. isEq(f,g,e) ==>
  !E' e':E'->A h1:E' ->E h2:E ->E'. e o h1 = e' & 
 e' o h2 = e & h1 o h2 = id(E) & h2 o h1 = id(E') ==>
 isEq(f,g,e')”));

val Thm6_isEq = prove_store("Thm6_isEq",
e0
(rpt strip_tac >> drule Thm6' >>
 rfs[] >> first_x_assum drule >>
 qsspecl_then [‘ce o p1(A, A)’,‘ce o p2(A, A)’] 
 strip_assume_tac isEq_ex >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 drule iso_isEq_isEq >> first_x_assum irule >>
 qexistsl_tac [‘h1’,‘h2’] >> arw[])
(form_goal
 “!R A f0:R->A f1:R->A. Mono(Pa(f0,f1)) ==>
 Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> 
 !cE ce:A->cE. iscoEq(f0,f1,ce) ==>
 isEq(ce o p1(A,A),ce o p2(A,A),Pa(f0,f1))”));



val Pb_fac_iff = prove_store("Pb_fac_iff",
e0
(rpt strip_tac >> drule $ iffLR isPb_def >>
 pop_assum strip_assume_tac >>
 dimp_tac >> strip_tac >--
 (pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
 strip_tac >> pop_assum (assume_tac o GSYM) >>
 arw[GSYM o_assoc]) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘a’ >> arw[])
(form_goal 
“!X Z f:X->Z Y g:Y->Z P p:P->X q.
 isPb(f,g,p,q) ==>
 !A u:A->X v:A->Y. 
 (?a:A->P. p o a = u & q o a = v) <=> f o u = g o v”));



val Pb_fac_iff_1 = prove_store("Pb_fac_iff_1",
e0
(rpt strip_tac >> drule Pb_fac_iff >>
 first_x_assum 
 (qspecl_then [‘1’,‘u’,‘id(1)’] assume_tac) >>
 fs[idR] >> pop_assum (assume_tac o GSYM) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘a’ >> arw[] >> once_rw[one_to_one_id]) >>
 qexists_tac ‘a’ >> arw[])
(form_goal 
“!X Z f:X->Z g:1->Z P p0:P->X q.
 isPb(f,g,p0,q) ==>
 !u:1->X. 
 (?a:1->P. p0 o a = u) <=> f o u = g”));



val Pb_reorder = prove_store("Pb_reorder",
e0
(rw[isPb_def] >> rpt strip_tac 
 >-- (pop_assum (K all_tac) >> once_arw[] >> rw[]) >>
 first_x_assum (qspecl_then [‘A’,‘v’,‘u’] assume_tac) >>
 qpick_x_assum ‘g:Y->Z o u:A->Y = f:X->Z o v’
 (assume_tac o GSYM) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 uex_tac >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘a’ >> strip_tac >> arw[] >>
 rpt strip_tac >> first_x_assum irule >> arw[]
)
(form_goal
“!X Z f:X->Z Y g:Y->Z P p0:P->X q0:P->Y.isPb(f,g,p0,q0) ==>
 isPb(g,f,q0,p0)”));


val pb_fac_exists' = proved_th $
e0
(rpt strip_tac >> 
assume_tac Pb_fac_iff >> 
 first_x_assum $ irule o iffRL >>
 qexistsl_tac [‘Z’,‘f’,‘g’] >> arw[])
(form_goal “!X Z f:X->Z Y g:Y->Z Pb p:Pb->X q:Pb->Y.isPb(f:X->Z,g:Y->Z,p,q) ==> 
 !A u v. f o u = g o v ==> ?a:A->Pb. p o a = u & q o a = v”);
(*



val char_pb = cg $
expandf
(rpt strip_tac >> irule prop_2_coro_subo >> arw[]>>
 drule Pb_Mono_Mono >> 
 qspecl_then [‘1+1’,‘i2(1,1)’] assume_tac from_one_Mono >>
 first_x_assum drule >> arw[] >>
 rpt strip_tac (* 2 *) >-- 
 (qby_tac
  ‘?y:1->Pb. pb1:Pb->X o y = a:A->X o x:1->A & pb2:Pb->1 o y = id(1)’
  >-- (drule pb_fac_exists' )))
(form_goal
“!A X a.Mono(a:A->X) ==> 
 !Pb pb1 pb2. isPb(Char(a),i2(1,1),pb1,pb2) ==> 
    ?h1 h2.pb1 o h1 = a & a o h2 = pb1 & h1 o h2 = id(Pb) & h2 o h1 = id(A)”);

>>
 pop_assum (qspecl_then [‘1’] assume_tac)



val char_pb = proved_th $
expandf
(rpt strip_tac >> irule prop_2_coro_subo >> arw[]>>
 drule Pb_Mono_Mono >> 
 qspecl_then [‘1+1’,‘i2(1,1)’] assume_tac from_one_Mono >>
 first_x_assum drule >> arw[] >>
 rpt strip_tac (* 2 *) >-- 
 (qby_tac
  ‘?y:1->Pb. pb1:Pb->X o y = a:A->X o x:1->A & pb2:Pb->1 o y = id(1)’
  >-- (drule pb_fac_exists' >> (*TO-DO:irule bug,should use irule works*)
  first_x_assum (qspecl_then [‘1’,‘a o x’,‘id(1)’] assume_tac) >>
  rev_drule Char_def >> first_x_assum (qspecl_then [‘a o x’] assume_tac) >>
  qsuff_tac ‘Char(a) o a o x = i2(1,1)’ 
  >-- (strip_tac >> fs[idR] >> rfs[](* >> qexistsl_tac [‘a'’] >> arw[] *)))))
(form_goal
“!A X a.Mono(a:A->X) ==> 
 !Pb pb1 pb2. isPb(Char(a),i2(1,1),pb1,pb2) ==> 
    ?h1 h2.pb1 o h1 = a & a o h2 = pb1 & h1 o h2 = id(Pb) & h2 o h1 = id(A)”);

*)


val char_pb = proved_th $
e0
(rpt strip_tac >> irule prop_2_coro_subo >> arw[]>>
 drule Pb_Mono_Mono >> 
 qspecl_then [‘1+1’,‘i2(1,1)’] assume_tac from_one_Mono >>
 first_x_assum drule >> arw[] >>
 rpt strip_tac (* 2 *) >-- 
 (qby_tac
  ‘?y:1->Pb. pb1:Pb->X o y = a:A->X o x:1->A & pb2:Pb->1 o y = id(1)’
  >-- (drule pb_fac_exists' >> (*TO-DO:irule bug,should use irule works*)
  first_x_assum (qspecl_then [‘1’,‘a o x’,‘id(1)’] assume_tac) >>
  rev_drule Char_def >> first_x_assum (qspecl_then [‘a o x’] assume_tac) >>
  qsuff_tac ‘Char(a) o a o x = i2(1,1)’
  >-- (strip_tac >> fs[idR]  >> qexistsl_tac [‘a'’] >> arw[]) >>
  pop_assum (assume_tac o GSYM) >> arw[] >>
  qexistsl_tac [‘x’] >> arw[]) >>
  pop_assum strip_assume_tac >> qexistsl_tac [‘y’] >> arw[]) >>
rev_drule Char_def >> 
drule $ iffLR isPb_def  >> pop_assum strip_assume_tac >> arw[] >>
qby_tac ‘Char(a) o pb1 o y  = i2(1,1) o pb2 o y’
>-- (rw[GSYM o_assoc] >> arw[]) >>
pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!A X a.Mono(a:A->X) ==> 
 !Pb pb1 pb2. isPb(Char(a),i2(1,1),pb1,pb2) ==> 
    ?h1 h2.pb1 o h1 = a & a o h2 = pb1 & h1 o h2 = id(Pb) & h2 o h1 = id(A)”);

val char_square = proved_th $
e0
(rpt strip_tac >> irule FUN_EXT >> rpt strip_tac >> 
 drule Char_def >>
 first_x_assum (qspecl_then [‘a o a'’] assume_tac) >> rw[o_assoc] >> 
 once_rw[one_to_one_id] >> rw[idR] >> 
 pop_assum (assume_tac o GSYM) >>
 arw[] >> qexistsl_tac [‘a'’] >> rw[])
(form_goal
“!A X a:A->X. Mono(a) ==> Char(a) o a = i2(1,1) o To1(A)”);

val Pb_ex = isPb_ex

val char_is_pb = proved_th $
e0
(rpt strip_tac >> drule char_pb >> 
 qspecl_then [‘X’,‘1+1’,‘Char(a)’,‘1’,‘i2(1,1)’] assume_tac Pb_ex >>
 pop_assum (x_choosel_then ["Pb","pb1","pb2"] assume_tac) >>
 first_x_assum drule  >> pop_assum strip_assume_tac >> 
 drule (isPb_def |> iffLR) >> pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘A’,‘a’,‘To1(A)’] assume_tac) >>
 rw[isPb_def] >>
 qby_tac ‘Char(a) o a = i2(1,1) o To1(A)’
 >-- (qby_tac ‘Char(a) o pb1 o h1 = i2(1,1) o pb2 o h1’
      >-- (arw[GSYM o_assoc]) >> rfs[] >> 
      pop_assum mp_tac >> once_rw[To1_def] >> rw[]) >>
 arw[] >> rpt strip_tac >> uex_tac >>
 (*here the goal is ?(a' : A' -> A). !(a' : A' -> A). a o a'# = u & to1(A, 1) o a'# = v <=>
                 a'# = a'# ... same name*) 
 suffices_tac (rapf "?a':A'->A. a:A->X o a' = u")
 >-- (strip_tac >> qexistsl_tac [‘a'’] >> strip_tac (* 2 *) >--
      (arw[] >> once_rw[To1_def] >> rw[]) >>
      rpt strip_tac >> irule $ iffLR Mono_def >>
      qexistsl_tac [‘X’,‘a’] >> arw[]) >>
 drule $ iffLR isPb_def >> pop_assum strip_assume_tac >>
 last_x_assum drule >> pop_assum (K all_tac) >>
 first_x_assum (qspecl_then [‘A'’,‘u’,‘v’] assume_tac)>>
 first_x_assum drule >> pop_assum (assume_tac o uex_expand) >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘h2 o a'’] >>
 first_x_assum (qspecl_then [‘a'’] assume_tac) >> fs[] >>
 arw[GSYM o_assoc])
(form_goal 
“!A X a.Mono(a:A->X) ==> isPb(Char(a),i2(1,1),a,To1(A))”);












(*TODOs.
val char_is_pb_unique = proved_th $
e0
(rpt strip_tac >> irule fun_ext >> rpt strip_tac >>
 irule one_to_two_eq >> qexistsl_tac ["i1","i2"] >> 
 drule char_is_pb >> first_x_assum drule >> 
 drule (iffLR ispb_def) >> pop_assum strip_assume_tac >>
 rev_drule (iffLR ispb_def) >> pop_assum strip_assume_tac >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘c o a' = i2 o id(1)’ >-- arw[idR] >>
      first_x_assum drule >> 
      pop_assum strip_assume_tac >>
      first_x_assum (qspecl_then ["a''"] assume_tac) >> fs[] >>
      qby_tac ‘char(i1, i2, a) o a o a'' = i2 o to1(A, 1) o a''’
      >-- arw[GSYM o_assoc] >> pop_assum mp_tac >>
      once_rw[one_to_one_id] >> rw[idR] >> once_arw[] >> rw[]) >>
 qby_tac ‘char(i1, i2, a) o a' = i2 o id(1)’ >-- arw[idR] >>
 last_x_assum drule >>
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then ["a''"] assume_tac) >> fs[] >>
 qby_tac ‘c o a o a'' = i2 o to1(A, 1) o a''’ 
 >-- arw[GSYM o_assoc] >> pop_assum mp_tac >>
 once_rw[one_to_one_id] >> rw[idR] >> once_arw[] >> rw[]
 )
(form_goal
“!A X a:A->X. ismono(a) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !c:X->two. ispb(c,i2,a,to1(A,1)) ==> c = char(i1,i2,a)”);

val iso_subobj_same_char = proved_th $
e0
(rpt strip_tac >> irule char_is_pb_unique >> arw[] >>
 drule char_square >> first_x_assum drule >>
 (*qspecl_then ["X","two","char(i1,i2,a)",""] assume_tac pb_ex*)
 rw[ispb_def] >> 
 qby_tac ‘char(i1, i2, a) o b = i2 o to1(B, 1)’
 >-- (qpick_x_assum ‘a o h2 = b’ (assume_tac o GSYM) >>
     once_arw[] >> rev_drule char_def >> 
     first_x_assum drule >> irule fun_ext >> strip_tac >>
     rw[o_assoc] >> 
     first_x_assum (qspecl_then ["a o h2 o a'"] assume_tac) >>
     once_rw[one_to_one_id] >> rw[idR] >>
     pop_assum (assume_tac o iffLR) >> first_x_assum irule >>
     qexistsl_tac ["h2 o a'"] >> rw[]) >>
 arw[] >> rpt strip_tac >>
 rev_drule char_is_pb >> first_x_assum drule >> 
 drule (iffLR ispb_def) >> pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then ["A'"] assume_tac) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexistsl_tac ["h1 o a'"] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (irule ismono_property >> qexistsl_tac ["X","b"] >>
     arw[] >> first_x_assum (qspecl_then ["a'"] assume_tac) >> fs[] >>
     qpick_x_assum ‘a o a' = u’ mp_tac >>
     qpick_x_assum ‘b o h1 = a’ (assume_tac o GSYM) >>
     once_arw[] >> rw[o_assoc]) >>
 qspecl_then ["A'"] assume_tac to1_unique >>
 first_x_assum (qspecl_then ["v","to1(B,1) o a''"] assume_tac) >>
 arw[] >>
 first_x_assum (qspecl_then ["a'"] assume_tac) >> fs[] >>
 qpick_x_assum ‘a o a' = u’ mp_tac >>
 qpick_x_assum ‘b o h1 = a’ (assume_tac o GSYM) >>
 once_arw[] >> rw[o_assoc]
 )
(form_goal  
“!a.ismono(a:A->X) ==>!b.ismono(b:B->X) ==>
 !h1:A->B h2:B->A. h1 o h2 = id(B) & h2 o h1 = id(A) ==> 
 b o h1 = a & a o h2 = b ==> 
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 char(i1,i2,a) = char(i1,i2,b)”);


*)




val iscoPr_expand = iscoPr_def |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!fg : AB->X. fg o i1 = f & fg o i2 = g”) |> store_as "iscoPr_expand";

val copa_def = 
    iscoPr_expand |> iffLR |> strip_all_and_imp
                  |> ex2fsym0 "copa" ["i1","i2","f","g"]
                  |> gen_all |> disch_all |> gen_all
                  |> store_as "copa_def"

val i12_of_copa = copa_def |> strip_all_and_imp
                           |> conjE1
                           |> gen_all 
                           |> disch_all
                           |> gen_all
                           |> store_as "i12_of_copa"


val is_copa = copa_def |> strip_all_and_imp
                       |> conjE2
                       |> gen_all 
                       |> disch_all
                       |> gen_all
                       |> store_as "is_copa"


(*a version of prop_5 lemma for general copr*)

val coPr_Iso = prove_store("coPr_Iso",
e0
(rpt strip_tac >> rw[Iso_def] >> 
 qexists_tac ‘copa(iA,iB,i1(A,B),i2(A,B))’>>
  strip_tac (* 2 *)
  >-- (irule from_coP_eq >> rw[o_assoc,i12_of_coPa,idL] >>
      drule i12_of_copa >> arw[]) >>
  drule is_copa >> 
  qsuff_tac
  ‘coPa(iA, iB) o copa(iA, iB, i1(A, B), i2(A, B)) = 
   copa(iA,iB,iA,iB) & id(AB) = copa(iA,iB,iA,iB)’
  >-- (strip_tac >> arw[]) >> strip_tac (* 2 *) >--
  (first_x_assum irule >> drule i12_of_copa >>
   arw[o_assoc,i12_of_coPa]) >> 
  first_x_assum irule >> rw[idL])
(form_goal
 “!A B AB iA:A->AB iB:B->AB. 
  iscoPr(iA,iB) ==> Iso(coPa(iA,iB))”)); 

(*actually can have a stronger version*)


val inc_Mono = prove_store("inc_Mono",
e0
(rpt strip_tac (* 2 *) >--
 (rw[Mono_def] >> rpt strip_tac >>
 irule FUN_EXT >> strip_tac >>
 qby_tac ‘copa(iA,iB,id(A),g o a o To1(B)) o iA o g = copa(iA,iB,id(A),g o a o To1(B)) o iA o h’
 >-- arw[] >> pop_assum mp_tac >>
 drule i12_of_copa >> rw[GSYM o_assoc] >>
 arw[idL] >> strip_tac >> arw[]) >>
 rw[Mono_def] >> rpt strip_tac >>
 irule FUN_EXT >> strip_tac >>
 qby_tac ‘copa(iA,iB,g o a o To1(A),id(B)) o iB o g =
          copa(iA,iB,g o a o To1(A),id(B)) o iB o h’
 >-- arw[] >> pop_assum mp_tac >>
 drule i12_of_copa >> rw[GSYM o_assoc] >>
 arw[idL] >> strip_tac >> arw[])
(form_goal 
“!A B AB iA:A->AB iB:B->AB. iscoPr(iA,iB) ==>
 Mono(iA) & Mono(iB)”));

val prop_5_lemma_copa = prove_store("prop_5_lemma_copa",
e0
(rpt strip_tac >>
 ccontra_tac >>
 qsuff_tac ‘i1(A,B) o x0 = i2(A,B) o x0'’
 >-- rw[prop_5_lemma] >>
 qby_tac ‘copa(i1,i2,i1(A,B),i2(A,B)) o i1 o x0 =
          copa(i1,i2,i1(A,B),i2(A,B)) o i2 o x0'’
 >-- arw[] >>
 drule i12_of_copa >> 
 fs[GSYM o_assoc])
(form_goal
 “!A B AB i1:A->AB i2:B->AB. iscoPr(i1,i2) ==> 
  !x0:1->A x0':1->B.~(i1 o x0 = i2 o x0')”));

val from_copr_components = prove_store(
"from_copr_components",
e0
(repeat strip_tac >> irule is_copa >> arw[])
(form_goal “!A B AB i1:A->AB i2:B->AB. iscoPr(i1, i2) ==>!X f:AB->X. f = copa(i1, i2, f o i1, f o i2)”));

val from_cop_eq = prove_store("from_cop_eq",
e0
(rpt strip_tac >> 
 qsuff_tac ‘f = copa(i1,i2,f o i1,f o i2) &
            g = copa(i1,i2,g o i1,g o i2)’
 >-- (strip_tac >> once_arw_tac[] >> 
     pop_assum (K all_tac) >> pop_assum (K all_tac) >> 
     arw_tac[]) >> strip_tac
 >> match_mp_tac from_copr_components >> arw_tac[])
(form_goal “!A B AB i1:A->AB i2:B->AB.iscoPr(i1,i2) ==> !X f:AB ->X g. f o i1 = g o i1 & f o i2 = g o i2 ==> f = g”));


val inc_fac = prove_store("inc_fac",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘B’,‘copa(iA,iB,i1(A,B),i2(A,B)) o f’] 
 strip_assume_tac INC_FAC (* 2 *) >--
 (disj1_tac >> qexists_tac ‘f0’ >> 
  qby_tac
  ‘coPa(iA,iB) o i1(A, B) o f0 = coPa(iA,iB) o copa(iA, iB, i1(A, B), i2(A, B)) o f’ >-- arw[] >>
  fs[GSYM o_assoc,i12_of_coPa] >>
  qsuff_tac ‘(coPa(iA, iB) o copa(iA, iB, i1(A, B), i2(A, B)))  = id(AB)’ >-- (strip_tac >> arw[idL]) >>
  irule from_cop_eq >> 
  qexistsl_tac [‘A’,‘iA’,‘B’,‘iB’] >> drule i12_of_copa >>
  arw[o_assoc,i12_of_coPa,idL]) >>
 disj2_tac >> qexists_tac ‘f0’ >> 
  qby_tac
  ‘coPa(iA,iB) o i2(A, B) o f0 = coPa(iA,iB) o copa(iA, iB, i1(A, B), i2(A, B)) o f’ >-- arw[] >>
  fs[GSYM o_assoc,i12_of_coPa] >>
  qsuff_tac ‘(coPa(iA, iB) o copa(iA, iB, i1(A, B), i2(A, B)))  = id(AB)’ >-- (strip_tac >> arw[idL]) >>
  irule from_cop_eq >> 
  qexistsl_tac [‘A’,‘iA’,‘B’,‘iB’] >> drule i12_of_copa >>
  arw[o_assoc,i12_of_coPa,idL])
(form_goal
 “!A AB iA:A->AB B iB:B->AB. iscoPr(iA,iB) ==>
 !f:1->AB. (?f0:1->A. iA o f0 = f)  |
           (?f0:1->B. iB o f0 = f) ”));


val copr_disjoint = prove_store("copr_disjoint",
e0
(rpt strip_tac >> drule prop_5_lemma_copa >> 
 drule inc_Mono >> drule inc_fac >> 
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 cases_on “?x0 : 1 -> A. x:1->AB = iA o x0” (* 2 *)
 >-- (arw[] >> pop_assum strip_assume_tac >>
     ccontra_tac >> pop_assum strip_assume_tac >>
     qby_tac ‘iA o x0 = iB o x0'’ 
     >-- (pop_assum mp_tac >> 
          pop_assum (assume_tac o GSYM) >>
          strip_tac >> pop_assum (assume_tac o GSYM) >>
          qpick_x_assum ‘!x0:1->A x0'. ~(iA o x0 = iB o x0')’
          (K all_tac) >> arw[]) >>
     rfs[]) >>
 arw[] >> pop_assum_list (map_every strip_assume_tac) (* 2 *)
 >-- (qby_tac ‘?x0:1->A. x = iA:A->AB o x0’
      >-- (qexists_tac ‘f0’ >> arw[]) >>
      first_x_assum opposite_tac) >>
 qexists_tac ‘f0’ >> arw[])
(form_goal “!A B AB iA:A->AB iB:B->AB. iscoPr(iA,iB) ==>
!x:1->AB. (~(?x0:1->A. x = iA o x0)) <=> (?x0:1->B. x = iB o x0)”));



val Char_Diag' = Char_Diag |> rewr_rule[TRUE_def]
                           |> store_as "Char_Diag'";






val Iso_Epi = prove_store("Iso_Epi",
e0
(rw[Iso_def,Epi_def] >> rpt strip_tac >>
 qsuff_tac ‘h o f o f' = g o f o f'’ 
 >-- (arw[idR] >> strip_tac >> arw[]) >> 
 arw[GSYM o_assoc])
(form_goal “!A B f:A->B. Iso(f) ==> Epi(f)”));


val iso_coPr_coPr = prove_store("iso_coPr_coPr",
e0
(rpt strip_tac >> rw[iscoPr_expand] >> rpt strip_tac >>
 drule $ iffLR Iso_def >> drule copa_def >> fs[] >>
 first_x_assum (qspecl_then [‘X'’,‘f’,‘g’] assume_tac) >>
 qexists_tac ‘copa(iA,iB,f,g) o f'’ >> rw[o_assoc] >>
 qby_tac ‘f' o f0 = iA & f' o g0 = iB’ >-- 
 (qby_tac ‘f' o copa(iA, iB, f0, g0) o iA = id(AB) o iA & 
           f' o copa(iA, iB, f0, g0) o iB = id(AB) o iB’
  >-- arw[GSYM o_assoc] >>
  pop_assum mp_tac >> drule i12_of_copa >> arw[idL]) >>
 arw[] >> 
 drule i12_of_copa >> arw[] >> 
 rpt strip_tac >> irule $ iffLR Epi_def >>
 qexistsl_tac [‘AB’,‘copa(iA, iB, f0, g0)’] >>
 drule Iso_Epi >> arw[o_assoc,idR] >>
 drule from_cop_eq >> first_x_assum irule >> 
 drule i12_of_copa >> arw[o_assoc]
 )
(form_goal “!A B AB iA:A->AB iB:B->AB. iscoPr(iA,iB) ==>
 !X f0:A->X g0:B->X. Iso(copa(iA,iB,f0,g0)) ==> iscoPr(f0,g0)”));


val copa_coPa = prove_store("copa_coPa",
e0
(rpt strip_tac >> flip_tac >> irule is_copa >> 
 rw[i12_of_coPa,i2_def])
(form_goal
 “!A X f:A->X B g:B->X. copa(i1(A,B),i2(A,B),f,g) = coPa(f,g)”));




val i1_xor_i2_1 = prove_store("i1_xor_i2_1",
e0
(rpt strip_tac >> qspecl_then [‘1’,‘1’] assume_tac i2_def >>
 drule copr_disjoint >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 qby_tac ‘(?x0. x = i1(1, 1) o x0) <=> x = i1(1,1)’
 >-- (dimp_tac >> strip_tac >-- (pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR]) >>
     qexists_tac ‘id(1)’ >> arw[idR]) >> fs[] >>
 qby_tac ‘(?x0. x = i2(1, 1) o x0) <=> x = i2(1,1)’
 >-- (dimp_tac >> strip_tac >-- (pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR]) >>
     qexists_tac ‘id(1)’ >> arw[idR]) >> fs[] >>
 cases_on “x = i1(1,1)” (* 2 *) >> dimp_tac >> strip_tac (* 3 *)
 >-- (ccontra_tac >> fs[]) >-- arw[] >> fs[])
(form_goal 
 “!x:1->1+1. x = i1(1,1) <=> ~(x = i2(1,1))”));


val TRUE2FALSE = prove_store("TRUE2FALSE",
e0
(assume_tac i1_xor_i2_1 >> fs[GSYM TRUE_def,GSYM FALSE_def])
(form_goal
“!f. ~(f = TRUE) <=> f = FALSE”));



val IMP_ex = prove_store("IMP_ex",
e0
(rpt strip_tac >> 
 by_tac “Mono(Pa(TRUE,FALSE))”
 >-- rw[from_one_Mono] >>
 drule Thm5 >> 
 pop_assum (x_choosel_then ["M","imp0"] strip_assume_tac) >>
 drule Char_def >> fs[TRUE_def] >>
 qexists_tac ‘Char(imp0)’ >> rpt strip_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 fs[GSYM copa_coPa] >>
 qspecl_then [‘1’,‘M’] assume_tac i2_def >>
 drule iso_coPr_coPr >> first_x_assum drule >> drule copr_disjoint >> 
 first_x_assum (qspecl_then [‘Pa(p1,p2)’] assume_tac) >>
 qby_tac 
 ‘(?x0:1->1. Pa(p1, p2) = Pa(TRUE, FALSE) o x0) <=> Pa(p1, p2) = Pa(TRUE, FALSE)’
 >-- (dimp_tac >> strip_tac >-- (first_x_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR]) >>
      qexists_tac ‘id(1)’ >> arw[idR]) >>
 fs[Pa_eq_eq] >> 
 pop_assum (K all_tac) >> pop_assum (assume_tac o GSYM) >> 
 fconv_tac (land_fconv no_conv (once_depth_fconv no_conv (rewr_fconv (eq_sym "ar")))) >>
 arw[] >> dimp_tac >> rpt strip_tac >> fs[] (* 2 *)
 >-- fs[GSYM TRUE2FALSE] >>
 ccontra_tac >> fs[] >> fs[GSYM TRUE_def,GSYM FALSE_def,i1_ne_i2_1])
(form_goal 
“?imp:(1+1) * (1 + 1)->1+1. 
 !p1 p2. imp o Pa(p1,p2) = TRUE <=> (p1 = TRUE ==> p2 = TRUE)”));

val IMP_def = IMP_ex |> ex2fsym0 "IMP" [] |> store_as "IMP_def";


val CONJ_ex = prove_store("CONJ_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Char(Pa(TRUE,TRUE))’ >> 
 qby_tac ‘Mono(Pa(TRUE,TRUE))’ >-- rw[from_one_Mono] >> 
 drule Char_def >> fs[TRUE_def] >> pop_assum (assume_tac o GSYM) >>
 once_arw[] >> rw[Pa_distr,Pa_eq_eq] >> once_rw[one_to_one_id] >> rw[idR] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (*  3 *)
 >-- (pop_assum (K all_tac) >> arw[])  
 >-- (once_arw[] >> rw[]) >>
 qexists_tac ‘id(1)’ >> arw[])
(form_goal 
“?conj:(1+1) * (1+1)->1+1. 
 !p1 p2. conj o Pa(p1,p2) = TRUE <=>
 (p1 = TRUE & p2 = TRUE)”));

val CONJ_def = CONJ_ex |> ex2fsym0 "CONJ" [] |> store_as "CONJ_def";

val IFF_ex = prove_store("IFF_ex",
e0
(rpt strip_tac >>
 qexists_tac ‘CONJ o Pa(IMP,IMP o Pa(p2(1+1,1+1),p1(1+1,1+1)))’ >> 
 rpt strip_tac >> rw[o_assoc,Pa_distr,CONJ_def] >> 
 rw[IMP_def,p12_of_Pa] >> dimp_tac >> rpt strip_tac (*  3*)
 >-- (dimp_tac >> strip_tac (* 2 *) >> first_x_assum drule >> arw[]) 
 >-- fs[] >-- fs[])
(form_goal 
“?iff:(1+1) * (1+1)->1+1. 
 !p1 p2. iff o Pa(p1,p2) = TRUE <=>
 (p1 = TRUE <=> p2 = TRUE)”));


val IFF_def = IFF_ex |> ex2fsym0 "IFF" [] |> store_as "IFF_def";

val True1TRUE = prove_store("True1TRUE",
e0
(rw[GSYM True_def] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal “True(1) = TRUE”));



val DISJ_ex = prove_store("DISJ_ex",
e0
(rpt strip_tac >> 
 by_tac “Mono(Pa(FALSE,FALSE))” >-- rw[from_one_Mono] >> 
 drule Thm5 >> 
 pop_assum (x_choosel_then ["O","or0"] strip_assume_tac) >>
 drule Char_def >>
 qexists_tac ‘Char(or0)’ >> rpt strip_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 fs[GSYM copa_coPa] >>
 qspecl_then [‘1’,‘O’] assume_tac i2_def >>
 drule iso_coPr_coPr >> first_x_assum drule >> drule copr_disjoint >> 
 first_x_assum (qspecl_then [‘Pa(p1,p2)’] assume_tac) >>
 fs[TRUE_def] >> 
 fconv_tac (land_fconv no_conv (once_depth_fconv no_conv (rewr_fconv (eq_sym "ar")))) >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rw[Pa_distr,Pa_eq_eq] >>
 once_rw[one_to_one_id] >> rw[idR]>> 
 qby_tac
 ‘(?x0:1->1 . p1 = FALSE & p2 = FALSE) <=> p1 = FALSE & p2 = FALSE’ 
 >-- (dimp_tac >> strip_tac >-- arw[] >> qexists_tac ‘id(1)’ >> arw[]) >>
 arw[] >> dimp_tac >> strip_tac (* 3 *)
 >-- (cases_on “p1 = TRUE” (* 2 *) >-- arw[] >>
     fs[TRUE2FALSE] >> fs[GSYM TRUE2FALSE]) 
 >> ccontra_tac >> fs[GSYM TRUE_def,GSYM FALSE_def,i1_ne_i2_1])
(form_goal
“?or:(1+1) * (1 +1)->1+1. 
 !p1:1->1+1 p2. or o Pa(p1,p2) = TRUE <=> 
  (p1 = TRUE | p2 = TRUE)”));

val DISJ_def = DISJ_ex |> ex2fsym0 "DISJ" [] |> store_as "DISJ_def";



val NEG_ex = prove_store("NEG_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘coPa(TRUE,FALSE)’ >> strip_tac >>
 assume_tac i1_xor_i2_1 >> fs[TRUE_def,FALSE_def] >>
 cases_on “pred = TRUE” >--
 (arw[] >> rw[GSYM TRUE_def,i12_of_coPa,GSYM FALSE_def] >> 
 ccontra_tac >> fs[TRUE_def,FALSE_def] >> 
 first_x_assum $ qspecl_then [‘TRUE’] assume_tac >> fs[]) >>
 rfs[] >> 
 first_x_assum $ qspecl_then [‘pred’] assume_tac >> fs[] >>
 rfs[] >> fs[GSYM FALSE_def,i12_of_coPa])
(form_goal
“?neg: 1+1 -> 1+1.
 !pred:1->1+1. neg o pred = TRUE <=> pred = FALSE”));


val NEG_def = NEG_ex |> ex2fsym0 "NEG" [] |> store_as "NEG_def";


(*
YX(y : ar(1, Y))(pxy : ar(X * Y, 1 + 1))
   
   ----------------------------------------------------------------------
   (NEG o All(X) o Tp(NEG o Ev(X, 1 + 1))) o Tp(pxy) o y = TRUE <=>
             ?(x : ar(1, X)). pxy o Pa(x#, y) = TRUE

parser bug
*)

val TRUE_xor_FALSE = i1_xor_i2_1 |> rewr_rule[FALSE_def,TRUE_def]
                                |> store_as "TRUE_xor_FALSE";

val TRUE_ne_FALSE = i1_ne_i2_1 |> rewr_rule[FALSE_def,TRUE_def]
                               |> store_as "TRUE_ne_FALSE";





val All_ex = prove_store("All_ex",
e0
(strip_tac >> qexists_tac ‘Char(Tp1(True(X)))’ >>
 qby_tac ‘Mono(Tp1(True(X)))’ >-- rw[from_one_Mono] >> 
 drule Char_def >> pop_assum (assume_tac o GSYM) >>
 fs[TRUE_def] >> once_rw[one_to_one_id] >> rw[idR] >> rpt strip_tac >>
 qby_tac
 ‘(?x0:1->1. Tp1(True(X)) = Tp(pxy) o y) <=> 
  Tp1(True(X)) = Tp(pxy) o y’ 
 >-- (dimp_tac >> strip_tac >> qexists_tac ‘id(1)’ >> arw[]) >>
 arw[] >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (qby_tac ‘Ev(X,1+1) o Pa(p1(X,1),Tp1(True(X)) o p2(X,1)) =
          Ev(X,1+1) o Pa(p1(X,1),Tp(pxy) o y o p2(X,1))’
 >-- arw[GSYM o_assoc] >>
 fs[GSYM Tp1_def,Ev_of_Tp,GSYM True_def] >>
 fs[Pa_o_split,GSYM o_assoc,Ev_of_Tp] >> fs[o_assoc] >> 
 qby_tac
 ‘(TRUE o To1(X) o p1(X, 1)) o Pa(x,id(1)) =
  (pxy o Pa(p1(X, 1), y o p2(X, 1))) o Pa(x,id(1))’ 
 >-- arw[] >> fs[o_assoc,Pa_distr,p12_of_Pa,idR] >>
 pop_assum  mp_tac >> once_rw[one_to_one_id] >> rw[idR] >> 
 strip_tac >> arw[]) >>
 flip_tac >> rw[GSYM Tp1_def] >> irule is_Tp >>
 rw[o_assoc,Pa_o_split] >> rw[GSYM o_assoc,Ev_of_Tp] >>
 irule FUN_EXT >> strip_tac >> rw[o_assoc,Pa_distr] >>
 once_rw[one_to_one_id] >> rw[idR] >> arw[] >>
 rw[GSYM True_def] >> rw[o_assoc] >> once_rw[one_to_one_id] >>
 rw[idR])
(form_goal
“!X.?Uq:Exp(X,1+1) -> 1+1. 
 !Y pxy:X * Y-> 1+1 y:1->Y.
 (Uq o Tp(pxy) o y = TRUE  <=> 
  !x:1->X. pxy o Pa(x,y) = TRUE)”));


val All_def = All_ex |> spec_all |> ex2fsym0 "All" ["X"]
                     |> gen_all
                     |> store_as "All_def";



val pxy_true = prove_store("pxy_true",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (arw[o_assoc,GSYM True_def] >> once_rw[one_to_one_id] >> 
 rw[idR]) >>
 irule FUN_EXT >> strip_tac >> once_rw[to_P_component] >>
 arw[GSYM True_def] >> rw[o_assoc] >> 
 once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!X Y pred:X * Y -> 1+1.pred = True(X * Y) <=> 
    !x:1->X y:1->Y. pred o Pa(x,y) = TRUE”));


fun exists_forall (n,s) = 
    let 
        val f0 = mk_fvar "f0" []
        val af0 = mk_forall n s (mk_neg f0)
        val ef0 = mk_exists n s f0
        val d1 = (C negI)
                     (existsE (n,s) (assume ef0)
                 (negE (assume f0) 
                   ((C allE) (assume af0) (mk_var(n,s)))))
                 af0 |>
                 disch ef0
        val d2 = elim_double_neg
                     ((C negI)
                          (negE
                               (allI (n,s)
                                     ((C negI)
                                          (negE
                                               (existsI (n,s) (mk_var(n,s)) f0 ((C add_cont) (assume f0) (HOLset.add(essps,(n,s))))
                                                        )
                                               (assume (mk_neg ef0)))
                                          f0))
                               (assume (mk_neg af0))
)
                          (mk_neg ef0))|>
                     disch (mk_neg af0)
    in dimpI d1 d2
    end


val Exq_ex = prove_store("Exq_ex",
e0
(strip_tac >> 
 qexists_tac ‘NEG o All(X) o Tp(NEG o Ev(X,1+1))’ >>
 rpt strip_tac >>
 rw[o_assoc,NEG_def] >>
 qby_tac
 ‘Tp(NEG o Ev(X,1+1)) o Tp(pxy) = Tp(NEG o pxy)’ 
 >-- (irule is_Tp >> rw[o_assoc,Pa_o_split] >> rw[GSYM o_assoc,Ev_of_Tp] >>
      rw[o_assoc,Ev_of_Tp]) >>
rw[TRUE_xor_FALSE,All_def] >> rw[o_assoc,NEG_def,Ev_of_Tp_el] >>
dimp_tac >> strip_tac (* 2 *) >--
(ccontra_tac >> 
 qsuff_tac ‘!x:1->X. pxy o Pa(x,y) = FALSE’ >-- arw[] >>
 strip_tac >>
 qpick_x_assum ‘~(!x:1->X. pxy o Pa(x,y) = FALSE)’ (K all_tac) >>
 rw[TRUE_xor_FALSE] >> ccontra_tac >>
 qsuff_tac ‘?x:1->X. pxy o Pa(x,y) = TRUE’ >-- arw[] >>
 qexists_tac ‘x’ >> arw[]) >>
ccontra_tac >>
first_x_assum (qspecl_then [‘x’] assume_tac) >> fs[TRUE_ne_FALSE]
)
(form_goal
“!X.?Exq:Exp(X,1+1) -> 1+1. 
 !Y pxy:X * Y->1+1 y:1->Y. 
 (Exq o Tp(pxy) o y = TRUE  <=> 
  ?x:1->X. pxy o Pa(x,y) = TRUE)”));

val Ex_def = Exq_ex |> spec_all |> ex2fsym0 "Ex" ["X"] |> gen_all
                    |> store_as "Ex_def"


val Eq_property_TRUE = prove_store("Eq_property_TRUE",
e0
(rpt strip_tac >> rw[GSYM True1TRUE] >> rw[GSYM Eq_property])
(form_goal
 “!X p1 p2.Eq(X) o Pa(p1,p2) = TRUE <=> p1 = p2”));

(*better have p1 p2 p3*)
val E1_ex = prove_store("E1_ex",
e0
(strip_tac >>
 abbrev_tac
 “IMP o 
    Pa(CONJ o Pa(Ev(X,1+1) o Pa(p1(X,X * Exp(X,1+1)), p2(X,Exp(X,1+1)) o p2(X,X * Exp(X,1+1))),
                 Ev(X,1+1) o Pa(p1(X,Exp(X,1+1)) o p2(X,X * Exp(X,1+1)),p2(X,Exp(X,1+1)) o p2(X,X * Exp(X,1+1)))),
      Eq(X) o 
      Pa(p1(X,X * Exp(X,1+1)), p1(X,Exp(X,1+1)) o p2(X,X * Exp(X,1+1)))) = p0” >>
 qexists_tac 
 ‘CONJ o
  Pa(Ex(X),All(X) o Tp(All(X) o Tp(p0)))’ >> rpt strip_tac >>
  rw[o_assoc,Pa_distr,CONJ_def] >> rw[All_def] >> rw[o_assoc,All_def] >>
 rw[Ex_def] >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 rw[o_assoc,Pa_distr,IMP_def] >> once_rw[CONJ_def] >>
 rw[p12_of_Pa] >> once_rw[Eq_property_TRUE] >>
 rw[Ev_of_Tp_el] >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘x’ >> arw[] >> rpt strip_tac >> first_x_assum irule >> arw[]) >>
 strip_tac >-- (qexists_tac ‘x’ >> arw[]) >>
 rpt strip_tac >> 
 qsuff_tac ‘x'' = x  & x' = x’ >-- (strip_tac >> arw[]) >> strip_tac >>
 first_x_assum irule >> arw[]
 )
(form_goal
“!X.?Exq: Exp(X,1+1) -> 1+1. 
 !Y pxy:X * Y->1+1 y:1->Y. 
 (Exq o Tp(pxy) o y = TRUE  <=> 
  ?x:1->X. pxy o Pa(x,y) = TRUE & 
  !x0:1->X. pxy o Pa(x0,y) = TRUE ==> x0 = x)”));


val E1_def =  E1_ex |> spec_all |> ex2fsym0 "E1" ["X"] |> gen_all
                    |> store_as "E1_def";
 


fun NEG_CONJ2IMP_NEG0 A B = 
    let 
        val AB = mk_conj A B
        val l = mk_neg AB
        val nB = mk_neg B
        val r = mk_imp A nB
        val l2r = negE (conjI (assume A) (assume B)) (assume l) |> negI B |> disch A |> disch l
        val r2l = negE (conjE2 (assume AB)) (mp (assume r) (conjE1 (assume AB))) 
                       |> negI AB |> disch r
    in dimpI l2r r2l
    end

val NEG_CONJ2IMP_NEG = NEG_CONJ2IMP_NEG0 (mk_fvar "A" []) (mk_fvar "B" [])



val FUN_EXT_iff = prove_store("FUN_EXT_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (drule FUN_EXT >> arw[]) >>
 rpt strip_tac >> arw[])
(form_goal
“!A B f:A->B g. (!a:1->A. f o a = g o a) <=> f = g”));


val True2TRUE = prove_store("True2TRUE",
e0
(rpt strip_tac >> rw[GSYM True_def,o_assoc] >>
 once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!X x:1->X. True(X) o x = TRUE”));


val False2FALSE = prove_store("False2FALSE",
e0
(rw[GSYM False_def,o_assoc] >> once_rw[one_to_one_id] >>
 rw[idR])
(form_goal
 “!X x:1->X. False(X) o x = FALSE”)); 



local
val eq_sym = 
prove_store("eq_sym",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> once_arw[] >> rw[])
(form_goal
“!A B f:A->B g:A->B. f = g <=> g = f”));
in
val pred_subset_ex = prove_store("pred_subset_ex",
e0
(rpt strip_tac >> 
 qspecl_then [‘X’,‘1+1’,‘pred’,‘1’,‘TRUE’] strip_assume_tac isPb_ex >>
 drule $ GSYM Pb_fac_iff_1 >>
 qexistsl_tac [‘P’,‘p’] >> arw[] >> strip_tac >> 
 (*TODO: write one function do the long thing parametized by the eq_sym.*)
 fconv_tac (rand_fconv no_conv (once_depth_fconv no_conv (rewr_fconv (spec_all eq_sym)))) >> rw[] (*almost equally stupid*)
 (*stupid *) (*rpt strip_tac >> dimp_tac >> rpt strip_tac >--
 (qex_tac ‘a’ >> arw[]) >> qex_tac ‘x0’ >> arw[]*))
(form_goal
“!X pred:X->1+1.?A ss:A ->X.
 (!x:1->X. pred o x = TRUE <=> ?x0:1->A. x = ss o x0)”));
val pred_subset_ex' = prove_store("pred_subset_ex'",
e0
(rpt strip_tac >> 
 qspecl_then [‘X’,‘1+1’,‘pred’,‘1’,‘TRUE’] strip_assume_tac isPb_ex >>
 drule $ GSYM Pb_fac_iff>>
 qexistsl_tac [‘P’,‘p’] >> arw[] >>
 qby_tac ‘Mono(p)’
 >-- (drule Pb_Mono_Mono >>
     first_x_assum irule >> rw[from_one_Mono]) >>
 arw[] >> pop_assum (K all_tac) >>
 pop_assum mp_tac >> once_rw[To1_def] >>
 rw[GSYM True_def] >> strip_tac >> arw[] >>
 rpt strip_tac >>
 first_x_assum 
  (qspecl_then [‘K’,‘x’,‘To1(K)’] assume_tac) >>
 arw[] >>
 (*TODO: write one function do the long thing parametized by the eq_sym.*)
 fconv_tac (rand_fconv no_conv (once_depth_fconv no_conv (rewr_fconv (spec_all eq_sym)))) >> rw[] (*almost equally stupid*)
 (*stupid *) (*rpt strip_tac >> dimp_tac >> rpt strip_tac >--
 (qex_tac ‘a’ >> arw[]) >> qex_tac ‘x0’ >> arw[]*))
(form_goal
“!X pred:X->1+1.?A ss:A ->X. Mono(ss) & 
 (!K x:K->X. pred o x = True(K) <=> ?x0:K->A. x = ss o x0)”));
end

val Swap_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac ‘Pa(p2(A,B),p1(A,B))’ >> rw[])
(form_goal
 “!A B. ?swap:A * B ->B * A. Pa(p2(A,B),p1(A,B)) = swap”)

val Swap_def = 
    Swap_ex |> spec_all |> eqT_intro
               |> iffRL |> ex2fsym "Swap" ["A","B"] 
               |> C mp (trueI []) |> gen_all
               |> store_as "Swap_def";


val Swap_property = proved_th $
e0
(rw[GSYM Swap_def,p12_of_Pa])
(form_goal
 “!A B. p1(B,A) o Swap(A,B) = p2(A,B) & p2(B,A) o Swap(A,B) = p1(A,B)”)


val Swap_Swap_id = prove_store("Swap_Swap_id",
e0
(rpt strip_tac >> irule to_P_eq >> rw[GSYM Swap_def,idR] >>
 rw[Pa_distr,p12_of_Pa])
(form_goal
 “!A B. Swap(B,A) o Swap(A,B) = id(A * B)”));

val has_components = prove_store("has_components",
e0
(rpt strip_tac >>
 qexistsl_tac [‘p1(A,B) o ab’,‘p2(A,B) o ab’] >>
 rw[GSYM to_P_component])
(form_goal
 “!X A B ab:X->A * B.
  ?a b. ab = Pa(a,b)”));



val Refl_Diag = prove_store("Refl_Diag",
e0
(rw[Refl_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac >> qexists_tac ‘d’ (* 2 *)
 >-- (arw[GSYM Diag_def,Pa_distr,Pa_eq_eq]) >>
 fs[GSYM Diag_def,Pa_distr,Pa_eq_eq])
(form_goal
 “!R A f0:R->A f1. Refl(f0,f1) <=>
  ?d:A->R. Pa(f0,f1) o d = Diag(A)”));


val Sym_alt = prove_store("Sym_alt",
e0
(rw[Sym_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘t’ >> arw[Pa_distr,Pa_eq_eq]) >>
 qexists_tac ‘d’ >> fs[Pa_distr,Pa_eq_eq] >>
 fs[GSYM Diag_def,Pa_distr,Pa_eq_eq])
(form_goal
 “!R A f0:R->A f1. Sym(f0,f1) <=>
  ?d:R ->R. Pa(f0,f1) o d = Pa(f1,f0)”));

val Pa_Swap_Mono0 = prove_store("Pa_Swap_Mono0",
e0
(rw[Mono_def] >> rpt strip_tac >>
 first_x_assum irule >>
 qby_tac
 ‘Swap(B,A) o Pa(f1, f0) o g = 
  Swap(B,A) o Pa(f1, f0) o h’ 
 >-- arw[] >>
 fs[GSYM Swap_def,GSYM o_assoc,Pa_distr,p12_of_Pa])
(form_goal
 “!R A B f0:R->A f1:R->B. Mono(Pa(f0,f1)) ==> Mono(Pa(f1,f0))”));


val Swap_Mono = prove_store("Swap_Mono",
e0
(strip_tac >> strip_tac >> strip_tac >>
 strip_tac >> once_rw[to_P_component] >>
 rpt strip_tac >> drule Pa_Swap_Mono0 >>
 rw[GSYM Swap_def,GSYM o_assoc,p12_of_Pa] >>
 first_x_assum accept_tac)
(form_goal
 “!R A B f:R->A * B. Mono(f) ==> Mono(Swap(A,B) o f)”));




val dflip_tac = 
fconv_tac 
 (basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))



val p21_Swap = prove_store("p12_Swap",
e0
(rpt strip_tac >> rw[GSYM Swap_def] >>
 irule to_P_eq >> rw[p12_of_Pa,GSYM o_assoc])
(form_goal
 “!R A B f:R->A * B. Pa(p2(A,B) o f,p1(A,B) o f) = Swap(A,B) o f”));



val Trans_alt = prove_store("Trans_alt",
e0
(rw[Trans_def] >> rpt strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *) >-- 
 (qby_tac ‘p1(A,A) o Pa(f0, f1) o r01 = 
           p1(A,A) o Pa(h0, h1) & 
           p2(A,A) o Pa(f0, f1) o r01 =
           p2(A,A) o Pa(h0, h1) & 
           p1(A,A) o Pa(f0, f1) o r12 = 
           p1(A,A) o Pa(h1, h2) & 
           p2(A,A) o Pa(f0, f1) o r12 =
           p2(A,A) o Pa(h1, h2)’ 
  >-- arw[] >>
  fs[GSYM o_assoc,p12_of_Pa] >>
  qby_tac ‘f1 o r01 = f0 o r12’ >-- arw[] >>
  first_x_assum drule >> pop_assum strip_assume_tac >>
  qexists_tac ‘u’ >> arw[Pa_distr,Pa_eq_eq]) >>
 qsuff_tac
 ‘?u:X->R. Pa(f0,f1) o u = Pa(f0 o h0, f1 o h1)’ >--
 (strip_tac >> qexists_tac ‘u’ >> 
  fs[Pa_distr,Pa_eq_eq]) >>
 first_x_assum irule >>
 qexistsl_tac [‘f1 o h0’,‘h0’,‘h1’] >>
 rw[Pa_distr,Pa_eq_eq] >> arw[])
(form_goal
 “!R A f0:R->A f1:R->A. Trans(f0,f1) <=>
  !X h0:X->A h1:X->A h2:X->A r01:X->R r12:X ->R .
  Pa(f0,f1) o r01 = Pa(h0,h1) &  Pa(f0,f1) o r12 = Pa(h1,h2) ==> ?r02. Pa(f0,f1) o r02 = Pa(h0,h2)”));



val prop_2_half2' = prove_store("prop_2_half2",
e0
(rpt strip_tac >> cases_on “is0(Y)” (* 2 *) >--
 (qby_tac ‘is0(X)’ >--
  (ccontra_tac >> 
   qsuff_tac ‘?y:1->Y.T’ >-- 
   (rw[] >> irule zero_no_MEM >> arw[]) >>
   drule NONZERO_EL >>
   pop_assum strip_assume_tac >>
   first_x_assum (qspecl_then [‘a o x’,‘x’] assume_tac) >>
   fs[] >> qexists_tac ‘xb'’ >> rw[]) >>
  fs[is0_expand] >>
  first_assum (qspecl_then [‘Y’] strip_assume_tac) >>
  qexists_tac ‘f’ >> 
  first_assum (qspecl_then [‘A’] strip_assume_tac) >>
  first_assum (qspecl_then [‘b o f’] strip_assume_tac) >>
  first_assum (qspecl_then [‘a’] strip_assume_tac) >>
  fs[]) >>
 drule Mono_no_zero_post_inv >> first_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘g o a’ >> irule FUN_EXT >>
 strip_tac >> 
 first_assum (qspecl_then [‘a o a'’,‘a'’] assume_tac) >>
 fs[] >> pop_assum (assume_tac o GSYM) >> arw[o_assoc] >>
 qby_tac ‘b o g o b o xb' = b o (g o b) o xb'’
 >-- rw[o_assoc] >>
 arw[idL])
(form_goal
 “!X A a:X->A Y b:Y->A. Mono(b) ==>
  (!x:1->A xb:1->X. a o xb = x ==> ?xb':1->Y. b o xb' = x)
  ==> ?h:X->Y. b o h = a”));


val Trans_alt' = prove_store("Trans_alt",
e0
(rw[Trans_alt] >> rpt strip_tac >>
 dimp_tac >> rpt strip_tac >-- 
 (first_x_assum irule >> 
 qexistsl_tac [‘h1’,‘r01’,‘r12’] >> arw[]) >>
 irule prop_2_half2' >> arw[] >>
 rpt strip_tac >>
 fs[Pa_eq_eq,Pa_distr] >>
 first_assum 
 (qspecl_then [‘h0 o xb’,‘h1 o xb’,‘h2 o xb’,
               ‘r01 o xb’,‘r12 o xb’]
 assume_tac) >>
 fs[GSYM o_assoc] >> rfs[] >>
 qexists_tac ‘r02’ >> arw[Pa_distr,Pa_eq_eq])
(form_goal
 “!R A f0:R->A f1:R->A. Mono(Pa(f0,f1)) ==> (Trans(f0,f1) <=>
  !h0:1->A h1:1->A h2:1->A r01:1->R r12:1 ->R .
  Pa(f0,f1) o r01 = Pa(h0,h1) &  Pa(f0,f1) o r12 = Pa(h1,h2) ==> ?r02. Pa(f0,f1) o r02 = Pa(h0,h2))”));

val Swap_Pa = prove_store("Swap_Pa",
e0
(rpt strip_tac >> rw[GSYM Swap_def] >> rw[Pa_distr,Pa_eq_eq,p12_of_Pa])
(form_goal “!X A f:X->A B g:X->B. Swap(A,B) o Pa(f,g) = Pa(g,f)”));


val p31_ex = prove_store("p31_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p31: A * B * C ->A. p1(A,B * C) = p31”));

val p31_def = p31_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p31" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all

val p32_ex = prove_store("p32_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(B,C) o p2(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p32: A * B * C ->B.p1(B,C) o p2(A,B * C) = p32”));

val p32_def = p32_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p32" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all

val p33_ex = prove_store("p33_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(B,C) o p2(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p33: A * B * C ->C.p2(B,C) o p2(A,B * C) = p33”));

val p33_def = p33_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p33" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all


val p31_of_Pa = prove_store("p31_of_Pa",
                            e0
                                (rpt strip_tac >> rw[GSYM p31_def,p1_of_Pa] )
                                (form_goal
                                     “!A B C X a:X-> A bc: X-> B * C. p31(A,B,C) o Pa(a, bc) = a”));


val p32_of_Pa = prove_store("p32_of_Pa",
e0
(rpt strip_tac >> rw[GSYM p32_def,o_assoc,p12_of_Pa] )
(form_goal
“!A B C X a:X-> A b: X-> B c: X-> C. p32(A,B,C) o Pa(a, Pa(b,c)) = b”));


val p33_of_Pa = prove_store("p33_of_Pa",
e0
(rpt strip_tac >> rw[GSYM p33_def,o_assoc,p2_of_Pa] )
(form_goal
“!A B C X a:X-> A b: X-> B c: X-> C. p33(A,B,C) o Pa(a, Pa(b,c)) = c”));





val Pa3_ex = prove_store("Pa3_ex",
e0
(rpt strip_tac >> qexists_tac ‘Pa(f,Pa(g,h))’ >> rw[])
(form_goal
 “!A B C X f:X->A g:X ->B h:X->C. ?Pa3.
 Pa(f,Pa(g,h)) = Pa3 
”));


val Pa3_def = Pa3_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa3" ["f","g","h"]
              |> C mp (trueI []) |> gen_all

val Pa4_ex = prove_store("Pa4_ex",
e0
(rpt strip_tac >> qexists_tac ‘Pa(f,Pa(g,Pa(h,j)))’ >> rw[])
(form_goal
 “!A B C D X f:X->A g:X ->B h:X->C j:X->D. ?Pa4.
 Pa(f,Pa(g,Pa(h,j))) = Pa4
”));

val Pa4_def = Pa4_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa4" ["f","g","h","j"]
              |> C mp (trueI []) |> gen_all

val p41_ex = prove_store("p41_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A, B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p41. p1(A,B * C * D) = p41”));

val p41_def = p41_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p41" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val p42_ex = prove_store("p42_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p42. p1(B, C * D) o p2(A,B * C * D) = p42”));


val p42_def = p42_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p42" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p43_ex = prove_store("p43_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p43. p1(C,D) o p2(B, C * D) o p2(A,B * C * D) = p43”));


val p43_def = p43_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p43" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p44_ex = prove_store("p44_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p44. p2(C,D) o p2(B, C * D) o p2(A,B * C * D) = p44”));


val p44_def = p44_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p44" ["A","B","C","D"]
                     |> C mp (trueI []) |> gen_all

fun mk_o a1 a2 = mk_fun "o" [a1,a2]

val CONJ = mk_fun "CONJ" []

fun Pa f g = mk_fun "Pa" [f,g]

fun Ex X = mk_fun "Ex" [X]

fun Tp f = mk_fun "Tp" [f]

val IMP = mk_fun "IMP" []

val two = rastt "1+1";



val p31_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p31_def,p1_of_Pa])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p31(A,B,C) o Pa3(f,g,h) = f”)



val p32_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p32_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p32(A,B,C) o Pa3(f,g,h) = g”)


val p33_of_Pa3 = prove_store("p33_of_Pa3",
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p33_def,p2_of_Pa,o_assoc])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p33(A,B,C) o Pa3(f,g,h) = h”));




val Ev_of_Tp_el' = prove_store("Ev_of_Tp_el'",
e0
(rpt strip_tac >> 
 qby_tac ‘Tp(f) = Tp(f) o id(P)’ >-- rw[idR] >>
 once_arw[] >> rw[Ev_of_Tp_el])
(form_goal
“!A B P f:A * P -> B  a:P -> A.
Ev(A, B) o Pa(a, Tp(f)) = f o Pa(a, id(P))”));


val Ev_of_el = prove_store("Ev_of_el",
e0
(rpt strip_tac >>
 qby_tac 
 ‘f = Tp1(Tp0(f))’ >-- rw[Tp1_Tp0_inv] >> once_arw[] >>
 rw[GSYM Tp1_def,Ev_of_Tp_el'] >> rw[Tp1_def,Tp1_Tp0_inv] >>
 rw[o_assoc,p1_of_Pa,idR])
(form_goal
 “!A B f:1->Exp(A,B) a:1->A.
  Ev(A,B) o Pa(a,f) = Tp0(f) o a”));

fun Po A B = mk_fun "*" [A,B]





val p41_of_Pa4 = prove_store("p41_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p41_def,p12_of_Pa])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p41(A,B,C,D) o Pa4(f,g,h,k) = f”));

val p42_of_Pa4 = prove_store("p42_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p42_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p42(A,B,C,D) o Pa4(f,g,h,k) = g”));


val p43_of_Pa4 = prove_store("p43_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p43_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p43(A,B,C,D) o Pa4(f,g,h,k) = h”));


val p44_of_Pa4 = prove_store("p44_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p44_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p44(A,B,C,D) o Pa4(f,g,h,k) = k”));



val Pa5_ex = prove_store("Pa5_ex",
e0
(rpt strip_tac >> qexists_tac ‘Pa(f,Pa(g,Pa(h,Pa(j,k))))’ >> rw[])
(form_goal
 “!A B C D E X f:X->A g:X ->B h:X->C j:X->D k:X->E. ?Pa5.
 Pa(f,Pa(g,Pa(h,Pa(j,k)))) = Pa5
”));

val Pa5_def = Pa5_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa5" ["f","g","h","j","k"]
              |> C mp (trueI []) |> gen_all



val p51_ex = prove_store("p51_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A, B * C * D * E)’ >> rw[])
(form_goal 
 “!A B C D E. ?p51. p1(A,B * C * D * E) = p51”));

val p51_def = p51_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p51" ["A","B","C","D","E"]
              |> C mp (trueI []) |> gen_all



val p52_ex = prove_store("p52_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(B,C * D * E) o p2(A,B * C * D * E)’ >> rw[])
(form_goal 
 “!A B C D E. ?p52. p1(B,C * D * E) o p2(A,B * C * D * E) = p52”));

val p52_def = p52_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p52" ["A","B","C","D","E"]
              |> C mp (trueI []) |> gen_all


val p53_ex = prove_store("p53_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(C,D * E) o p2(B,C * D * E) o p2(A,B * C * D * E)’ >> rw[])
(form_goal 
 “!A B C D E. ?p53.  p1(C,D * E) o p2(B,C * D * E) o p2(A,B * C * D * E) = p53”));

val p53_def = p53_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p53" ["A","B","C","D","E"]
              |> C mp (trueI []) |> gen_all

val p54_ex = prove_store("p54_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(D,E) o p2(C,D * E) o p2(B,C * D * E) o p2(A,B * C * D * E)’ >> rw[])
(form_goal 
 “!A B C D E. ?p54. p1(D,E) o p2(C,D * E) o p2(B,C * D * E) o p2(A,B * C * D * E) = p54”));

val p54_def = p54_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p54" ["A","B","C","D","E"]
              |> C mp (trueI []) |> gen_all


val p55_ex = prove_store("p55_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(D,E) o p2(C, D * E) o p2(B,C * D * E) o p2(A,B * C * D * E)’ >> rw[])
(form_goal 
 “!A B C D E. ?p55. p2(D,E) o p2(C, D * E) o p2(B,C * D * E) o p2(A,B * C * D * E) = p55”));


val p55_def = p55_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p55" ["A","B","C","D","E"]
              |> C mp (trueI []) |> gen_all





val p51_of_Pa5 = prove_store("p51_of_Pa5",
e0
(rpt strip_tac >> rw[GSYM Pa5_def,GSYM p51_def,p12_of_Pa])
(form_goal
“!A B C D E X f:X->A g:X->B h:X->C j:X->D k:X->E.
 p51(A,B,C,D,E) o Pa5(f,g,h,j,k) = f”));


val p52_of_Pa5 = prove_store("p52_of_Pa5",
e0
(rpt strip_tac >> rw[GSYM Pa5_def,GSYM p52_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D E X f:X->A g:X->B h:X->C j:X->D k:X->E.
 p52(A,B,C,D,E) o Pa5(f,g,h,j,k) = g”));


val p53_of_Pa5 = prove_store("p53_of_Pa5",
e0
(rpt strip_tac >> rw[GSYM Pa5_def,GSYM p53_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D E X f:X->A g:X->B h:X->C j:X->D k:X->E.
 p53(A,B,C,D,E) o Pa5(f,g,h,j,k) = h”));


val p54_of_Pa5 = prove_store("p54_of_Pa5",
e0
(rpt strip_tac >> rw[GSYM Pa5_def,GSYM p54_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D E X f:X->A g:X->B h:X->C j:X->D k:X->E.
 p54(A,B,C,D,E) o Pa5(f,g,h,j,k) = j”));






val p55_of_Pa5 = prove_store("p55_of_Pa5",
e0
(rpt strip_tac >> rw[GSYM Pa5_def,GSYM p55_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C j:X->D k:X->E.
 p55(A,B,C,D,E) o Pa5(f,g,h,j,k) = k”));


val Tp0_INJ = prove_store("Tp0_INJ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >-- 
 (once_rw[GSYM Tp1_Tp0_inv] >> arw[]) >> arw[])
(form_goal
 “!A B f:1->Exp(A,B) g:1->Exp(A,B).
  Tp0(f) = Tp0(g) <=> f = g”));

val pred_ext = prove_store("pred_ext",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (cases_on “p1:1->1+1 = TRUE” >-- fs[] >>
 fs[TRUE2FALSE] >> fs[TRUE_ne_FALSE] >>
 fs[TRUE2FALSE]) >>
 arw[])
(form_goal
“!p1 p2. (p1 = TRUE <=> p2 = TRUE) <=> p1 = p2”));

fun Pow A = Exp A two

fun Tp0 f = mk_fun "Tp0" [f]


val Pre_ex = prove_store("Pre_ex",
e0
(rpt strip_tac >> qexistsl_tac [‘PRE o n’] >> rw[])
(form_goal “!X n:X->N. ?pn. PRE o n = pn”));

val Pre_def = Pre_ex |> spec_all |> ex2fsym0 "Pre" ["n"]
                     |> gen_all |> store_as "Pre_def";




val Mem_ex = prove_store("Mem_ex",
e0
(strip_tac >> qexists_tac ‘Ev(X,1+1)’ >> rw[])
(form_goal
 “!X. ?mem. Ev(X,1+1) = mem”));

val Mem_def = Mem_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Mem" ["X"]
             |> C mp (trueI []) |> gen_all



val _ = new_pred "IN" [("a",ar_sort (mk_ob "X") (mk_ob "A")),
                       ("as",ar_sort (mk_ob "X") (Exp (mk_ob "A") two))]

val IN_def = store_ax("IN_def",
“!X A a:X->A ss:X->Exp(A,1+1). 
 IN(a,ss) <=> Mem(A) o Pa(a,ss) = True(X)”);

val IN_def1 = prove_store("IN_def1",
e0
(rw[True1TRUE,IN_def])
(form_goal “!A a:1->A ss:1->Exp(A,1+1). 
 IN(a,ss) <=> Mem(A) o Pa(a,ss) = TRUE”));



val IN_EXT = prove_store("IN_EXT",
e0
(rw[IN_def,GSYM Mem_def] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac >> arw[] >> irule Ev_eq_eq >> 
 fs[True1TRUE,pred_ext] >> irule FUN_EXT >>
 rpt strip_tac >> rw[Pa_distr,o_assoc] >>
 once_rw[one_to_one_id] >> rw[idR] >> arw[])
(form_goal “!X s1:1-> Exp(X,1+1) s2.
 s1 = s2 <=> (!x.IN(x,s1) <=> IN(x,s2))”));






(*singleton*)
val Sing_ex = prove_store("Sing_ex",
e0
(strip_tac >> qexists_tac ‘Tp(Char(Diag(A)))’ >>
 rw[])
(form_goal “!A. ?Sing. Tp(Char(Diag(A))) = Sing”));

val Sing_def = Sing_ex |> spec_all 
                       |> ex2fsym0 "Sing" ["A"]
                       |> store_as "Sing_def";



(*sigma*)
val Sig_ex = prove_store("Sig_ex",
e0
(strip_tac >> qexists_tac ‘Char(Sing(A))’ >>
 rw[])
(form_goal “!A. ?Sig. Char(Sing(A)) = Sig”));

val Sig_def = Sig_ex |> spec_all 
                       |> ex2fsym0 "Sig" ["A"]
                       |> store_as "Sig_def";


val pred_ext' = prove_store("pred_ext'",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 irule FUN_EXT >> strip_tac >> 
 once_rw[GSYM pred_ext] >> arw[])
(form_goal
 “!X p1:X->1+1 p2. 
  (!x. p1 o x = TRUE <=> p2  o x = TRUE) <=> p1 = p2”));

val Sing_Mono = prove_store("Sing_Mono",
e0
(strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qby_tac ‘Mem(B) o Pa(p1(B,B),Sing(B) o p2(B,B))
          = Eq(B)’
 >-- rw[GSYM Mem_def,GSYM Sing_def,GSYM Eq_def,
        Ev_of_Tp] >> 
 qby_tac ‘Eq(B) o Pa(p1(B,X),g o p2(B,X)) = 
          Eq(B) o Pa(p1(B,X),h o p2(B,X))’
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[o_assoc,Pa_distr,p12_of_Pa] >>
     arw[GSYM o_assoc]) >>
 irule FUN_EXT >> strip_tac >>
 qsuff_tac ‘!a'. g o a = a' <=> h o a = a'’ >--
 (rpt strip_tac >> 
 first_x_assum (qspecl_then [‘g o a’] assume_tac) >>
 fs[]) >>
 strip_tac >> 
 pop_assum mp_tac >>
 once_rw[GSYM pred_ext'] >> 
 strip_tac >>
 first_x_assum 
  (qspecl_then [‘Pa(a',a)’] assume_tac) >>
 fs[o_assoc,Pa_distr,p12_of_Pa,Eq_property_TRUE] >>
 dflip_tac >> arw[])
(form_goal “!B. Mono(Sing(B))”));



val Mem_Sing = prove_store("Mem_Sing",
e0
(rw[GSYM Mem_def,GSYM Sing_def] >>
 rw[Ev_of_Tp_el] >> rw[Char_Diag,GSYM TRUE_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!B b0:1->B b. Mem(B) o Pa(b,Sing(B) o b0) = TRUE<=>
 b0 = b ”));

val Rel_U_fac = prove_store("Rel_U_fac",
e0
(rpt strip_tac>> irule prop_2_half2' >>
 rw[Sing_Mono] >> rpt strip_tac >>
 first_x_assum (qsspecl_then [‘xb’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘b’ >> 
 once_rw[IN_EXT] >>
 rw[IN_def,True1TRUE] >>
 rw[Mem_Sing] >> 
 rw[GSYM Mem_def] >>
 last_x_assum (assume_tac o GSYM) >> arw[] >>
 rw[Ev_of_Tp_el] >>
 strip_tac >> dimp_tac >> strip_tac >--
 (pop_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum drule >> arw[])
(form_goal
 “!A B R:B * A -> 1+1.
    (!a:1->A.?!b:1->B. R o Pa(b,a) = TRUE) ==>
    ?f:A->B. Sing(B) o f = Tp(R)”));


val Rel2Ar = prove_store("Rel2Ar",
e0
(rpt strip_tac >> drule Rel_U_fac >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘h’ >>
 rpt strip_tac >> 
 qby_tac
 ‘Mem(B) o Pa(b,Sing(B) o h o a) = Mem(B) o Pa(b,Tp(R) o a)’
 >-- arw[GSYM o_assoc] >>
 fs[GSYM Mem_def,GSYM Sing_def,Ev_of_Tp_el] >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Char_Diag,GSYM TRUE_def] >> rflip_tac >> rw[]
 )
(form_goal
 “!A B R:B * A -> 1+1. 
   (!a:1->A.?!b:1->B. R o Pa(b,a) = TRUE) ==>
   (?f:A->B. !a b. f o a = b <=> R o Pa(b,a) = TRUE)”));


val Rel2Ar' = prove_store("Rel2Ar'",
e0
(rpt strip_tac >> 
 assume_tac Rel2Ar >>
 qby_tac
 ‘?R'. !a b. R' o Pa(b,a) = TRUE <=> 
  R o Pa(a,b) = TRUE’
 >-- (qexists_tac ‘R o Swap(B,A)’ >>
     rw[o_assoc,Swap_Pa]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘!a:1->A. ?!b.R' o Pa(b,a) = TRUE’ 
 >-- (strip_tac >>uex_tac >>
     last_x_assum 
     (qspecl_then [‘a’] (strip_assume_tac o uex_expand)) >>
     qexists_tac ‘b’ >> arw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >>
 fs[])
(form_goal
 “!A B R:A * B -> 1+1. 
   (!a:1->A.?!b:1->B. R o Pa(a,b) = TRUE) ==>
   (?f:A->B. !a b. f o a = b <=> R o Pa(a,b) = TRUE)”));



val Fst_ex = prove_store("Fst_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A,B) o ab’ >> rw[])
(form_goal “!X A B ab:X->A * B. ?fst.p1(A,B) o ab = fst”));


val Snd_ex = prove_store("Snd_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(A,B) o ab’ >> rw[])
(form_goal “!X A B ab:X->A * B. ?snd.p2(A,B) o ab = snd”));

val Fst_def = Fst_ex |> spec_all |> ex2fsym0 "Fst" ["ab"]
                     |> gen_all
                     |> store_as "Fst_def";



val Snd_def = Snd_ex |> spec_all |> ex2fsym0 "Snd" ["ab"]
                     |> gen_all
                     |> store_as "Snd_def";

val Fst_Snd_Pa = p12_of_Pa |> rewr_rule[Fst_def,Snd_def]
                           |> store_as "Fst_Snd_Pa";

val Fst_Pa = p1_of_Pa |> rewr_rule[Fst_def] |> store_as "Fst_Pa";

val Snd_Pa = p2_of_Pa |> rewr_rule[Snd_def] |> store_as "Snd_Pa";


val And_ex = prove_store("And_ex",
e0
(rpt strip_tac >> qexists_tac ‘CONJ o Pa(p,q)’ >> rw[])
(form_goal “!X p:X->1+1 q. ?pq. CONJ o Pa(p,q) = pq”));

val And_def = And_ex |> spec_all
                     |> ex2fsym0 "And" ["p","q"]
                     |> gen_all
                     |> store_as "And_def";

val And_property = rewr_rule[And_def] CONJ_def


val Or_ex = prove_store("Or_ex",
e0
(rpt strip_tac >> qexists_tac ‘DISJ o Pa(p,q)’ >> rw[])
(form_goal “!X p:X->1+1 q. ?pq. DISJ o Pa(p,q) = pq”));

val Or_def = Or_ex |> spec_all
                   |> ex2fsym0 "Or" ["p","q"]
                   |> gen_all
                   |> store_as "Or_def";

val Or_property = rewr_rule[Or_def] DISJ_def;


val Imp_ex = prove_store("Imp_ex",
e0
(rpt strip_tac >> qexists_tac ‘IMP o Pa(p,q)’ >> rw[])
(form_goal “!X p:X->1+1 q. ?pq. IMP o Pa(p,q) = pq”));

val Imp_def = Imp_ex |> spec_all
                   |> ex2fsym0 "Imp" ["p","q"]
                   |> gen_all
                   |> store_as "Imp_def";

val Imp_property = rewr_rule[Imp_def] IMP_def;


val Iff_ex = prove_store("Iff_ex",
e0
(rpt strip_tac >> qexists_tac ‘IFF o Pa(p,q)’ >> rw[])
(form_goal “!X p:X->1+1 q. ?pq. IFF o Pa(p,q) = pq”));

val Iff_def = Iff_ex |> spec_all
                   |> ex2fsym0 "Iff" ["p","q"]
                   |> gen_all
                   |> store_as "Iff_def";

val Iff_property = rewr_rule[Iff_def] IFF_def;


val ALL_ex = prove_store("ALL_ex",
e0
(rpt strip_tac >> qexists_tac ‘All(X) o Tp(p)’ >> rw[])
(form_goal “!X Y p:X * Y -> 1+1. ?ap.All(X) o Tp(p) = ap”));

val ALL_def = ALL_ex |> spec_all |> ex2fsym0 "ALL" ["p"]
                     |> gen_all |> store_as "ALL_def";


val ALL_property = All_def |> rewr_rule[GSYM o_assoc,ALL_def]


val EX_ex = prove_store("EX_ex",
e0
(rpt strip_tac >> qexists_tac ‘Ex(X) o Tp(p)’ >> rw[])
(form_goal “!X Y p:X * Y -> 1+1. ?ep.Ex(X) o Tp(p) = ep”));

val EX_def = EX_ex |> spec_all |> ex2fsym0 "EX" ["p"]
                     |> gen_all |> store_as "EX_def";

val EX_property = Ex_def |> rewr_rule[GSYM o_assoc,EX_def]


val UE_ex = prove_store("UE_ex",
e0
(rpt strip_tac >> qexists_tac ‘E1(X) o Tp(p)’ >> rw[])
(form_goal “!X Y p:X * Y -> 1+1. ?uep.E1(X) o Tp(p) = uep”));

val UE_def = UE_ex |> spec_all |> ex2fsym0 "UE" ["p"]
                   |> gen_all |> store_as "UE_def";

val UE_property = E1_def |> rewr_rule[GSYM o_assoc,UE_def]

val EQ_ex = prove_store("EQ_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eq(X) o Pa(f,g)’ >> rw[])
(form_goal “!A X f:A->X g. ?fg. Eq(X) o Pa(f,g) = fg”));

val EQ_def = EQ_ex |> spec_all |> ex2fsym0 "EQ" ["f","g"]
                   |> gen_all |> store_as "EQ_def";

val EQ_property_TRUE = Eq_property_TRUE 
                           |> rewr_rule[EQ_def]

val EQ_property = Eq_property
                           |> rewr_rule[EQ_def]



val Not_ex = prove_store("Not_ex",
e0
(rpt strip_tac >> qexists_tac ‘NEG o p’ >> rw[])
(form_goal “!X p:X->1+1. ?np. NEG o p = np”));

val Not_def = Not_ex |> spec_all
                     |> ex2fsym0 "Not" ["p"]
                     |> gen_all
                     |> store_as "Not_def";

val Not_property = rewr_rule[Not_def] NEG_def;
