

val _ = new_sort "cat" [];

val _ = new_sort "fun" [("A",mk_sort "cat" []),("B",mk_sort "cat" [])]

val _ = new_sort_infix "fun" "->"

val cat_sort = mk_sort "cat" []
fun fun_sort A B = mk_sort "fun" [A,B]
fun mk_cat A = mk_var(A,cat_sort)
fun mk_fun F A B = mk_var(F,fun_sort A B)

val _ = EqSorts := "fun" :: (!EqSorts)

 

val _ = new_sort "nt" [("f",fun_sort (mk_cat "A") (mk_cat "B")),
                       ("g",fun_sort (mk_cat "A") (mk_cat "B"))]


val _ = new_fun "o" (mk_sort "fun" [mk_var("A",mk_sort "cat" []),mk_var("C",mk_sort "cat" [])],[("f",mk_sort "fun" [mk_var("B",mk_sort "cat" []),mk_var("C",mk_sort "cat" [])]),("g",mk_sort "fun" [mk_var("A",mk_sort "cat" []),mk_var("B",mk_sort "cat" [])])])


fun ex2fsym0 name args th = th |> eqT_intro |> iffRL |> ex2fsym name args
                               |> C mp (trueI []) 

fun uex_expand th = rewr_rule [uex_def $ concl th] th

val isPr_def = define_pred
“!A B AB p1:AB->A p2:AB->B. isPr(p1,p2) <=>
   !X f:X->A g:X->B.?!fg:X->AB. p1 o fg = f & p2 o fg = g”

val isPr_ex = store_ax("isPr_ex",“!A B.?AB p1:AB->A p2:AB->B.isPr(p1,p2)”);

val Po_def = isPr_ex |> spec_all |> ex2fsym0 "*" ["A","B"] |> gen_all |> store_as "Po_def"

val p1_def = Po_def |> spec_all |> ex2fsym0 "p1" ["A","B"] |> gen_all |> store_as "p1_def"

val p2_def = p1_def |> spec_all |> ex2fsym0 "p2" ["A","B"] |> gen_all |> store_as "p2_def"


val Pa_def = p2_def |> rewr_rule[isPr_def] |> spec_all
                    |> uex_expand 
                    |> ex2fsym0 "Pa" ["f","g"] |> gen_all
                    |> store_as "Pa_def"

val _ = add_parse 0x1D7D8

val _ = add_parse 120793




val isEq_def = define_pred
“!A B f:A->B g E e:E->A. 
      isEq(f,g,e) <=> 
      f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0”

val isEq_ex = store_ax("isEq_ex",“!A B f:A->B g:A->B.?E e:E->A.isEq(f,g,e)”)

val Eqa_def = 
    isEq_def |> iffLR 
             |> spec_all |> undisch |> conjE2 
             |> spec_all |> undisch |> uex_expand
             |> conj_all_assum |> disch_all
             |> ex2fsym "Eqa" ["f","g","e","a"]
             |> gen_all
             |> store_as "Eqa_def"
 

val is0_def = 
define_pred “!ZERO.is0(ZERO) <=> !X.?!f:ZERO ->X. T”


val ZERO_ex = store_ax("ZERO_ex",“?ZERO.is0(ZERO)”)

val ZERO_def = ex2fsym0 "0" [] ZERO_ex |> store_as "ZERO_def"

val ZERO_prop = ZERO_def |> conv_rule (once_depth_fconv no_conv (rewr_fconv (spec_all is0_def))) |> store_as "ZERO_prop"

val From0_def = ZERO_prop |> spec_all |> uex_expand |> ex2fsym0 "From0" ["X"] |> gen_all |> store_as "From0_def"



val is1_def = define_pred
“!ONE. is1(ONE) <=> !X.?!f:X->ONE.T”



val ONE_ex = store_ax("ONE_ex",“?ONE.is1(ONE)”)
                    
val ONE_def = ex2fsym0 "1" [] ONE_ex |> store_as "ONE_def"

val ONE_prop = ONE_def |> rewr_rule [is1_def]
                       |> store_as "ONE_prop"

val To1_def = ONE_prop |> spec_all |> uex_expand |> ex2fsym0 "To1" ["X"] |> gen_all |> store_as "To1_def"



val _ = new_fun "id" 
       (mk_sort "fun" [mk_var("A",mk_sort "cat" []),mk_var("A",mk_sort "cat" [])],
        [("A",mk_sort "cat" [])])


val idL = store_ax("idL", “!B A f:B->A. id(A) o f = f”);

val idR = store_ax("idR",“!A B f:A->B. f o id(A) = f”);

val o_assoc = store_ax("o_assoc",“!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f”);


val _ = new_pred "Iso" [("f",fun_sort (mk_cat "A") (mk_cat "B"))]

val Iso_def = store_ax("Iso_def",
“!A B f:A->B. Iso(f) <=> ?f':B->A. f' o f = id(A) & f o f' = id(B)”);


val areIso_def = store_ax("areIso_def",
“!A B. areIso(A,B) <=> ?f:A->B g:B->A. f o g = id(B) & g o f = id(A)”)

val ZERO_not_ONE = store_ax("ZERO_not_ONE",
“~(?f:0->1. Iso(f))”)


val _ = new_fun "2" (cat_sort,[])

val _ = new_fun "0f" (fun_sort (rastt "1") (rastt "2"),[])

val _ = new_fun "1f" (fun_sort (rastt "1") (rastt "2"),[])


val isExp_def = define_pred
“!A B A2B ev:A * A2B -> B.
         isExp(ev) <=> !X f:A * X->B. ?!h:X->A2B. ev o Pa(p1(A,X), h o p2(A,X)) = f”




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


val _ = new_pred "isPb"
  [("f",fun_sort (mk_cat "X") (mk_cat "Z")),
   ("g",fun_sort (mk_cat "Y") (mk_cat "Z")),
   ("p",fun_sort (mk_cat "P") (mk_cat "X")),
   ("q",fun_sort (mk_cat "P") (mk_cat "Y"))];


val isPb_def = store_ax("isPb_def",
“!X H f:X -> H Y g : Y -> H P p : P -> X q : P -> Y.
 isPb(f, g, p, q) <=> f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v”);

val isPb_expand = isPb_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : A -> P. p:P->X o a = u & q:P->Y o a = v”) |> store_as "isPb_expand";

val isPb_ex = store_ax("isPb_ex",“!X H f:X->H Y g:Y->H. ?P p:P->X q. isPb(f,g,p,q)”);

val PCC1 = store_ax("PCC1",
“?p:0->1 q:0->1. isPb(0f,1f,p,q)”);


val zero_ex = prove_store("zero_ex",
e0
cheat
(form_goal
 “∃z:2->2. z = 0f o To1(2)”));  

val zero_def = zero_ex |> ex2fsym0 "𝟘" [] 


val one_ex = prove_store("one_ex",
e0
cheat
(form_goal
 “∃l:2->2. l = 1f o To1(2)”));  

val one_def = one_ex |> ex2fsym0 "𝟙" [] 

val CC2_0 = store_ax("CC2_0",“~(𝟘 = 𝟙) & ~(𝟘 = 𝟚) & ~(𝟙 = 𝟚)”)

val CC2_1 = store_ax ("CC2_1",“ ∀f:2->2. f = 𝟘 | f = 𝟙 | f = 𝟚”);


val CC2_2 = store_ax("CC2_2",
“!A B f:A->B g:A->B. ~(f = g) ==> ?a:2->A. ~(f o a = g o a)”);


val imp_lemma = proved_th $
e0
(dimp_tac >> strip_tac (* 3 *)
 >-- (cases_on “A” >-- arw[] >> first_x_assum drule >>
      arw[]) >>
 arw[])
(form_goal
 “~ A ==> B <=> B | A”)

val uex_tac:tactic = fn (ct,asl,w) =>
    let val th = uex_def w
        val w' = snd $ dest_dimp $ concl th
    in ([(ct,asl,w')],(sing (dimp_mp_r2l th)))
    end
 
val Thm1 = prove_store("Thm1",
e0
(strip_tac >> cases_on “0f o To1(C) = 1f o To1(C)” 
 >-- (strip_assume_tac PCC1 >> fs[isPb_def] >>
      first_x_assum rev_drule >>
      pop_assum (strip_assume_tac o uex_expand) >>
      qsuff_tac ‘~(?a1 : 2->C. T) ==> is0(C)’
      >-- rw[imp_lemma] >>
      strip_tac >> rw[is0_def] >> strip_tac >> uex_tac >>
      qexists_tac ‘From0(X) o a’ >> rw[] >> rpt strip_tac >>
      ccontra_tac >> drule CC2_2 >> fs[] >>
      qsuff_tac ‘?a1:2->C.T’ >-- (rw[] >>
      first_x_assum accept_tac) >>
      qexists_tac ‘a'’ >> rw[]) >>
 disj2_tac >> drule CC2_2 >> 
 pop_assum strip_assume_tac >> qexists_tac ‘a’ >> rw[])
(form_goal
 “!C. is0(C) | (?a:2->C.T)”) );

val iscoPr_def = define_pred
“!A B AB i1:A->AB i2:B->AB. iscoPr(i1,i2) <=>
   !X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g”




val iscoPr_ex = store_ax("iscoPr_ex",“!A B.?AB i1:A->AB i2:B->AB.iscoPr(i1,i2)”);

val coPo_def = iscoPr_ex |> spec_all |> ex2fsym0 "+" ["A","B"] |> gen_all |> store_as "coPo_def";

val i1_def = coPo_def |> spec_all |> ex2fsym0 "i1" ["A","B"] |> gen_all |> store_as "i1_def";

val i2_def = i1_def |> spec_all |> ex2fsym0 "i2" ["A","B"] |> gen_all |> store_as "i2_def";

val coPa_def = i2_def |> rewr_rule[iscoPr_def] |> spec_all
                      |> uex_expand 
                      |> ex2fsym0 "coPa" ["f","g"]
                      |> gen_all
                      |> store_as "coPa_def";


val _ = new_pred "Mono" [("f",fun_sort (mk_cat "A") (mk_cat "B"))]

val Mono_def = store_ax("Mono_def",“!A B f:A->B. Mono(f) <=> !X g:X->A h. f o g = f o h ==> g = h”);

val rfs = rev_full_simp_tac

val post_inv_Mono = prove_store("post_inv_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qby_tac
 ‘i o m o g = i o m o h’ >-- arw[] >>
 rfs[GSYM o_assoc] >> fs[idL])
(form_goal
 “!A B m:A->B i:B->A. i o m = id(A) ==> Mono(m)”));



val i12_of_coPa = coPa_def |> spec_all |> conjE1
                           |> gen_all 
                           |> store_as "i12_of_coPa";

val i1_of_coPa = i12_of_coPa |> spec_all |> conjE1
                             |> gen_all 
                             |> store_as "i1_of_coPa";


val i2_of_coPa = i12_of_coPa |> spec_all |> conjE2
                             |> gen_all 
                             |> store_as "i2_of_coPa";
 
val Thm2_1_i1 = prove_store("Thm2_1_i1",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 cases_on “g:X->A = h” >-- arw[] >>
 qsuff_tac ‘?f:B->A.T’
 >-- (strip_tac >> 
      qby_tac ‘coPa(id(A),f) o i1(A,B) = id(A)’
      >-- rw[i1_of_coPa] >>
      qby_tac ‘coPa(id(A),f) o i1(A, B) o g = coPa(id(A),f) o i1(A, B) o h’
      >-- arw[] >>
      rfs[GSYM o_assoc,idL]) >>
 drule CC2_2 >> pop_assum strip_assume_tac >>
 qexists_tac ‘g o a o 1f o To1(B)’ >> rw[])
(form_goal
 “!A B. Mono(i1(A,B))”));


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

val from0_unique = prove_store("form0_unique",
e0
(rpt strip_tac >>
 qspecl_then [‘X’,‘f’] assume_tac From0_def >>
 qspecl_then [‘X’,‘g’] assume_tac From0_def >> 
 arw[])
(form_goal
 “!X f:0->X g:0->X. f = g”));

val zero_to_zero_id = prove_store("zero_to_zero_id",
e0
(strip_tac >>
 qspecl_then [‘0’,‘f’,‘id(0)’] assume_tac from0_unique >>
 first_x_assum accept_tac)
(form_goal
 “!f:0->0. f = id(0)”))


val one_not_to_zero = prove_store("one_not_to_zero",
e0
(strip_tac >> assume_tac ZERO_not_ONE >>
 qsuff_tac ‘?g:0->1. Iso(g)’ >-- arw[] >>
 pop_assum (K all_tac) >>
 rw[Iso_def] >> qexistsl_tac [‘From0(1)’,‘f’] >>
 rw[zero_to_zero_id,one_to_one_id])
(form_goal “!f:1->0.F”));


val to0_is0 = prove_store("to0_is0",
e0
(rw[is0_def] >> rpt strip_tac >> uex_tac >>
 qexists_tac ‘From0(X) o f0’ >> rw[] >> rpt strip_tac >>
 ccontra_tac >> drule CC2_2 >> pop_assum strip_assume_tac >>
 qsspecl_then [‘f0 o a o 1f’] assume_tac one_not_to_zero >> 
 first_x_assum accept_tac)
(form_goal
 “!A f0:A->0. is0(A)”));

val Thm2_2 = prove_store("Thm2_2",
e0
(rw[isPb_def] >> rpt strip_tac >> strip_assume_tac PCC1 >>
 fs[isPb_def] >> 
 qsuff_tac ‘?u:P->1 v. 0f o u = 1f o v’
 >-- (strip_tac >> first_x_assum drule >> 
      pop_assum (strip_assume_tac o uex_expand) >>
      qsspecl_then [‘a’] accept_tac to0_is0) >> 
 qexistsl_tac [‘To1(A) o p’,‘To1(B) o q’] >>
 qby_tac 
  ‘coPa(0f o To1(A), 1f o To1(B)) o i1(A, B) o p = 
   coPa(0f o To1(A), 1f o To1(B)) o i2(A, B) o q’ 
 >-- arw[] >>
 fs[GSYM o_assoc,i12_of_coPa])
(form_goal
 “!A B P p:P->A q.isPb(i1(A,B),i2(A,B),p,q) ==> is0(P)”));

val Epi_def = store_ax("Epi_def",“!A B f:A->B. Epi(f) <=> !X g:B->X h. g o f = h o f ==> g = h”);

val CC3 = store_ax("CC3", “~Epi(coPa(0f,1f))”);

val isgen_def = define_pred
“!G. isgen(G) <=> !A B f1:A->B f2. ~(f1 = f2) ==> ?g: G -> A. ~(f1 o g = f2 o g)”


val isPb_def = store_ax("isPb_def",
“!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y.
 isPb(f, g, p, q) <=> f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v”);

val E_ex = prove_store("E_ex",
e0
(rw[isPo_ex])
(form_goal
 “∃E e1:2->E e2:2-> E. isPo(coPa(0f,1f),coPa(0f,1f),e1,e2)”));

val E_def = E_ex |> ex2fsym0 "E" [] |> ex2fsym0 "ε1" []
                 |> ex2fsym0 "ε2" [] |> store_as "E_def";

val Epi_iff_Po_id = prove_store("Epi_iff_Po_id",
e0
cheat
(form_goal
 “∀A B f:A->B. Epi(f) ⇔ isPo(f,f,id(B),id(B))”));

val iso_Po_Po = prove_store("iso_Po_Po",
e0
(cheat)
(form_goal
 “∀X A f:X->A B g:X->B P1 p1:A->P1 q1:B->P1. isPo(f,g,p1,q1) ⇒
  ∀P2 p2: A-> P2 q2: B -> P2 i:P1->P2 j: P2 -> P1.
  j o i = id(P1) & i o j = id(P2) ⇒ isPo(f,g,p2,q2)”));

val Po_equal_id = prove_store("Po_equal_id",
e0
(rpt strip_tac >>
 drule $ iffLR isPo_expand >>
 fs[] >>
 first_x_assum (qsspecl_then [‘id(B)’,‘id(B)’] assume_tac) >>
 fs[] >> drule iso_Po_Po >> first_x_assum irule >>
 qexistsl_tac [‘a’,‘p’] >>
 arw[] >>
 drule $ iffLR isPo_expand >> fs[] >>
 first_x_assum (qsspecl_then [‘p’,‘p’] assume_tac) >>
 fs[] >> 
 first_assum (qspecl_then [‘p o a’] assume_tac) >>
 first_x_assum (qspecl_then [‘id(P)’] assume_tac) >>
 rfs[idL,o_assoc,idR])
(form_goal “∀A B e:A->B P p:B->P. isPo(e,e,p,p) ⇒
 isPo(e,e,id(B),id(B))”));

val e1_ne_e2 = prove_store("e1_ne_e2",
e0
(ccontra_tac >>
 qsuff_tac ‘isPo(coPa(0f,1f),coPa(0f,1f),𝟚,𝟚)’
 >-- rw[GSYM Epi_iff_Po_id,two_def,CC3] >>
 assume_tac E_def >> rfs[two_def] >>
 drule Po_equal_id >> first_x_assum accept_tac
 )
(form_goal “~(ε1 = ε2)”));

val e1_e2_same_dom = prove_store("e1_e2_same_dom",
e0
(cheat)
(form_goal “dom(ε1) = dom(ε2)”));


val e1_e2_same_cod = prove_store("e1_e2_same_cod",
e0
(cheat)
(form_goal “cod(ε1) = cod(ε2)”));


val Thm3_1 = prove_store("Thm3_1",
e0
(rpt strip_tac >> fs[isgen_def] >>
 assume_tac e1_ne_e2 >> first_x_assum drule >>
 pop_assum strip_assume_tac >> drule CC2_2 >>
 pop_assum (x_choose_then "f" assume_tac) >>
 fs[o_assoc] >>
 qspecl_then [‘g o f’] strip_assume_tac CC2_1 (* 3 *)
 >-- (fs[zero_def] >> 
     fs[GSYM dom_def,GSYM o_assoc,e1_e2_same_dom])
 >-- (fs[one_def] >> 
     fs[GSYM cod_def,GSYM o_assoc,e1_e2_same_cod]) >>
 qexistsl_tac [‘f’,‘g’] >> arw[two_def])
(form_goal
 “!G. isgen(G) ==> ?s:2->G r:G->2. r o s = id(2)”));

(*all distinct*)


val areIso_def = store_ax("areIso_def",
“!A B. areIso(A,B) <=> ?f:A->B g:B->A. f o g = id(B) & g o f = id(A)”)

val distinct_three_lemma = prove_store("distinct_three_lemma",
e0
(rpt strip_tac >>
 first_assum (qspecl_then [‘g1’] strip_assume_tac) >>
 first_assum (qspecl_then [‘g2’] strip_assume_tac) >>
 first_assum (qspecl_then [‘g3’] strip_assume_tac) >> fs[] >>
 first_assum (qspecl_then [‘g’] strip_assume_tac) >> fs[])
(form_goal
 “∀A B f1 f2 f3:A->B. 
  ~(f1 = f2) & ~(f1 = f3) & ~(f2 = f3) &
  (∀f:A->B. f = f1 | f = f2 | f = f3) ⇒ 
  ∀g1 g2 g3:A->B. 
  ~(g1 = g2) & ~(g1 = g3) & ~(g2 = g3) ⇒ 
  ∀g:A->B. g = g1 | g = g2 | g = g3”));


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


val flip_tac = 
fconv_tac (rewr_fconv (eq_sym "fun"));


val dflip_tac = 
fconv_tac 
 (basic_once_fconv no_conv (rewr_fconv (eq_sym "fun")))

val Thm3_2 = prove_store("Thm3_2",
e0
(rpt strip_tac >> drule Thm3_1 >> 
 rw[areIso_def] >> 
 pop_assum (x_choosel_then ["f","g"] strip_assume_tac) >>
 qexistsl_tac [‘g’,‘f’] >> arw[] >>
 qby_tac
 ‘~(f o 0f o To1(2) o g = f o 1f o To1(2) o g)’
 >-- (ccontra_tac >>
     qby_tac 
     ‘g o (f o 0f o To1(2) o g) o f = 
      g o (f o 1f o To1(2) o g) o f’ 
     >-- arw[] >>
     rfs[GSYM o_assoc,idL] >> rfs[o_assoc,idR] >>
     fs[GSYM one_def,GSYM zero_def,CC2_0]) >>
 qby_tac
 ‘~(f o 0f o To1(2) o g = id(G))’
 >-- 
 (ccontra_tac >>
  qby_tac 
  ‘g o (f o 0f o To1(2) o g) o f = 
   g o (id(G)) o f’ 
  >-- arw[] >>
  rfs[GSYM o_assoc,idL] >> rfs[o_assoc,idR] >>
  rfs[GSYM two_def,GSYM zero_def,CC2_0,idL]) >>
 qby_tac
 ‘~(f o 1f o To1(2) o g = id(G))’
 >-- 
 (ccontra_tac >>
  qby_tac 
  ‘g o (f o 1f o To1(2) o g) o f = 
   g o (id(G)) o f’ 
  >-- arw[] >>
  rfs[GSYM o_assoc,idL] >> rfs[o_assoc,idR] >>
  rfs[GSYM two_def,GSYM one_def,CC2_0,idL]) >> 
 qsuff_tac ‘~(f o g = f o 1f o To1(2) o g) & 
            ~(f o g = f o 0f o To1(2) o g)’
 >-- (qby_tac ‘∀a: G->G. a = f o 1f o To1(2) o g | 
 a = f o 0f o To1(2) o g | a = id(G)’ 
     >-- (irule distinct_three_lemma >> arw[] >>
          dflip_tac >> arw[] >> dflip_tac >>
          qexistsl_tac [‘g1’,‘g2’,‘g3’] >> arw[]) >>
     first_x_assum (qspecl_then [‘f o g’] strip_assume_tac)>>
     rfs[]) >>
 strip_tac >> ccontra_tac (* 2 *)
 >-- (qby_tac
     ‘g o (f o g) o f = g o (f o 1f o To1(2) o g) o f’
     >-- arw[] >>
     rfs[GSYM o_assoc,idL] >> 
     rfs[o_assoc,idR] >> 
     fs[GSYM CC2_0,GSYM two_def,GSYM one_def]) >>
 qby_tac
 ‘g o (f o g) o f = g o (f o 0f o To1(2) o g) o f’
 >-- arw[] >>
 rfs[GSYM o_assoc,idL] >> 
 rfs[o_assoc,idR] >> 
 fs[GSYM CC2_0,GSYM two_def,GSYM zero_def])
(form_goal
 “!G. isgen(G) ⇒ 
  ∀g1 g2 g3:G->G. 
  ~(g1 = g2) & ~(g1 = g3) & ~(g2 = g3) & 
  (!e:G->G. e = g1 | e = g2 | e = g3) ⇒ 
  areIso(G,2)”));


val _ = new_pred "isPo"
  [("f",fun_sort (mk_cat "Z") (mk_cat "X")),
   ("g",fun_sort (mk_cat "Z") (mk_cat "Y")),
   ("p",fun_sort (mk_cat "X") (mk_cat "P")),
   ("q",fun_sort (mk_cat "Y") (mk_cat "P"))];


val isPo_def = store_ax("isPo_def",
“!H X f:H -> X Y g : H -> Y P p : X -> P q : Y -> P.
 isPo(f, g, p, q) <=> p o f = q o g &
 !A u : X -> A v : Y -> A. 
    u o f = v o g ==> 
    ?!a : P -> A. a o p = u & a o q = v”);

val isPo_expand = isPo_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : P -> A. a o p:X->P = u & a o q:Y->P = v”) |> store_as "isPo_expand";

val isPo_ex = store_ax("isPo_ex",“!H X f:H->X Y g:H->Y. ?P p:X->P q:Y->P. isPo(f,g,p,q)”);


val _ = new_fun "3" (cat_sort,[])

val _ = new_fun "α" (fun_sort (rastt "2") (rastt "3"),[])

val _ = new_fun "β" (fun_sort (rastt "2") (rastt "3"),[])


val _ = new_fun "γ" (fun_sort (rastt "2") (rastt "3"),[])

(*
And y: 2 -*3 with y 0 0 = a 0 O and y a 1 = ,B a 1. This completes the axiom.
 The functor F: 3 2 with F a = 0 and F o /3 = 2 proves L i /3. The domain and
 codomain relations show neither a nor ,B equals y.
*)

val CC4_1 = store_ax("CC4_1",
“γ o 0f = α o 0f & γ o 1f = β o 1f”)

val CC4_2 = store_ax("CC4_2",“isPo(1f,0f,α,β)”)

val Poa_def = 
    isPo_expand |> iffLR 
                |> strip_all_and_imp
                |> conjE2
                |> strip_all_and_imp
                |> ex2fsym0 
                "Poa" ["f","g","p","q","u","v"]
                |> disch 
                “u:X->A o f:H->X = v:Y->A o g”
                |> qgenl [‘A’,‘u’,‘v’]
                |> disch_all
                |> qgenl
                [‘H’,‘X’,‘f’,‘Y’,‘g’,‘P’,‘p’,‘q’]


val dom_ex = prove_store("dom_ex",
e0
(rpt strip_tac >> qexists_tac ‘f o 0f’ >> rw[])
(form_goal
“!A f:2->A. ?df. df = f o 0f”));

val dom_def = dom_ex |> spec_all |> ex2fsym0 "dom" ["f"]
                     |> gen_all

val cod_ex = prove_store("cod_ex",
e0
(cheat)
(form_goal
“!A f:2->A. ?df. df = f o 1f”));

val cod_def = cod_ex |> spec_all |> ex2fsym0 "cod" ["f"]
                     |> gen_all


val oa_ex = prove_store("oa_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Poa(1f,0f,α,β,f,g) o γ’ >>
 rw[])
(form_goal
 “!A f:2->A g. dom(g) = cod(f)==> 
  ?gf:2->A. gf = Poa(1f,0f,α,β,f,g) o γ”));
  
 
val oa_def = oa_ex |> spec_all |> undisch 
                   |> ex2fsym0 "@" ["g","f"]
                   |> disch_all |> gen_all


(* THEOREM 4. The composite in 2 of the nonidentity arrow 12 with either of the
 identity arrows 0 ? !2 and 0 a !2 is 1*)

val dom_cod_zot = prove_store("dom_one",
e0
(rw[zero_def,one_def,dom_def,cod_def,o_assoc,
    one_to_one_id,idR,two_def,idL])
(form_goal
 “dom(𝟘) = 0f ∧ cod(𝟘) = 0f ∧ dom(𝟙) = 1f ∧ cod(𝟙) = 1f ∧
  dom(𝟚) = 0f ∧ cod(𝟚) = 1f”));

val zf_ne_of = prove_store("zf_ne_of",
e0
(ccontra_tac >> 
 qby_tac ‘0f o To1(2) = 1f o To1(2)’
 >-- arw[] >>
 fs[GSYM zero_def,GSYM one_def,CC2_0])
(form_goal “~ (0f = 1f)”));

val dom_cod_is_two = prove_store("dom_cod_is_two",
e0
(rpt strip_tac >> 
 qsspecl_then [‘f’] strip_assume_tac CC2_1 >> 
 fs[dom_cod_zot] >-- fs[zf_ne_of] >> fs[GSYM zf_ne_of])
(form_goal
 “∀f:2->2. dom(f) = 0f & cod(f) = 1f ⇒ f = 𝟚”));

val Thm4 = prove_store("Thm4",
e0
(qby_tac
 ‘dom(𝟙) = cod(𝟚)’ >-- rw[dom_cod_zot] >>
 qby_tac
 ‘dom(𝟚) = cod(𝟘)’ >-- rw[dom_cod_zot] >>
 drule oa_def >>
 rev_drule oa_def >> arw[] >> strip_tac >-- 
 (irule dom_cod_is_two >>
 assume_tac CC4_2 >> drule Poa_def >>
 fs[GSYM dom_def,GSYM cod_def] >>
 first_x_assum (qsspecl_then [‘𝟚’,‘𝟙’] assume_tac) >>
 rfs[] >>
 rw[cod_def,dom_def,CC4_1,o_assoc] >>
 arw[GSYM o_assoc] >> 
 rw[GSYM dom_def,GSYM cod_def,dom_cod_zot]) >>
 irule dom_cod_is_two >>
 assume_tac CC4_2 >> drule Poa_def >>
 fs[GSYM dom_def,GSYM cod_def] >>
 first_x_assum (qsspecl_then [‘𝟘’,‘𝟚’] assume_tac) >>
 rfs[] >>
 rw[cod_def,dom_def,CC4_1,o_assoc] >>
 arw[GSYM o_assoc] >> 
 rw[GSYM dom_def,GSYM cod_def,dom_cod_zot]
 )
(form_goal “𝟙 @ 𝟚 = 𝟚 & 𝟚 @ 𝟘 = 𝟚”)
)



(*composable*)
val cpsb_def = define_pred “!A f:2->A g:2->A. cpsb(g,f) <=> dom(g) = cod(f)”;

val isid_def = define_pred “!A f:2->A. isid(f) <=> ?f0:1->A. f = f0 o To1(2)”

val dom_one_cod_two = prove_store("dom_one_cod_two",
e0
(rw[dom_cod_zot])
(form_goal
 “dom(𝟙) = cod(𝟚)”));


val dom_two_cod_zero = prove_store("dom_two_cod_zero",
e0
(rw[dom_cod_zot])
(form_goal
 “dom(𝟚) = cod(𝟘)”));

val Thm5_1 = prove_store("Thm5_1",
e0
(rpt strip_tac >> 
 fs[cpsb_def] >> 
 assume_tac CC4_2 >> drule Poa_def >>
 first_assum (qsspecl_then [‘𝟚’,‘𝟙’] assume_tac) >>
 fs[GSYM dom_def,GSYM cod_def,dom_cod_zot] >>
 first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
 rfs[] >> 
 qby_tac ‘f o Poa(1f, 0f, α, β, 𝟚, 𝟙) = 
          Poa(1f, 0f, α, β, f, g)’
 >-- (first_x_assum irule >> 
     arw[o_assoc,two_def,idR] >>
     fs[isid_def] >> rw[one_def,GSYM cod_def,GSYM o_assoc] >>
     qpick_x_assum ‘dom(g) = cod(f)’ (assume_tac o GSYM) >>
     arw[dom_def,o_assoc] >>
     qsuff_tac ‘f0 o (To1(2) o 0f) o To1(2) = f0 o To1(2)’ 
     >-- rw[o_assoc] >> rw[one_to_one_id,idL]) >>
 drule oa_def >> arw[] >>
 pop_assum (K all_tac) >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[o_assoc] >>
 assume_tac Thm4 >> assume_tac dom_one_cod_two >>
 drule oa_def >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[two_def,idR])
(form_goal
 “!A g:2->A. isid(g) ==> 
  (!f. cpsb(g,f) ==> g @ f = f)”));


val Thm5_2 = prove_store("Thm5_2",
e0
(rpt strip_tac >> 
 fs[cpsb_def] >> 
 assume_tac CC4_2 >> drule Poa_def >>
 first_assum (qsspecl_then [‘𝟘’,‘𝟚’] assume_tac) >>
 fs[GSYM dom_def,GSYM cod_def,dom_cod_zot] >>
 first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
 rfs[] >> 
 qby_tac ‘g o Poa(1f, 0f, α, β, 𝟘, 𝟚) = 
          Poa(1f, 0f, α, β, f, g)’
 >-- (first_x_assum irule >> 
     arw[o_assoc,two_def,idR] >>
     fs[isid_def] >> rw[zero_def,GSYM cod_def,GSYM o_assoc] >>
     arw[GSYM dom_def] >> rw[cod_def,o_assoc] >> 
     qsuff_tac ‘f0 o (To1(2) o 1f) o To1(2) = f0 o To1(2)’ 
     >-- rw[o_assoc] >> rw[one_to_one_id,idL]) >>
 drule oa_def >> arw[] >>
 pop_assum (K all_tac) >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[o_assoc] >>
 assume_tac Thm4 >> assume_tac dom_two_cod_zero>>
 drule oa_def >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[two_def,idR])
(form_goal
 “!A f:2->A. isid(f) ==> 
  (!g. cpsb(g,f) ==> g @ f = g)”));

val _ = add_parse (int_of "¹")
val _ = add_parse (int_of "²")
val _ = add_parse (int_of "³")
val _ = add_parse (int_of "ᵅ") 
val _ = add_parse (int_of "ᵝ")  
val _ = add_parse (int_of "ˠ")  


val Tp0_ex = prove_store("Tp0_ex",
e0
(rpt strip_tac >> qexists_tac ‘Ev(X,Y) o Pa(id(X),f o To1(X))’ >>
 rw[])
(form_goal
 “!X Y f:1->Exp(X,Y).?tp0:X->Y. Ev(X,Y) o Pa(id(X),f o To1(X)) = tp0”));

val Tp0_def = 
    Tp0_ex |> spec_all |> ex2fsym0 "Tp0" ["f"] |> gen_all
           |> store_as "Tp0_def"



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

val p12_of_Pa = Pa_def |> spec_all |> conjE1
                       |> gen_all
                       |> store_as "p12_of_Pa";


val Swap_property = proved_th $
e0
(rw[GSYM Swap_def,p12_of_Pa])
(form_goal
 “!A B. p1(B,A) o Swap(A,B) = p2(A,B) & p2(B,A) o Swap(A,B) = p1(A,B)”)


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


val Pa_distr = proved_th $
e0
(rpt strip_tac >> irule is_Pa >>
 rw[GSYM o_assoc,p12_of_Pa])
(form_goal
“!A B X a1:X ->A a2:X->B X0 x:X0->X. Pa(a1,a2) o x = 
Pa(a1 o x,a2 o x) ”)

val Swap_Swap_id = prove_store("Swap_Swap_id",
e0
(rpt strip_tac >> irule to_P_eq >> rw[GSYM Swap_def,idR] >>
 rw[Pa_distr,p12_of_Pa])
(form_goal
 “!A B. Swap(B,A) o Swap(A,B) = id(A * B)”));




(*

val Thm6_square= prove_store("Thm6_sqaure",
e0
()
(form_goal
 “!fgij:2 * 2 -> A ghkl:2 * 2 -> A f g i j h k l.
   fgij o Pa(0f o To1(2),id(2)) = f &
   fgij o Pa(1f o To1(2),id(2)) = g &
   fgij o Pa(id(2),0f o To1(2)) = i &
   fgij o Pa(id(2),1f o To1(2)) = j &
   ghkl o Pa(0f o To1(2),id(2)) = g &
   ghkl o Pa(1f o To1(2),id(2)) = h &
   ghkl o Pa(id(2),0f o To1(2)) = k &
   ghkl o Pa(id(2),1f o To1(2)) = l ==>
   
   
  fgij o Pa(1f o To1(2),id(2)) = f 
  ghkl o Pa(0f o To1(2),id(2)) & 
  !cmp:2 * 2 ->A. 
  cmp o Pa(0f o To1(2),id(2)) = 

  cpsb(ghkl,fgij) ==> 
  Tp0(ghkl @ fgij) o Pa(id(2),0f o To1(2)) = 
  (Tp0(ghkl) o Pa(id(2),0f o To1(2))) @ ”));


val Thm6 = prove_store("Thm6",
e0
()
(form_goal
 “!fgij:2-> Exp(2,A) ghkl:2-> Exp(2,A). 
  cpsb(ghkl,fgij) ==> 
  Tp0(ghkl @ fgij) o Pa(id(2),0f o To1(2)) = 
  (Tp0(ghkl) o Pa(id(2),0f o To1(2))) @ ”));

*)

val two_ex = prove_store("two_ex",
e0
cheat
(form_goal
 “∃t:2->2. t = id(2)”));

val two_def = two_ex |> ex2fsym0 "𝟚" [];

val _ = add_parse (int_of "𝟚");
(*commutative square*)

val csL_ex = prove_store("csL_ex",
e0
(cheat)
(form_goal
 “!A cs:2 * 2 ->A. 
  ∃l. l = cs o Pa(𝟘,𝟚)”));

val csL_def = csL_ex |> spec_all |> ex2fsym0 "csL" ["cs"]
                     |> gen_all

val csR_ex = prove_store("csR_ex",
e0
(cheat)
(form_goal
 “!A cs:2 * 2 ->A. 
  ∃r. r = cs o Pa(𝟙,𝟚)”));


val csR_def = csR_ex |> spec_all |> ex2fsym0 "csR" ["cs"]
                     |> gen_all


val csT_ex = prove_store("csT_ex",
e0
(cheat)
(form_goal
 “!A cs:2 * 2 ->A. 
  ∃t.t  = cs o Pa(𝟚,𝟘)”));

val csT_def = csT_ex |> spec_all |> ex2fsym0 "csT" ["cs"]
                     |> gen_all

val csB_ex = prove_store("csB_ex",
e0
(cheat)
(form_goal
 “!A cs:2 * 2 ->A. 
  ∃b. b = cs o Pa(𝟚,𝟙)”));

val csB_def = csB_ex |> spec_all |> ex2fsym0 "csB" ["cs"]
                     |> gen_all

val Pt_ex = prove_store("Pt_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Ev(A,B) o Pa(p1(A,X), h o p2(A,X))’ >>
 rw[])
(form_goal “∀A B X h:X-> Exp(A,B). ∃pt. pt = Ev(A,B) o Pa(p1(A,X), h o p2(A,X))”));

val Pt_def = Pt_ex |> spec_all |> ex2fsym0 "Pt" ["h"]
                   |> gen_all |> store_as "Pt_def";

(*exponential, on dom *)
val Ed_ex = prove_store("Ed_ex",
e0
(rpt strip_tac >>
 qexists_tac‘Tp(Ev(B,X) o Pa(f o p1(A,Exp(B,X)),p2(A,Exp(B,X))))’ >> rw[])
(form_goal
 “∀A B f:A->B X. ∃ed. ed = Tp(Ev(B,X) o Pa(f o p1(A,Exp(B,X)),p2(A,Exp(B,X))))”));

val Ed_def = Ed_ex |> spec_all |> ex2fsym0 "Ed" ["f","X"]
                   |> gen_all

(*erase the label A^1 , an iso A^1 -> A*)
val Er1_ex = prove_store("Er1_ex",
e0
(strip_tac >> qexists_tac ‘Ev(1,A) o Pa(To1(Exp(1,A)),id(Exp(1,A)))’ >> rw[])
(form_goal
 “∀A. ∃er1. er1 = Ev(1,A) o Pa(To1(Exp(1,A)),id(Exp(1,A)))”));

val Er1_def = Er1_ex |> spec_all |> ex2fsym0 "Er1" ["A"]
                     |> gen_all

val A1f_ex = prove_store("A1f_ex",
e0
(strip_tac >> qexists_tac ‘Er1(A)  o Ed(1f,A)’ >> rw[])
(form_goal
 “∀A. ∃a1f. a1f = Er1(A) o Ed(1f,A)”));

fun define_const f fsymname inputs = 
let val (l,r) = dest_eq f
    val (n,s) = dest_var l
    val g = form_goal (mk_exists n s f)
    val eth =
        prove_store(fsymname ^ "_ex",e0
                    (exists_tac r >> accept_tac (refl r))
                    g)
    val th = ex2fsym0 fsymname inputs eth |> gen_all
                      |> store_as (fsymname ^ "_def")
in (eth,th)
end

(*define_const “a1f = Er1(A) o Ed(1f,A)” "A1f" ["A"]*)

(*
val (Ed1_ex,Ed1_def) = define_const “a1f = Er1(A) o Ed(f:X->Y,A)” "Ed1" ["f","A"];

*)


val fun_pres_oa = prove_store("fun_pres_oa",
e0
(cheat)
(form_goal
 “∀A f:2->A g. cpsb(g,f) ⇒
  ∀B k:A->B. k o (g @ f) = (k o g) @ (k o f)”));

val To1_o_To1 = prove_store("To1_o_To1",
e0
(cheat)
(form_goal
 “∀A f:X->A. To1(A) o f = To1(X)”));



val Ev_of_Tp = prove_store("Ev_of_Tp",
e0
(rpt strip_tac >> rw[Tp_def])
(form_goal
 “!A B X f:A * X ->B. 
  Ev(A,B) o Pa(p1(A,X),Tp(f) o p2(A,X)) = f”));


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



val Ev_of_Tp_el' = prove_store("Ev_of_Tp_el'",
e0
(rpt strip_tac >> 
 qby_tac ‘Tp(f) = Tp(f) o id(P)’ >-- rw[idR] >>
 once_arw[] >> rw[Ev_of_Tp_el])
(form_goal
“!A B P f:A * P -> B  a:P -> A.
Ev(A, B) o Pa(a, Tp(f)) = f o Pa(a, id(P))”));


val A1f_of_cs = prove_store("A1f_of_cs",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,dom_def,Pa_distr,
    o_assoc,To1_o_To1,idL,Ev_of_Tp_el,Ev_of_Tp_el',
    p12_of_Pa,one_to_one_id,idR])
(form_goal
 “∀A f:1-> Exp(2,A).
  (Er1(A) o Ed(0f,A)) o f = dom(Pt(f) o Pa(id(2),To1(2)))”));

val csT_Pt = prove_store("csT_Pt",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,csT_def] >>
 rw[Pa_distr,o_assoc,To1_o_To1,idL] >>
 rw[Ev_of_Tp_el,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el',Pa_distr,o_assoc,GSYM Swap_def,p12_of_Pa,
    two_def,zero_def] )
(form_goal 
 “∀A f:2-> Exp(2,A). csT(Pt(f)) = 
  (Er1(A) o Ed(0f,A)) o Tp(Pt(f)o Swap(2,2))”));



(*
A0f: A^2 -> A

2 -> A^2 -> A


*)


val csL_Pt = prove_store("csL_Pt",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,csL_def] >>
 rw[Pa_distr,o_assoc,To1_o_To1,idL] >>
 rw[Ev_of_Tp_el,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el',Pa_distr,o_assoc,GSYM Swap_def,p12_of_Pa,
    two_def,zero_def,idR] )
(form_goal 
 “∀A f:2-> Exp(2,A). csL(Pt(f)) = 
 (Er1(A) o Ed(0f,A)) o f”));


val csR_Pt = prove_store("csR_Pt",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,csR_def] >>
 rw[Pa_distr,o_assoc,To1_o_To1,idL] >>
 rw[Ev_of_Tp_el,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el',Pa_distr,o_assoc,GSYM Swap_def,p12_of_Pa,
    two_def,one_def,idR] )
(form_goal 
 “∀A f:2-> Exp(2,A). csR(Pt(f)) = 
 (Er1(A) o Ed(1f,A)) o f”));



val Thm6_vertical = prove_store("Thm6_vertical",
e0
(rpt strip_tac >> rw[csL_Pt,csR_Pt] >> drule fun_pres_oa >> 
 arw[])
(form_goal
 “∀A s1:2-> Exp(2,A) s2:2-> Exp(2,A). cpsb(s2,s1) ⇒ 
  csL(Pt(s2 @ s1)) = csL(Pt(s2)) @ csL(Pt(s1))  ∧
  csR(Pt(s2 @ s1)) = csR(Pt(s2)) @ csR(Pt(s1))”));

val oa_dom_cod = prove_store("oa_dom_cod",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 fs[cpsb_def] >> drule oa_def >> 
 arw[] >> rw[dom_def,cod_def,o_assoc,CC4_1] >>
 assume_tac CC4_2 >> drule Poa_def >>
 fs[dom_def,cod_def] >>
 last_x_assum (assume_tac o GSYM) >>
 first_x_assum drule >> arw[GSYM o_assoc])
(form_goal
 “∀A f:2->A g. cpsb(g,f) ⇒ dom(g @ f) = dom(f) ∧ cod(g @ f) = cod(g)”));


val Thm6_vertical_full = prove_store("Thm6_vertical_full",
e0
(rpt strip_tac >> rw[csL_Pt,csR_Pt] >> drule fun_pres_oa >> 
 arw[] >>
 rw[csT_dom,csB_cod] >> drule oa_dom_cod >> arw[])
(form_goal
 “∀A s1:2-> Exp(2,A) s2:2-> Exp(2,A). cpsb(s2,s1) ⇒ 
  csL(Pt(s2 @ s1)) = csL(Pt(s2)) @ csL(Pt(s1)) ∧
  csR(Pt(s2 @ s1)) = csR(Pt(s2)) @ csR(Pt(s1)) ∧
  csT(Pt(s2 @ s1)) = csT(Pt(s1)) ∧
  csB(Pt(s2 @ s1)) = csB(Pt(s2))”));


val csL_csT = prove_store("csL_csT",
e0
(rw[csL_def,csT_def,o_assoc,GSYM Swap_def,p12_of_Pa,
    Pa_distr])
(form_goal
 “∀A f: 2 * 2 -> A. csT(f o Swap(2,2)) = csL(f)”));



val csR_csB = prove_store("csR_csB",
e0
(rw[csR_def,csB_def,o_assoc,GSYM Swap_def,p12_of_Pa,
    Pa_distr])
(form_goal
 “∀A f: 2 * 2 -> A. csB(f o Swap(2,2)) = csR(f)”));


val csR_csB' = prove_store("csR_csB'",
e0
(rw[csR_def,csB_def,o_assoc,GSYM Swap_def,p12_of_Pa,
    Pa_distr])
(form_goal
 “∀A f: 2 * 2 -> A. csR(f o Swap(2,2)) = csB(f)”));

val csT_dom = prove_store("csT_dom",
e0
(rw[csT_def,dom_def,Pt_def,o_assoc,Pa_distr,p12_of_Pa,
    two_def,zero_def])
(form_goal
 “∀A s:2->Exp(2,A). csT(Pt(s)) = Pt(dom(s)) o Pa(id(2),To1(2))”));


val csB_cod = prove_store("csB_cod",
e0
(rw[csB_def,cod_def,Pt_def,o_assoc,Pa_distr,p12_of_Pa,
    two_def,one_def])
(form_goal
 “∀A s:2->Exp(2,A). csB(Pt(s)) = Pt(cod(s)) o Pa(id(2),To1(2))”));

val pT_ex = prove_store("pT_ex",
e0
(rpt strip_tac >> qexists_tac ‘(Pt(h) o Swap(X,A))’ >>
 rw[])
(form_goal “∀A B X h:X->Exp(A,B). 
 ∃pt. pt = Pt(h) o Swap(X,A)”));

val pT_def = pT_ex |> spec_all |> ex2fsym0 "pT" ["h"]
                   |> gen_all


(* multiply by 1 is iso

A -- Pa(id(A),To1(A)) --> A * 1 -- p1(A,1) --> A
*)

val Cr1_iso = prove_store("Cr1_iso",
e0
(strip_tac >> rw[p12_of_Pa,Pa_distr,one_to_one_id] >>
 flip_tac >> irule is_Pa >> rw[idL,idR,To1_def])
(form_goal “∀A. p1(A,1) o Pa(id(A),To1(A)) = id(A) & 
                Pa(id(A),To1(A)) o p1(A,1) = id(A * 1)”));
              

val o_Cr1_eq = prove_store("o_Cr1_eq",
e0
(cheat)
(form_goal
 “∀A B.
  (∀f:A->B g. f o p1(A,1) = g o p1(A,1) ⇔ f = g) ∧ 
  (∀f:A * 1->B g. f o Pa(id(A),To1(A)) = g o Pa(id(A),To1(A)) ⇔ 
  f = g)”));
 
(*
generate lemma which says composing with them eq iff eq
*)

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


val Pt_eq_eq = prove_store("Pt_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 irule Ev_eq_eq >> arw[GSYM Pt_def])
(form_goal
 “∀A B X f:X-> Exp(A,B) g. Pt(f) = Pt(g) ⇔f = g”));


val Pt_Tp = prove_store("Pt_Tp",
e0
(rw[Pt_def,Ev_of_Tp])
(form_goal
 “∀A B X f:A * X -> B. Pt(Tp(f)) = f”));



val Tp_Pt = prove_store("Tp_Pt",
e0
(rpt strip_tac >> rw[Pt_def] >> flip_tac >> irule is_Tp >>
 rw[])
(form_goal
 “∀A B X f:X -> Exp(A,B). Tp(Pt(f)) = f”));


val Thm6_0 = prove_store("Thm6_0",
e0
(strip_tac >> 
strip_tac >> strip_tac >> strip_tac >> 
 irule Thm6_vertical >>
 rw[cpsb_def] >> fs[GSYM csL_csT,GSYM csR_csB]  >>
 fs[GSYM pT_def] >> flip_tac >>
 qby_tac ‘Pt(Tp(pT(s1))) = pT(s1)’ >-- rw[Pt_Tp] >>
 qby_tac
 ‘csB(Pt(Tp(pT(s1)))) = csT(Pt(Tp(pT(s2))))’
 >-- arw[Pt_Tp] >>
 pop_assum mp_tac >> pop_assum_list (K all_tac) >>
 strip_tac >> fs[csB_cod,csT_dom] >>
 fs[o_Cr1_eq,Pt_eq_eq])
(form_goal
 “∀A s1:2 -> Exp(2,A) s2. 
  csR(Pt(s1)) = csL(Pt(s2)) ⇒ 
  csL(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csL(Pt(Tp(pT(s2)))) @ csL(Pt(Tp(pT(s1)))) &
  csR(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csR(Pt(Tp(pT(s2)))) @ csR(Pt(Tp(pT(s1))))”));

val Thm6 = Thm6_0 |> rewr_rule[Pt_Tp] |> store_as "Thm6";



val Thm6_0_full = prove_store("Thm6_0",
e0
(strip_tac >> 
strip_tac >> strip_tac >> strip_tac >> 
 irule Thm6_vertical_full >>
 rw[cpsb_def] >> fs[GSYM csL_csT,GSYM csR_csB]  >>
 fs[GSYM pT_def] >> flip_tac >>
 qby_tac ‘Pt(Tp(pT(s1))) = pT(s1)’ >-- rw[Pt_Tp] >>
 qby_tac
 ‘csB(Pt(Tp(pT(s1)))) = csT(Pt(Tp(pT(s2))))’
 >-- arw[Pt_Tp] >>
 pop_assum mp_tac >> pop_assum_list (K all_tac) >>
 strip_tac >> fs[csB_cod,csT_dom] >>
 fs[o_Cr1_eq,Pt_eq_eq])
(form_goal
 “∀A s1:2 -> Exp(2,A) s2. 
  csR(Pt(s1)) = csL(Pt(s2)) ⇒ 
  csL(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csL(Pt(Tp(pT(s2)))) @ csL(Pt(Tp(pT(s1)))) &
  csR(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csR(Pt(Tp(pT(s2)))) @ csR(Pt(Tp(pT(s1))))  & 
  csT(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csT(Pt(Tp(pT(s1)))) & 
  csB(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csB(Pt(Tp(pT(s2))))”));


val Thm6_full = Thm6_0_full |> rewr_rule[Pt_Tp] 
                            |> store_as "Thm6_full";

val Pt_def_alt = prove_store("Pt_def_alt",
e0
(rw[pT_def,Swap_Swap_id,idR,o_assoc])
(form_goal “∀A B X f:X -> Exp(A,B). 
 Pt(f) = pT(f) o Swap(A,X)”));

val csL_csT_Pt = prove_store("csL_csT_Pt",
e0
(rw[Pt_def_alt,csL_csT])
(form_goal
 “∀A s:2->Exp(2,A).csL(pT(s)) = csT(Pt(s))”));

val csT_csL_pT = prove_store("csT_csL_pT",
e0
(rw[GSYM csL_csT,pT_def])
(form_goal
 “∀A s:2->Exp(2,A).csT(pT(s)) = csL(Pt(s))”));

val csR_csB_Pt = prove_store("csR_csB_Pt",
e0
(rw[Pt_def_alt,csR_csB])
(form_goal
 “∀A s:2->Exp(2,A).csR(pT(s)) = csB(Pt(s))”));

val csB_csR_pT = prove_store("csB_csR_pT",
e0
(rw[GSYM csR_csB,pT_def])
(form_goal
 “∀A s:2->Exp(2,A).csB(pT(s)) = csR(Pt(s))”));

val Thm6_ex_0 = prove_store("Thm6_ex_0",
e0
(rpt strip_tac >> drule Thm6_full >>
 qexists_tac ‘Pt(Tp(pT(s2)) @ Tp(pT(s1)))’ >>
 arw[csL_csT_Pt,csR_csB_Pt,csT_csL_pT,csB_csR_pT])
(form_goal
 “∀A s1:2->Exp(2,A) s2. 
  csR(Pt(s1)) = csL(Pt(s2)) ⇒ 
  ∃s. csL(s) = csT(Pt(s2)) @ csT(Pt(s1)) & 
      csR(s) = csB(Pt(s2)) @ csB(Pt(s1)) &
      csT(s) = csL(Pt(s1)) & 
      csB(s) = csR(Pt(s2))”));

val cs_Swap = prove_store("cs_Swap",
e0
(rw[csT_def,csB_def,csL_def,csR_def,o_assoc,
    GSYM Swap_def,p12_of_Pa,Pa_distr])
(form_goal
 “∀A s: 2 * 2 ->A.
  csT(s o Swap(2, 2)) = csL(s) ∧
  csB(s o Swap(2, 2)) = csR(s) ∧
  csL(s o Swap(2, 2)) = csT(s) ∧
  csR(s o Swap(2, 2)) = csB(s)”));

val Thm6_ex = prove_store("Thm6_ex",
e0
(rpt strip_tac >> drule Thm6_ex_0 >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘s o Swap(2,2)’ >>
 arw[cs_Swap])
(form_goal
 “∀A s1:2->Exp(2,A) s2. 
  csR(Pt(s1)) = csL(Pt(s2)) ⇒ 
  ∃s. csT(s) = csT(Pt(s2)) @ csT(Pt(s1)) & 
      csB(s) = csB(Pt(s2)) @ csB(Pt(s1)) &
      csL(s) = csL(Pt(s1)) & 
      csR(s) = csR(Pt(s2))”));


val Thm6_vertical_ex = prove_store("Thm6_vertical_ex",
e0
(rpt strip_tac >>
 qby_tac ‘cpsb(s2,s1)’ 
 >-- (rw[cpsb_def] >> fs[csB_cod,csT_dom,o_Cr1_eq,Pt_eq_eq])>>
 drule Thm6_vertical_full >>
 qexists_tac ‘Pt(s2 @ s1)’ >> arw[])
(form_goal
 “∀A s1:2->Exp(2,A) s2. 
  csB(Pt(s1)) = csT(Pt(s2)) ⇒ 
  ∃s. csL(s) = csL(Pt(s2)) @ csL(Pt(s1)) & 
      csR(s) = csR(Pt(s2)) @ csR(Pt(s1)) &
      csT(s) = csT(Pt(s1)) & 
      csB(s) = csB(Pt(s2))”));


val cs_vertical_ex = prove_store("cs_vertical_ex",
e0
(rpt strip_tac >>
 qsspecl_then [‘Tp(s1)’,‘Tp(s2)’] assume_tac
 Thm6_vertical_ex >>
 rfs[Pt_Tp] >> qexists_tac ‘s’ >> arw[])
(form_goal
 “∀A s1: 2 * 2 -> A s2: 2 * 2 -> A.
   csB(s1) = csT(s2) ⇒
  ∃s. csL(s) = csL(s2) @ csL(s1) ∧
      csR(s) = csR(s2) @ csR(s1) ∧
      csT(s) = csT(s1) ∧
      csB(s) = csB(s2)
  ”));



val cs_horizontal_ex = prove_store("cs_horizontal_ex",
e0
(rpt strip_tac >>
 qsspecl_then [‘Tp(s1)’,‘Tp(s2)’] assume_tac
 Thm6_ex >>
 rfs[Pt_Tp] >> qexists_tac ‘s’ >> arw[])
(form_goal
 “∀A s1: 2 * 2 -> A s2: 2 * 2 -> A.
   csR(s1) = csL(s2) ⇒
  ∃s. csT(s) = csT(s2) @ csT(s1) ∧
      csB(s) = csB(s2) @ csB(s1) ∧
      csL(s) = csL(s1) ∧
      csR(s) = csR(s2)
  ”));



val Thm7 = prove_store("Thm7",
e0
cheat
(form_goal
 “!A f:2->A g f' g'. 
   cpsb(g,f) & cpsb(g',f') & 
   g @ f = g' @ f' ==>
   ?q: 2* 2->A.
   csT(q) = f & 
   csR(q) = g &
   csL(q) = f' &
   csB(q) = g'  
   ”));


val iso_def = define_pred
“!A f:2->A. iso(f) <=> 
 ?g:2->A. dom(g) = cod(f) & dom(f) = cod(g) &
 g @ f = dom(f) o To1(2) & f @ g = cod(f) o To1(2) ”


val CC6 = store_ax("CC6",
“?A f:2->A. iso(f) & ~isid(f)”); 

val Thm14 = prove_store("Thm14",
e0
cheat
(form_goal
“?A A1:1->A A2. ~(A1 = A2) &
?f:2->A. dom(f) = A1 & cod(f) = A2 ”));

val Thm15 = prove_store("Thm15",
e0
cheat
(form_goal
 “!A B f:A->B. Epi(f) ==> !B0:1->B. ?A0:1->A. B0 = f o A0”))
 
val Thm16 = prove_store("Thm16",
e0
cheat
(form_goal
 “!A B f:2->A + B. (?f0:2->A. f = i1(A,B) o f0) |
(?f0:2->B. f = i2(A,B) o f0)”));


(*
A full subcategory of A is a monic i: S >-4 A such that if f a 0 and f a I are both
 in S then so is f. A full subcategory classifier is a category Cl with a selected object
 t: 1 -+ Cl such that any full subcategory i: S >-4 A is the pullback of t along a unique
 functor c: A - Cl.
*)


val FSC_def = define_pred
“!S A i:S->A. FSC(i) <=> Mono(i) & 
 !f:2->A d:1->S c:1->S. dom(f) = i o d & cod(f) = i o c ==> 
 ?f0:2->S. f = i o f0”;

val FSCC_def = define_pred
“!Cl t:1->Cl. FSCC(t) <=> 
 (!S A i:S->A. FSC(i) ==> ?!c:A->Cl. isPb(c,t,i,To1(S)))”

 
val Thm17 = prove_store("Thm17",
e0
cheat
(form_goal “?Cl t:1->Cl. FSCC(t)”));

val DC_def = define_pred “!A. DC(A) <=> !f:2->A. isid(f)”



val iscoEq_def = define_pred
“!A B f:A->B g cE ce:B -> cE. 
      iscoEq(f,g,ce) <=> 
      ce o f = ce o g & 
      !X x:B->X. x o f = x o g ==>
      ?!x0:cE->X. x = x0 o ce”



val iscoEq_ex = store_ax("iscoEq_ex",“!A B f:A->B g:A->B.?cE ce:B->cE.iscoEq(f,g,ce)”);

val coEqa_def = 
    iscoEq_def |> iffLR 
               |> spec_all |> undisch |> conjE2 
               |> spec_all |> undisch |> uex_expand
               |> conj_all_assum |> disch_all
               |> ex2fsym "coEqa" ["f","g","ce","x"]
               |> store_as "coEqa_def"

 
val Thm20 = prove_store("Thm20",
e0
cheat
(form_goal
 “!D. DC(D) ==> !A f:A->D g Q q:D->Q. iscoEq(f,g,q) ==>
 DC(Q)”));
 
val Thm21 = prove_store("Thm21",
e0
cheat
(form_goal
 “!A. DC(A) ==> !S i:S->A. FSC(i) ==>
  ?!c:A-> 1+1. isPb(c,i2(1,1),i,To1(S))
  ”));

val SO_def = define_pred
“!A S s:S->A. SO(s) <=> 
 (DC(S) & Mono(s) & 
  !X f:X->A. DC(X) ==> ?f0:X->S. f = s o f0)”

val SA_def = define_pred
“!A S s:S -> Exp(2,A). SA(s) <=> SO(s)”

(*
 THEOREM 22. If A has a set of objects, so does the coequalizer of any parallel pair with codomain A.

*)

val Thm22 = prove_store("Thm22",
e0
cheat
(form_goal
 “!A S s:S->A. SO(s) ==> 
  !X f:X->A g Q q:A->Q. iscoEq(f,g,q) ==>
  ?Sq sq:Sq -> Q. SO(q)”));


(*
val Thm23 = prove_store("Thm23",
e0
()
(form_goal
 “”));
*)

val ICat_def = define_pred
“∀C0 C1 s: C1-> C0 t:C1 -> C0 e: C0 -> C1 CC c: CC -> C1. 
 ICat(s,t,e,c) ⇔ 
 s o e = id(C0) ∧ t o e = id(C0)”

(*
THEOREM 24. If G: A2 -+ B2 and F: A -+ B are an internal functor between the
 internal categories on A and B, then G = F
*)
val IFun_def = define_pred
“∀F0:C0 -> D0 F1:C1->D1. IFun(F0,F1) ⇔
 ”

!A B. A = B <=> 
 (!X f:X->A. P(f)) <=> (!X f:X->B. P(f)) & 
 (!X f:A->X. P(f)) <=> (!X f:B->X. P(f))


val _ = 
“?C. ”
val Z2_O2_ex




IsTopos(C) ==> hasProd(C)


?C.
(asob(A:Ob(C))):ob 

asOb() 

?ETCS. 
!A B f:A->B. ?



!C \equiv to the WS of ETCS
  P()




IsTopos(ETCS) ==> hasProd(ETCS)

!A:OB(ETCS) B.? AB: OB(ETCS)....



!A:ob B:ob. 





cat sort
fun sort

C:cat

f: C:cat ->D

1 

2

a --> b

C


f(a) --> f(b)


!f:2->C g:2->C. f o 1 = g o 0 ==>
 ?! fog: 2->C. fog o 0 = f o 0 &
               fog o 1 = g o 1


!f:2->C g:2->C h:2->C.

f o 1 = g o 0 & ... ==> 
(h o_C g) o_C f = h o_C g o_C f =



Ob(C) Ar: Ob(C) -> Ob(C)


perfectoid space

fragile

IsTopos(C) ==> hasProd(C)












