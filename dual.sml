(*
val _ = new_fun "op" (cat_sort,[("A",cat_sort)])

val _ = new_fun "opf" (fun_sort (rastt "op(A)") (rastt "op(B)"),
                      [("f",fun_sort (rastt "A") (rastt "B"))])


val CC7 = store_ax("CC7",
“(∀A. opf(Id(A)) = Id(op(A))) ∧ 
 (∀A B f:A ->B C g:B->C. opf(g o f) = opf(g) o opf(f))”


val _ = new_fun "%" (fun_sort (mk_cat "A") (mk_cat "B"),
                      [("f",fun_sort (rastt "op(op(A))")
                                     (rastt "op(op(B))"))])



val _ = add_parse (int_of "%");


opf (f: A -> B)

f:A^op -> B^op

f'':A^op^op -> B^ op^op

A^op^op -> B


f^op^op = f


Makkai



val opf_opf_eq = store_ax
("opf_opf_eq",“!A B. (∀f:A->B. %(opf(opf(f))) = f) ∧
                     (∀f:op(A) -> op(B). opf(%(opf(f))) = f)”)

val op_bij0 = prove_store("op_bij0",
e0
(rpt strip_tac
    >-- (uex_tac >> qexists_tac ‘(opf(f))’ >>
        arw[] >> rpt strip_tac >> 
        qby_tac ‘opf(f) = opf(%(opf(f0')))’
        >-- arw[] >> rfs[]) 
    >-- (uex_tac >> qexists_tac ‘%(opf(f))’ >>
        arw[] >> rpt strip_tac >> 
        qby_tac ‘%(opf(f)) = %(opf(opf(f0')))’
        >-- arw[] >> rfs[]))
(form_goal “(!A B. (∀f:A->B. %(opf(opf(f))) = f) ∧
(∀f:op(A) -> op(B). opf(%(opf(f))) = f)) ==>
(∀A B.
 (∀f:A->B. ∃!f0:op(A) ->op(B). f = %(opf(f0))) ∧ 
 (∀f:op(A) -> op(B). ∃!f0:A->B. f = opf(f0)))”));

val op_bij = mp op_bij0 opf_opf_eq |> store_as "op_bij";


“(∀f:A->op(B). ∃!f0:op(A) -> B. f = d%(opf(f0))) ∧
 (∀f:op(A) ->B. ∃!f0:A -> op(B). f = %c(opf(f0)))”





have op(op(2)) = 2/

know that 2 is a 

2 ---> A ==f,g===> B

∀f g. f ≠ g, want op(2) -->A. f o a ≠ g o a 
have 2 -> op(2), want 2->2, 




val op_0f_1f = store_ax
("op_0f_1f",“1%(%2(opf(0f))) = 1f”)





val _ = new_fun "d%" (fun_sort (mk_cat "A") (mk_cat "B"),
                      [("f",fun_sort (rastt "op(op(A))")
                                     (rastt "B"))])


val _ = new_fun "%d" (fun_sort (rastt "op(op(A))") (mk_cat "B"),
                      [("f",fun_sort (rastt "A")
                                     (rastt "B"))])

val _ = new_fun "%c" (fun_sort (mk_cat "A") (mk_cat "B"),
                      [("f",fun_sort (rastt "A")
                                     (rastt "op(op(B))"))])


val _ = new_fun "c%" (fun_sort (mk_cat "A") (rastt "op(op(B))"),
                      [("f",fun_sort (rastt "A")
                                     (rastt "B"))])

val _ = new_fun "1%" (fun_sort (rastt "1") (mk_cat "A"),
                      [("f",fun_sort (rastt "op(1)")
                                     (rastt "A"))])

val _ = new_fun "0%" (fun_sort (rastt "0") (mk_cat "A"),
                      [("f",fun_sort (rastt "op(0)")
                                     (rastt "A"))])

val _ = new_fun "2%" (fun_sort (rastt "2") (mk_cat "A"),
                      [("f",fun_sort (rastt "op(2)")
                                     (rastt "A"))])


val _ = new_fun "%2" (fun_sort (mk_cat "A") (rastt "2"),
                      [("f",fun_sort (rastt "A")
                                     (rastt "op(2)"))])

val opf_opf_eq = store_ax
("opf_opf_eq",“!A B. (∀f:A->B. %(opf(opf(f))) = f) ∧
(∀f:op(A) -> op(B). opf(%(opf(f))) = f)”)

rpt strip_tac >> dimp_tac >> strip_tac
>-- (rpt strip_tac
    >-- (uex_tac >> qexists_tac ‘(opf(f))’ >>
        arw[] >> rpt strip_tac >> 
        qby_tac ‘opf(f) = opf(%(opf(f0')))’
        >-- arw[] >> rfs[]) 
    >-- (uex_tac >> qexists_tac ‘%(opf(f))’ >>
        arw[] >> rpt strip_tac >> 
        qby_tac ‘%(opf(f)) = %(opf(opf(f0')))’
        >-- arw[] >> rfs[])) >> 
rpt strip_tac 
>-- first_x_assum 
    (qspecl_then [‘A’,‘B’] strip_assume_tac) >>
    first_x_assum (qspecl_then [‘’])


“(!A B. (∀f:A->B. %(opf(opf(f))) = f) ∧
(∀f:op(A) -> op(B). opf(%(opf(f))) = f)) ⇔ 
(∀A B.
 (∀f:A->B. ∃!f0:op(A) ->op(B). f = %(opf(f0))) ∧ 
 (∀f:op(A) -> op(B). ∃!f0:A->B. f = opf(f0)))”


∀f:op(A) -> op(B). %(opf(f)) = opf

val op_0f_1f = store_ax
("op_0f_1f",“1%(%2(opf(0f))) = 1f”)

val op_1f_0f = prove_store("op_1f_0f",
e0
()
(form_goal “1%(%2(opf(1f))) = 0f”));




val co_co_eq = store_ax
“∀A B f:A->B. d%(%d(f)) = f ∧ %c(c%(f)) = f”

strip_tac >> uex_tac >> qexists_tac ‘%(opf(f))’ >>

“∀f:op(A)->op(B). ∃!f0:A->B. f = opf(f0)”


val op_obj_bij = prove_store("op_obj_bij",
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘1%(opf(a))’ >> rw[])
(form_goal “∀A a:1->A. ∃!a0:1->op(A). a0 = 1%(opf(a))”));




val op_ob_bij' = prove_store("op_ob_bij'",
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘1%(%c(opf(a)))’ >>
 )
(form_goal “∀A a:1-> op(A). ∃!a0:1->A. a = 1%(opf(a0))”));


val op_ar_bij = prove_store("op_ar_bij",
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘2%(opf(a))’ >> rw[])
(form_goal “∀A a:2->A. ∃!a0:2->op(A). a0 = 2%(opf(a))”));
*)

val _ = new_pred "isop" [("A",cat_sort),("A'",cat_sort)]

val _ = new_pred "isopf" 
            [("f",fun_sort (mk_cat "A") (mk_cat "B")),
             ("f'",fun_sort (mk_cat "A'") (mk_cat "B'"))]

(*isop just says there exists a correspondence of 
object and arrows between these categories. Note that does not *)

(*A^op ^op = A, can use iff *)
val op_op_refl = store_ax("op_op_refl",
“∀A Aop. isop(A,Aop) ⇒ isop(Aop,A)”);

val opf_uex = store_ax("opf_uex",
“∀A B f:A->B Aop Bop. isop(A,Aop) ∧ isop(B,Bop) ⇒ 
  ∃!f':Aop -> Bop. isopf(f,f')”);

val opf_opf_refl = store_ax("opf_opf_refl",
“∀A B f:A->B Aop Bop f':Aop -> Bop. isopf(f,f') ⇒ isopf(f',f)”);

val op_2 = store_ax("op_2",“isop(2,2)”);

val op_1 = store_ax("op_1",“isop(1,1)”);

val op_3 = store_ax("op_3",“isop(3,3)”);

val opf_0f = store_ax("opf_0f",“isopf(0f,1f)”);

(*should prove that op cats are equivalent*)

val opf_def = opf_uex |> spec_all |> undisch 
                      |> uex_expand
                      |> ex2fsym0 "opf" ["f","Aop","Bop"]
                      |> gen_all
                      |> disch_all
                      |> gen_all
                      |> store_as "opf_def";


(*

A^op^op = A ∧ F^op^op

f: A-> B g:A->B

opf(f,A',B') = opf(g,A',B')

axiom


isopf(f:A->B,f':A'->B') ⇒ isop(A,A') ∧ isop(B,B')


 isop(A,A') ∧ isop(B,B') ⇒ ∃!

*)

val opf_property = opf_def |> strip_all_and_imp 
                     |> conjE1
                     |> gen_all 
                     |> disch_all |> gen_all
                     |> store_as "opf_property";


val is_opf = opf_def |> strip_all_and_imp 
                     |> conjE2 
                     |> gen_all 
                     |> disch_all |> gen_all
                     |> store_as "is_opf";

val ob_of_2 = prove_store("ob_of_2",
e0
(cheat)
(form_goal “∀f:1->2. f = 1f | f = 0f”));

val opf_1f = prove_store("opf_1f",
e0
(assume_tac opf_0f >> drule opf_opf_refl >> arw[])
(form_goal “isopf(1f,0f)”));

val op_ob_uex = prove_store("op_ob_uex",
e0
(rpt strip_tac >> irule opf_uex >> arw[op_1])
(form_goal “∀A A'. isop(A,A') ⇒ ∀a:1->A. ∃!a':1->A'. isopf(a,a')”));


val opf_o_opf = store_ax("opf_o_opf",
“∀A B f:A->B A' B' f':A'->B'. isopf(f,f') ⇒ 
 ∀C g:B->C C' g':B'->C'. isopf(g,g') ⇒
 isopf(g o f, g' o f')”);

val opar_dom_cod = prove_store("opar_dom_cod",
e0
(rpt strip_tac 
>-- (rw[dom_def,cod_def] >> 
    irule opf_o_opf >> arw[opf_0f]) 
>-- (rw[dom_def,cod_def] >>
    irule opf_o_opf >> arw[opf_1f]))
(form_goal
“∀A A'. isop(A,A') ⇒ 
∀a:2->A a':2 ->A'. isopf(a,a') ⇒
 isopf(dom(a),cod(a')) ∧ 
 isopf(cod(a),dom(a'))”));


val op_ar_uex = prove_store("op_ar_uex",
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘opf(a,2,A')’ >> 
 qby_tac ‘isopf(a, opf(a, 2, A'))’ 
 >-- (irule opf_property >> arw[op_2]) >>
 drule opar_dom_cod >> first_x_assum drule >>
 arw[] >> rpt strip_tac >>
 irule is_opf >> arw[op_2])
(form_goal “∀A A'. isop(A,A') ⇒
 ∀a:2->A. ∃!a':2->A'. isopf(a,a') ∧ isopf(dom(a),cod(a')) ∧ 
 isopf(cod(a),dom(a'))”));


(*AQ: is this one needed? a bit weird

isopf(f:A->B,f':A' -> B') ⇒ isop(A,A') ∧ isop(B,B')


if do not allow equality on objects, then not able to use uex quantifier, hence should be forbidden. How?
*)

val op_cat_ex = prove_store("op_cat_ex",
e0
(strip_tac >>  
 qsspecl_then [‘Id(A)’] strip_assume_tac op_ex >>
 qexists_tac ‘Aop’ >> arw[])
(form_goal “∀A. ∃A'. isop(A,A')”));

val opf_id_id = store_ax("opf_id_id",
“∀A A'. isop(A,A') ⇒ isopf(Id(A),Id(A'))”);

(*pop assum list reverse the order...*)

val opf_unique = prove_store("opf_unique",
e0
(cheat)
(form_goal “∀A A'. isop(A,A') ⇒ ∀B B'.isop(B,B') ⇒
 ∀f:A->B f1:A'->B' f2:A' ->B'.  isopf(f,f1) ∧ isopf(f,f2) ⇒ f1 = f2”));

val op_prod = prove_store("op_prod",
e0
(rpt strip_tac >> rw[isPr_def] >>
 rpt strip_tac >> uex_tac >>
 qby_tac ‘∃X0. isop(X,X0)’ >-- rw[op_cat_ex] >>
 pop_assum strip_assume_tac >>
 drule op_op_refl >>
 qby_tac ‘∃f':X0 ->A. isopf(f,f')’ 
 >-- (irule opf_ex >> arw[] >> irule op_op_refl >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘∃g':X0 ->B. isopf(g,g')’ 
 >-- (irule opf_ex >> arw[] >> irule op_op_refl >> arw[]) >>
 pop_assum strip_assume_tac >> 
 fs[isPr_def] >>
 first_x_assum (qsspecl_then [‘f'’,‘g'’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qby_tac ‘∃fg':X->AB'. isopf(fg,fg')’
 >-- (irule opf_ex >> arw[]) >>
 pop_assum strip_assume_tac >> 
 qexists_tac ‘fg'’ >>
 qby_tac ‘p1' o fg' = f & p2' o fg' = g’ 
 >-- (strip_tac  
      >-- (qsuff_tac ‘p1' o fg' = opf(p1 o fg,X,A') ∧ 
                     f = opf(p1 o fg,X,A')’ 
          >-- (rpt strip_tac >> arw[]) >>
          strip_tac
          >-- (irule is_opf >> arw[] >> 
              qpick_x_assum ‘p1 o fg = f'’ 
              (assume_tac o GSYM) >> arw[] >>
              irule opf_o_opf >> arw[]) 
          >-- (irule is_opf >> arw[] >> 
               irule opf_opf_refl >> arw[])) >>
      cheat (*same *) ) >>
 arw[] >> rpt strip_tac >>
 qsuff_tac ‘isopf(fg, fg'')’ 
 >-- (strip_tac >> irule opf_unique >>
     qexistsl_tac [‘X0’,‘AB’,‘fg’] >> arw[]) >>
 qby_tac
 ‘p1 o opf(fg'', X0,AB) = f' ∧ 
  p2 o opf(fg'', X0,AB) = g'’
 >-- cheat >>
 qby_tac ‘opf(fg'', X0,AB) = fg’
 >-- (first_x_assum irule >> arw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 irule opf_opf_refl >> irule opf_property >> arw[] >>
 irule op_op_refl >> arw[])
(form_goal
 “∀A B AB p1:AB ->A p2:AB ->B.isPr(p1,p2) ⇒
 ∀A' B' AB'. isop(A,A') ∧ isop(B,B') ∧ isop(AB,AB') ⇒ 
 ∀p1':AB' -> A' p2':AB' -> B'. isopf(p1,p1') ∧ isopf(p2,p2') ⇒ isPr(p1',p2')”));

val op_3 = store_ax("op_3",“isop(3,3)”);

val ab_dom_cod = prove_store("ab_dom_cod",
e0
(rw[dom_def,cod_def] >> assume_tac CC4_2 >>
 fs[isPo_def])
(form_goal “dom(β) = cod(α)”));

val oa_gamma_ba = prove_store("oa_gamma_ba",
e0
(cheat)
(form_goal “∀f:2->3 g:2->3. ~isid(f) ∧ ~isid(g) ∧ dom(g) = cod(f) ⇒ g = β ∧ f = α”));

val isid_opf = prove_store("isid_opf",
e0
(cheat)
(form_goal “∀A A'. isop(A,A') ⇒ 
 (∀f:2->A. isid(f) ⇔ isid(opf(f,2,A')))”));

val ab_not_id = prove_store("ab_not_id",
e0
(cheat)
(form_goal “~isid(α) ∧ ~isid(β)”));

val dom_opf_cod = prove_store("dom_opf_cod",
e0
(rpt strip_tac >> drule opar_dom_cod >>
 irule is_opf >> arw[op_1] >> 
 qsuff_tac ‘isopf(f,opf(f,2,A'))’ 
 >-- (strip_tac >> first_x_assum drule >> arw[]) >>
 irule opf_property >> arw[op_2]
 )
(form_goal “∀A A'. isop(A,A') ⇒ 
 ∀f:2->A. dom(opf(f,2,A')) = opf(cod(f),1,A') ”));



val cod_opf_dom = prove_store("cod_opf_dom",
e0
(rpt strip_tac >> drule opar_dom_cod >>
 irule is_opf >> arw[op_1] >> 
 qsuff_tac ‘isopf(f,opf(f,2,A'))’ 
 >-- (strip_tac >> first_x_assum drule >> arw[]) >>
 irule opf_property >> arw[op_2]
 )
(form_goal “∀A A'. isop(A,A') ⇒ 
 ∀f:2->A. cod(opf(f,2,A')) = opf(dom(f),1,A') ”));


val opf_ab = prove_store("opf_ab",
e0
(irule oa_gamma_ba >>
 assume_tac op_3 >> drule $ GSYM isid_opf >> arw[] >>
 rw[ab_not_id] >> 
 drule dom_opf_cod >> arw[] >>
 drule cod_opf_dom >> arw[] >>
 assume_tac ab_dom_cod >> 
 cheat
 (*cannot use category as input, trouble here! 
 alternatively, have a machinary that regard op(_,2,3), not 
 op(_,_,_), as a function symbol.*)
 )
(form_goal “opf(α,2,3) = β ∧ opf(β,2,3) = α”));

(*if add the assumption that opf ⇒ is op cat, then agree with the actual situation, and can avoid the precondition in opf_opf_o*)

val opf_opf_o = prove_store("opf_opf_o",
e0
(rpt strip_tac >> irule is_opf >> arw[] >>
 irule opf_o_opf >> strip_tac >> irule opf_property >> arw[])
(form_goal “∀A A'.isop(A,A') ⇒ ∀B B'. isop(B,B') ⇒
  ∀C C'. isop(C,C') ⇒ 
  ∀f:A->B g:B->C. opf(g,B',C') o opf(f,A',B') = 
  opf(g o f,A',C')”));

val opf_oa = prove_store("opf_oa",
e0
(rpt strip_tac >-- (fs[cpsb_def] >>
 drule dom_opf_cod >> arw[] >>
 drule cod_opf_dom >> arw[] >> cheat
 (*same problem as above*)) >>
 qby_tac ‘cpsb(opf(f,2,A'),opf(g,2,A'))’
 >-- cheat >>
 rw[] >> drule oa_def' >> arw[] >>
 qby_tac
 ‘Poa(1f, 0f, α, β, opf(g, 2, A'), opf(f, 2, A')) = 
 opf(Poa(1f,0f,α,β,f,g),3,A')’ 
 >-- flip_tac >> irule is_Poa_ab >> fs[cpsb_def] >>
     qsuff_tac 
     ‘opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(α,2,3) =
      opf(f, 2, A') ∧ 
      opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(β,2,3) =
      opf(g, 2, A')’
     >-- rw[opf_ab] >>
     (*Poa_ab_eqn*)

cheat >>
 arw[] >> 
 qby_tac ‘γ = opf(γ,2,3)’ >-- cheat >>
 once_arw[] >> 
 qby_tac
 ‘opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(γ, 2, 3) = 
  opf(Poa(1f, 0f, α, β, f, g) o γ, 2,A')’
 >-- (irule opf_opf_o >> arw[op_2,op_3]) >>
 qpick_x_assum ‘γ = opf(γ, 2, 3)’ (K all_tac) >> 
 arw[] >>
 rev_drule oa_def' >> cheat (*same problem*))
(form_goal “∀A f:2->A g:2->A. cpsb(g,f) ⇒
 ∀A'. isop(A,A') ⇒ 
 cpsb(opf(f,2,A'),opf(g,2,A')) ∧
 opf(f,2,A') @ opf(g,2,A') = opf(g @ f,2,A')”));


val opf_op_ex = prove_store

(*for all f:A->B exists f':A'->B' such that f' is op to f and A' is op to A and B' is op to B*)

val opf1_eq = store_ax("opf1_eq",
“∀A B f:A->B g:A->B. f = g ⇒
 ∀A' B'. isop(A,A') ∧ isop(B,B') ⇒ 
 opf(f,A',B') = opf(g,A',B')”);


val opf_opf_eqn = prove_store("opf_opf_eqn",
e0
(rpt strip_tac >> 
 flip_tac >> irule is_opf >> drule op_op_refl >>
 rev_drule op_op_refl >> arw[] >>
 irule opf_opf_refl >> irule opf_property >> arw[])
(form_goal “∀A B A' B'. isop(A,A') ∧ isop(B,B') ⇒ 
 ∀f:A->B. opf(opf(f, A', B'), A, B) = f”));

rpt strip_tac >> irule Thm3_2 >> rpt strip_tac
>-- cheat >>
rw[isgen_def] >> rpt strip_tac >>
qspecl_then [‘A’] strip_assume_tac op_cat_ex >> 
qspecl_then [‘B’] (x_choose_then "B'" strip_assume_tac) 
op_cat_ex >>
qby_tac ‘~(opf(f1,A',B') = opf(f2,A',B'))’ >-- 
(ccontra_tac >>
 qsuff_tac ‘opf(opf(f1,A',B'),A,B) = f1 ∧
            opf(opf(f2,A',B'),A,B) = f2’
 >-- (drule opf1_eq >>
      first_x_assum (qspecl_then [‘A’,‘B’] assume_tac) >>
      drule op_op_refl >> 
      qby_tac ‘isop(A', A)’ >-- 
      (irule op_op_refl >> arw[]) >>
      strip_tac >> fs[]) >>
 strip_tac >> irule opf_opf_eqn >> arw[]) >>
drule CC2_2 >> pop_assum strip_assume_tac >>
qexists_tac ‘opf(a,op2,A)’ >>
qby_tac ‘opf(opf(a, op2, A),2,A') = a’
>-- irule opf_opf_eqn >> arw[] >> irule op_op_refl >> arw[]>>
    qby_tac ‘~(opf(f1, A', B') o opf(opf(a, op2, A), 2, A') =
              opf(f2, A', B') o opf(opf(a, op2, A), 2, A'))’      >-- arw[] >>
    qby_tac ‘opf(f1, A', B') o opf(opf(a, op2, A), 2, A') = 
             opf(f1 o opf(a, op2, A),2,B')’
    >-- (irule opf_opf_o >> arw[] >> 
        irule op_op_refl >> arw[]) >>
    qby_tac ‘opf(f2, A', B') o opf(opf(a, op2, A), 2, A') = 
             opf(f2 o opf(a, op2, A),2,B')’
    >-- (irule opf_opf_o >> arw[] >> 
        irule op_op_refl >> arw[]) >>
    fs[] >> 
    ccontra_tac >> drule opf1_eq >>
    first_x_assum (qspecl_then [‘2’,‘B'’] assume_tac) >>
    rfs[] >> rev_drule op_op_refl >> fs[]
        


qexists_tac ‘opf(a,op2,A')’
“∀op2. isop(2,op2) ⇒ areIso(op2,2)”




 _^op preserves identity functors, domains, codomains and composites of
 functors, and, for all A and F


F:A -> B
F^op: A^op -> B^op

