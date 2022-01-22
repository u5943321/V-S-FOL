(*
input !a. newP(a) <=> 
          (Pbase(a0) ==> P(a0)) &
          !a1. Pstep(a1) ==> P(a1)



       P(!P.IN(Empty(X),P) &
 (!xs0. IN(xs0,P) ==> !x. IN(Ins(x,x0),P)) ==> 
 IN(xs,P))

*)














use Reln to define N

!n. P o n = 
\

(*sense of power set should be a part of input*)

val f = “!x xs. FINITE(xs:mem(Pow(X))) <=>
(!P.IN(Empty(X),P) &
 (!xs0. IN(xs0,P) ==> !x. IN(Ins(x,x0),P)) ==> 
 IN(xs,P))”

val _ = new_pred "inN" [("n",mem_sort (rastt "N0"))]

val f =“!n:mem(N0). inN(n) <=>
(!P.IN(O0,P) &
 (!n0. IN(n0,P) ==> IN(Eval(S0,n0),P)) ==> 
 IN(n,P))”

(*store_ax “”

define_pred
define_fun 

cheat*)

val th0 = mk_thm (essps,[],f);


val rules0_base = proved_th $ 
e0
(rw[th0] >> rpt strip_tac)
(form_goal “inN(O0)”)



val rules0_step = proved_th $ 
e0
(rw[th0] >> rpt strip_tac >> 
 first_assum irule >>
 first_x_assum irule >> arw[])
(form_goal “!n0. inN(n0) ==> inN((Eval(S0,n0)))”)

val ind0 = th0 |> spec_all |> iffLR
                      |> undisch
                      |> strip_all_and_imp
                      |> disch “inN(n)”
                      |> gen_all
                      |> disch_all |> gen_all


(*better have automatic match from P to the input formula, since only have one variable.*)

val l = fVar_Inst 
[("P",([("n0",mem_sort (rastt "N0"))],
 “n0 = O0 | ?a:mem(N0). n0 = Eval(S0, a) & inN(a)”))]
 (IN_def_P_expand |> qspecl [‘N0’])
val cases0 = proved_th $
e0
(strip_tac >> dimp_tac >--
 (strip_assume_tac l >> pop_assum (K all_tac) >>
  arw[] >> match_mp_tac ind0 (*irule does not work since it will strip to the outmost, should we handle this error by let irule do less strip?*)>>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rpt strip_tac (* 2 *)
 >-- (disj2_tac >> qexists_tac ‘n0'’ >> 
     arw[rules0_base]) >>
 disj2_tac >> qexists_tac ‘n0'’ >> arw[] >>
 drule rules0_step >> arw[]) >>
 strip_tac (* 2 *)
 >-- arw[rules0_base] >>
 arw[] >> irule rules0_step >> arw[])
(form_goal
 “!n0. inN(n0) <=> n0 = O0 |
  (?a. n0 = Eval(S0,a) & inN(a))”)


(*
.... ==> P(a,b)


T ==> P(a,b)


J. Harrison
   "Inductive Definitions: Automation and Application"
   In: E. T. Schubert, P. J. Windley and J. Alves-Foss (editors),
   "Proceedings of the 8th International Workshop on Higher Order Logic
   Theorem Proving and Its Applications", Aspen Grove, UT, USA, September 1995.
   Volume 971 of Lecture Notes in Computer Science, Springer-Verlag,
   pages 200-213.



*)

(*so define a relation is let the input be member of somme product

Should the sort fun be obtained by type_definition?

*)


val Cd_cases =
   ⊢ ∀a0 a1.
       R a0 a1 ⇔
       a0 = ∅ ∧ a1 = 0 ∨
       ∃xs n x0. a0 = {x0} ∪ xs ∧ a1 = SUC n ∧ R xs n ∧ x0 ∉ xs: Thm.thm
val Cd_ind =
   ⊢ ∀R'.
       R' ∅ 0 ∧ (∀xs n x0. R' xs n ∧ x0 ∉ xs ⇒ R' ({x0} ∪ xs) (SUC n)) ⇒
       ∀a0 a1. R a0 a1 ⇒ R' a0 a1: Thm.thm
val Cd_rules = ⊢ R ∅ 0 ∧ ∀xs n x0. R xs n ∧ x0 ∉ xs ⇒ R ({x0} ∪ xs) (SUC n):
   Thm.thm

(*raw version, base case does not have implication, 
 input element not a pair, only two clauses
*)
fun Reln f = 
    let val ((n,s),b) = dest_forall f
        val (todefine,cond) = dest_dimp b
        val ((P,sp),c0) = dest_forall cond
        val (ant0,concl0) = dest_imp c0
        val (basec,indc) = dest_conj ant0
        val bm = hd $ snd $ dest_pred basec
        val th0 = mk_thm(fvf f,[],f)
        val ind = th0 |> spec_all |> iffLR
                      |> undisch
                      |> strip_all_and_imp
                      |> disch todefine
                      |> gen_all
                      |> disch_all |> gen_all
        val rules = 
            conjI (th0 |> allE bm 
                       |> iffRL |> undisch
                       |> rewr_rule[th0])
        val rules = 


val rules = mk_thm(fvf f,[],f)
        val cjs = List.map concl (conjuncts rules)
        val 

Inductive genRel:
(!a b:num.  a = b ==> genRel 0 a b ) ∧
 !n a b. genRel n a b ==> 
         genRel n (SUC a) (SUC b)
End

IN ETCS

“FINITE(xs) <=> !P:1->Exp(Exp(X,1+1),1+1). 
 IN(Empty(X),P) &
 !xs. 

(P o Empty(X) = TRUE &
 !xs. P o xs = TRUE ==> !x.P o Ins(x,xs) = TRUE) ==>
 P o xs = TRUE”


AX1 ver without fvar:
!ss:Pow(A * B). ?R. !a b. Holds(R,a,b) <=> IN(Pair(a,b),ss)

then rely on IN_def_P



IN SEAR 

“FINITE(xs) <=> !ss:Pow(Pow(X)). 
 (IN(Empty(X),ss) & 
 !xs. IN(xs,ss) ==> !x.IN(Ins(x,xs),ss)) ==>
 IN(xs,ss)”


input is 
“!a.P0(a) ==> P(a) &
 !a.P(a) ==> Q(a) ==> P(f a)”

(*
To define a rel by recursion.


P(a0,b0) <=> R(a0,b0) & 
(!a b. P(a,b) ==> !a' b'. Q(a,b,a',b') ==> 
 P(a',b'))

!a b. P(a,b) <=>
 !ss. (R(a0,b0) <=> IN(Pair(a0,b0),ss)) &
      !a1 b1. IN(Pair(a1,b1),ss) ==>
      !a1' b1'. Q(a1,b1,a1',b1') ==> 
      IN(Pair(a1',b1'),ss)


P_ind
ind principle:
((R(a0,b0) ==> P1(a0,b0)) &
!a b. P1(a,b) ==> 
  !a' b'. Q(a,b,a',b') ==> P1(a',b')) ==>
!a b. P(a,b) ==> P1(a,b)

P_rules:

(R(a0,b0) ==> P(a0,b0)) & 
!a b. P(a,b) ==> 
 !a' b'.Q(a,b,a',b') ==> P(a',b')


P_cases:

!a b. P(a,b) <=> 
 (R(a,b)) |
 ?a0 b0. Q(a0,b0,a,b) & P(a0,b0)


*)
