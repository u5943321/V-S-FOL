
Cat

Ob: Cat

Ar Ob Ob

Fun Cat

Nat: Fun Fun

!C. X Y:Ob(C) f:X->Y g:Y->X. id(X) o g = g & f o id(Y) = f


















fun fVar_Inst_th (pair as (P,(argl:(string * sort) list,Q))) th = 
    let val (ct,asl,w) = dest_thm th
        val asl' = List.map (form.fVar_Inst_f pair) asl
        val w' = form.fVar_Inst_f pair w
        val vs = bigunion (pair_compare String.compare sort_compare)
                          (List.map fvf (w' :: asl'))
        val newct = HOLset.union(ct,vs)
    in mk_thm (newct,asl',w')
    end


val Imp_lemma = prove_store("Imp_lemma",
e0
(rw[Imp_property] >> rpt strip_tac >> arw[])
(form_goal “(p = TRUE <=> P) & (q = TRUE <=> Q) ==> (Imp(p,q) = TRUE <=> (P ==> Q))”));


val Imp_lemma = prove_store("Imp_lemma",
e0
(rw[GSYM Imp_def] >> rw[o_assoc] >>rw[Pa_distr] >>
 rw[IMP_def] >> rpt strip_tac >> arw[])
(form_goal “(p o Pa(n:1->A,m:1->B) = TRUE <=> P) & (q o Pa(n,m) = TRUE <=> Q) ==> (Imp(p,q) o Pa(n,m) = TRUE <=> (P ==> Q))”));



val Imp_lemma = prove_store("Imp_lemma",
e0
(rw[GSYM Imp_def] >> rw[o_assoc] >>rw[Pa_distr] >>
 rw[IMP_def] >> rpt strip_tac >> arw[])
(form_goal “!A p:A->1+1 q:A-> 1+1 a. (p o a = TRUE <=> P) & (q o a = TRUE <=> Q) ==> (Imp(p,q) o a = TRUE <=> (P ==> Q))”));


val Iff_lemma = prove_store("Iff_lemma",
e0
(rw[GSYM Iff_def] >> rw[o_assoc] >>rw[Pa_distr] >>
 rw[IFF_def] >> rpt strip_tac >> arw[])
(form_goal “!A p:A->1+1 q:A-> 1+1 a. (p o a = TRUE <=> P) & (q o a = TRUE <=> Q) ==> (Iff(p,q) o a = TRUE <=> (P <=> Q))”));


val And_lemma = prove_store("And_lemma",
e0
(rw[GSYM And_def] >> rw[o_assoc] >>rw[Pa_distr] >>
 rw[CONJ_def] >> rpt strip_tac >> arw[])
(form_goal “!A p:A->1+1 q:A-> 1+1 a. (p o a = TRUE <=> P) & (q o a = TRUE <=> Q) ==> (And(p,q) o a = TRUE <=> (P & Q))”));


val Or_lemma = prove_store("Or_lemma",
e0
(rw[GSYM Or_def] >> rw[o_assoc] >>rw[Pa_distr] >>
 rw[DISJ_def] >> rpt strip_tac >> arw[])
(form_goal “!A p:A->1+1 q:A-> 1+1 a. (p o a = TRUE <=> P) & (q o a = TRUE <=> Q) ==> (Or(p,q) o a = TRUE <=> (P | Q))”));


val Not_lemma = prove_store("Not_lemma",
e0
(rw[GSYM Not_def] >> rw[o_assoc] >>rw[Pa_distr] >>
 rw[NEG_def,TRUE_xor_FALSE] >> rpt strip_tac >> arw[])
(form_goal “!A p:A->1+1 a. ((p o a = TRUE)  <=> P) ==>
 (Not(p) o a = TRUE <=> ~P)”));





(*
val EX_lemma = prove_store("EX_lemma",
e0
(rw[EX_property] >> rpt strip_tac >> arw[])
(form_goal 
 “!A B b p:A * B -> 1+1. (!a.p o Pa(a,b) = TRUE <=> P(a,b)) ==>
 (EX(p:A * B -> 1+1) o b = TRUE <=>
 (?a:1->A. P(a,b)))”));
*)


val EX_lemma = prove_store("EX_lemma",
e0
(rw[EX_property] >> rpt strip_tac >> arw[])
(form_goal 
 “!A B b p:A * B -> 1+1. (!a.p o Pa(a,b) = TRUE <=> P(a,b)) ==>
 (EX(p:A * B -> 1+1) o b = TRUE <=>
 (?a:1->A. P(a,b)))”));


val ALL_lemma = prove_store("ALL_lemma",
e0
(rw[ALL_property] >> rpt strip_tac >> arw[])
(form_goal 
 “!A B b p:A * B -> 1+1. (!a.p o Pa(a,b) = TRUE <=> P(a,b)) ==>
 (ALL(p:A * B -> 1+1) o b = TRUE <=>
 (!a:1->A. P(a,b)))”));



val Eq_lemma = prove_store("Eq_lemma",
e0
(rpt strip_tac >>
 qsspecl_then [‘a12’] strip_assume_tac has_components >>
 arw[] >> fs[Eq_property_TRUE,p12_of_Pa] >> rpt strip_tac >> arw[])
(form_goal 
 “!X a12:1->X * X a1 a2. 
  p1(X,X) o a12 = a1 &
  p2(X,X) o a12 = a2 ==>
  (Eq(X) o a12 = TRUE <=> a1 = a2)”));

fun IL_tac (g as (ct,asl,w)) = 
    let val (il,f) = dest_dimp w
    in case view_form f of
           Conn("&",_) => 
           let val (gl1,pf1) = irule And_lemma g
           in 

(*need to detect pattern of 

P(n,m) |-> !n. P(n,m)


P(a,b) |-> !a. P(a,b)

P(a) |-> !a. P(a)


\x y. P x y |-> \y. !x. P x y

 

*)


val Add_prop = prove_store("Add_prop",
e0
(rw[GSYM Add_def] >> rw[Pa_distr,o_assoc])
(form_goal
 “!A X a:A->N b c:X->A. Add(a,b) o c = Add(a o c, b o c)”));


val Le_Add_ex = prove_store("Le_Add",
e0
(qby_tac
 ‘?P. !m. P o m = TRUE <=> 
  (!n.Le(n,m) ==> ?p. Add(p,n) = m)’
 >-- exists_tac $
 form2IL [dest_var $ rastt "m:1->N"] 
 “!n.(Le(n:1->N,m) ==> ?p. Add(p,n) = m)” >>
 rw[ALL_property,GSYM Imp_def,o_assoc,Pa_distr,IMP_def,
    EX_property,GSYM Le_def1,p12_of_Pa,
    Eq_property_TRUE,Add_prop,Pa3_def,p31_of_Pa3,
    p33_of_Pa3,p32_of_Pa3] >>
 

 
(*

Le(Suc(n),0) <=> F


Le(Suc(n),0)

Le,Suc,v(for var),0




*)

cheat >>
 pop_assum strip_assume_tac >>  
 qsuff_tac ‘!m. P o m = TRUE’ 
 >-- arw[] >> 
 rw[IP_el] >> arw[] >>
 rpt strip_tac
 >--  (arw[] >> qexists_tac ‘O’ >> rw[Add_O]) >>


qby_tac
 ‘?P. !n m. P o Pa(n,m) = TRUE <=> 
  (Le(n,m) ==> ?p. Add(p,n) = m)’
 >--
 exists_tac $
 form2IL [dest_var $ rastt "n:1->N",
          dest_var $ rastt "m:1->N"] 
 “(Le(n:1->N,m) ==> ?p. Add(p,n) = m)” >>
 rpt strip_tac >> 
 irule Imp_lemma >>
 rpt strip_tac (* 2 *)
 >-- irule (fVar_Inst_th ("P",([("a",ar_sort ONE N),
                         ("n",ar_sort ONE (Po N N))],“Add(a,Fst(b)) = Snd(b:1-> N * N)”))
     (EX_lemma |> qspecl [‘N’,‘N * N’] |> spec_all)
     |> qgen ‘b’ |> qspecl [‘Pa(n:1->N,m:1->N)’]
     |> rewr_rule[Fst_Snd_Pa] ) >>
     rpt strip_tac >> rw[o_assoc] >> irule Eq_lemma >>
     (*a point to mark, no tool allows simplifiying 
      Pa(Add(p31(N, N, N), p32(N, N, N)), p33(N, N, N)) o
               Pa(a, Pa(n, m))
      into Add(a,n,m),
      if allow it, perhaps need something called function variables...*)
     rw[GSYM Add_def,
        GSYM p31_def,GSYM p32_def,GSYM p33_def] >>
     rw[p12_of_Pa,Pa_distr,o_assoc]
  >-- rw[o_assoc,Pa_distr,p12_of_Pa,Le_def1] >>



 rw[GSYM Imp_def] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[IMP_def] >>
 rw[o_assoc] >> rw[Pa_distr] >>
 rw[GSYM p31_def,GSYM p32_def,GSYM p33_def] >>
 rw[p12_of_Pa] >>
 rw[EX_property] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[Eq_property_TRUE] >>
 rw[GSYM Add_def] >> rw[o_assoc] >> rw[Pa_distr] >>
 rw[p12_of_Pa] >> rw[o_assoc] >> rw[p12_of_Pa] >>
 rw[GSYM Le_def1]


)
(form_goal
 “!m:1->N n. Le(n,m) ==> ?p. Add(p,n) = m”));



val LESS_MONO_ADD = prove_store("LESS_MONO_ADD",
e0
(strip_tac >> strip_tac >>
qby_tac
 ‘?P. !p.
 P o p = TRUE <=>
 (Lt(m,n) <=> Lt(Add(m,p),Add(n,p)))’
 >-- (
 exists_tac $
 form2IL [dest_var $ rastt "p:1->N"]
 “(Lt(m:1->N,n) <=> Lt(Add(m,p),Add(n,p)))” >>
 rpt strip_tac >>
 irule Iff_lemma >> strip_tac (* 2 *)
 >-- rw[GSYM Add_def,o_assoc,Pa_distr,
        one_to_one_id,idL,idR,Lt_def1]


 rw[GSYM Iff_def] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[IFF_def] >>
 rw[o_assoc] >> rw[Pa_distr] >>
 (*rw[p12_of_Pa] >>
 rw[EX_property] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[Eq_property_TRUE] >> *)
 rw[GSYM Add_def] >> rw[o_assoc] >> rw[Pa_distr] >>
 (*rw[p12_of_Pa] >> *) rw[o_assoc] >> (*rw[p12_of_Pa] >>*)
 rw[one_to_one_id] >> rw[idL,idR] >>
 rw[GSYM Lt_def1]


 rw[GSYM Iff_def] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[IFF_def] >>
 rw[o_assoc] >> rw[Pa_distr] >>
 rw[p12_of_Pa] >>
 rw[EX_property] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[Eq_property_TRUE] >> 
 rw[GSYM Add_def] >> rw[o_assoc] >> rw[Pa_distr] >>
 rw[p12_of_Pa] >> rw[o_assoc] >> rw[p12_of_Pa] >>
 rw[one_to_one_id] >> rw[idL,idR] >>
 rw[GSYM Lt_def1]


)
(form_goal
 “!m:1->N n p. Lt(m,n) <=> Lt(Add(m,p),Add(n,p))”));


val EQ_MONO_ADD_EQ = prove_store("EQ_MONO_ADD_EQ",
e0
(strip_tac >> strip_tac >>
 qby_tac
 ‘?P. !p.  
 P o p = TRUE <=> 
 Add(m,p) = Add(n,p) <=> m = n’
 >-- (
 exists_tac $
 form2IL [dest_var $ rastt "p:1->N"]
 “Add(m,p) = Add(n,p) <=> m = n:1->N” >>

 rw[GSYM Iff_def] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[IFF_def] >>
 rw[o_assoc] >> rw[Pa_distr] >>
 (*rw[p12_of_Pa] >>
 rw[EX_property] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[Eq_property_TRUE] >> *)
 rw[GSYM Add_def] >> rw[o_assoc] >> rw[Pa_distr] >>
 (*rw[p12_of_Pa] >> *) rw[o_assoc] >> (*rw[p12_of_Pa] >>*)
 rw[one_to_one_id] >> rw[idL,idR] >>
 rw[Eq_property_TRUE]



 rw[GSYM Iff_def] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[IFF_def] >>
 rw[o_assoc] >> rw[Pa_distr] >>
 rw[p12_of_Pa] >>
 rw[EX_property] >> rw[o_assoc] >>
 rw[Pa_distr] >> rw[Eq_property_TRUE] >> 
 rw[GSYM Add_def] >> rw[o_assoc] >> rw[Pa_distr] >>
 rw[p12_of_Pa] >> rw[o_assoc] >> rw[p12_of_Pa] >>
 rw[one_to_one_id] >> rw[idL,idR] >>
 rw[GSYM Lt_def1]

 

)
(form_goal
 “!m:1->N n p. Add(m,p) = Add(n,p) <=> m = n”));



val Suc_NEQ = prove_store("Suc_NEQ",
e0
(qby_tac
 ‘?P. !a. P o a = TRUE <=> (a = Suc(a))’
 >-- (
 exists_tac $
 form2IL [dest_var $ rastt "a:1->N"]
 “a = Suc(a:1->N)” >>
 
 )
(form_goal “!a:1->N. ~(a = Suc(a))”));


Eq_property_TRUE
ALL_def
EX_def

fun ind_rw (ct,asl,w) = 
    let val funs = fsymsf w
        val t1 = if List.exists
                    (fn str => HOLset.member(funs,str))
                 ["All","Ex","And","Or","Imp","Iff"]
                 then rw[GSYM All_def]

    in if 
