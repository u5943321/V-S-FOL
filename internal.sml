
(*proposed soluion as alternative to choose a pullback object to reduce the parameters, and build the whole diagram,

but may need to prove this approach does give such a diagram to show it works...*)

val is_o_def = store_ax("is_o_def", (*should be define_pred*)
“∀Ar Ob d:Ar -> Ob c:Ar -> Ob
  P π1:P (*Ar *_Ob Ar -> Ar*) -> Ar π2:P -> Ar cps:P -> Ar X a1:X->Ar a2:X-> Ar a:X->Ar.
  is_o(a1,a2,a,cps) ⇔ 
  isPb(d,c,π1,π2) ∧ 
  d o a2 = c o a1 ∧ 
  a = cps o Pba(d,c,π1,π2,a1,a2)”);

(*use big product instead*)
val is_intcat_def = store_ax("is_intcat_def",
“∀Ar Ob d:Ar -> Ob c:Ar -> Ob
  P π1:P -> Ar π2:P -> Ar cps:P -> Ar id:Ob -> Ar.
 is_intcat(d,c,id,π1,π2,cps) ⇔ 
 ∀X a1:X->Ar a2:X->Ar a3:X-> Ar a12 a23 a123.
 is_o(a1,a2,a12,cps) ∧ is_o(a2,a3,a23,cps) ⇒
 is_o(a1,a23,a123,cps) ∧ is_o(a12,a3,a123,cps)”);



