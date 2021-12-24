


(*

when a formula with fVar is to be insted, we first look at the free variables in the formula to be insted, and identify if there are variables which should be free after inst, but will be captured by quantifiers. if there are, rename the bound variables, so they will not be matched to the ones that should be free. 

for instance, when inst !a. P(a) with 

P: λf. isInj(f) & a in im(f).

the a 
*)
fun newname names n = 
    if HOLset.member(names,n) then n
    else newname names (n^"'") 

(*a bit worry for the case !n. P(n#) & n = a
when view_form, it will give
"n'" and P(n') & n = a
instead of n.

val f = “!f:A->B. isFun(f) & f = a ”

val n' = "g"

val ((n,s),b) = dest_forall f

val f0 = “(!f:A->B. f = a) <=> (!g. g = a)”
val th0 = mk_thm(fvf f0,[],f0)

val f1 = “(!f:A->B. f = a) & a = b”

basic_fconv 

*)

fun rename_forall_fconv f n' = 
    case view_form f of
        vQ("!",n,s,b) => 
        let val b' = mk_forall n' s (substf ((n,s),mk_var(n',s)) b)
            val l2r = 


fun fVar_Inst1 (pair as (P,(argl:(string * sort) list,Q))) f = 
    case view_form f of
        vfVar(P0,args0) =>
(*ListPair.map ListPair.foldl*)
(*mk_inst (zip argl args0)ListPair. [] *)
        if P0 = P then
            let val venv = match_tl essps (List.map mk_var argl) args0 emptyvd 
            in inst_form (mk_menv venv emptyfvd) Q
            end
(*if the number of arguments is wrong, or the sorts is wrong, then handle the matching exn by returning f *)
        else f
      | vConn(co,fl) => mk_conn co (List.map (fVar_Inst1 pair) fl)
      | vQ(q,n,s,b) => mk_quant q n s (fVar_Inst1 pair b)
      | vPred _ => f


(*in last meeting discussed that :
P(a:mem(A),b:mem(B))

Q(c:mem(C),d:mem(D))

should not be allowed since the sort is incorrect, but if use rw, then can just use fVar to inst form. 
*)

(*ex2fsym should check that the input thm does not contain fvars*)

fun fVar_Instl l f = 
    case l of [] => f
            | pair :: t => fVar_Inst1 pair (fVar_Instl t f)

fun fVar_Inst l th = 
    let val (ct,asl,w) = dest_thm th
        val asl' = List.map (fVar_Instl l) asl
        val w' = fVar_Instl l w
        val vs = bigunion (pair_compare String.compare sort_compare)
                          (List.map fvf (w' :: asl'))
        val newct = HOLset.union(ct,vs)
    in mk_thm (newct,asl',w')
    end
