
fun v2t (V:string * sort) (t:term) env = Binarymap.insert(env,V,t)
        
fun match_t nss pat ct env = 
    case (view_term pat,view_term ct) of 
        (vFun(f1,s1,l1),vFun(f2,s2,l2)) => 
        if f1 <> f2 then 
            raise TER("match_term.different function names: ",[],[pat,ct])
        else (match_s nss s1 s2 (match_tl nss l1 l2 env))
      | (vVar(n1,s1),_) => 
        if has_bound_t ct then 
            raise TER ("match_term.attempting matching to a term with bounded variable",[],[]) 
        else  
        if HOLset.member(nss,(n1,s1)) then
            if pat = ct then env 
            else raise TER ("match_term.current term is local constant: ",[],[pat,ct])
        else 
            (case (Binarymap.peek(env,(n1,s1))) of
                 SOME t => if t = ct then env else
                           raise TER ("match_term.double bind: ",[],[pat,t,ct])
               | _ => 
                 v2t (n1,s1) ct (match_s nss s1 (sort_of ct) env))
      | (vB i1,vB i2) => 
        if i1 <> i2 then 
            raise TER ("match_term.bound variables have different levels: ",[],[pat,ct])
        else env
      | _ => raise Fail "match_term.unexpected term constructor"
and match_s nss sp cs env = 
    case (dest_sort sp,dest_sort cs) of 
        ((sn1,tl1),(sn2,tl2)) =>
        if sn1 = sn2 then
            match_tl nss tl1 tl2 env
        else raise TER ("match_sort.attempting matching two different sorts: "^ sn1 ^ " , " ^ sn2,[sp,cs],[])
and match_tl nss l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_tl nss t1 t2 (match_t nss h1 h2 env)
      | _ => raise TER ("match_sort.incorrect length of list",[],[])



fun inst_t env t = 
    case view_term t of 
        vVar(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => mk_var (n,inst_sort env s))
      | vFun(f,s,tl) => mk_fun0 f (inst_sort env s) (List.map (inst_term env) tl)
      | _ => t
and inst_s env s = 
    case (dest_sort s) of
        (sn,tl) => 
        mk_sort sn (List.map (inst_term env) tl)




(*


fun fv2f' fm f menv0: menv = mk_menv (vd_of menv0) (fv2f fm f (fvd_of menv0))


fun lookup_f' (menv:menv) fm = Binarymap.peek (fvd_of menv,fm)


fun match_s' nss s1 s2 (vd,fvd: string * ) = (match_s nss s1 s2 vd,fvd)

*)

fun fvf_list f = HOLset.listItems (fvf f)


P(f(a)) match to ismono(f(a))

if only collect variables, not terms of formula, then the match of 
P(f(a)) to any formula always fail.

Therefore for P(n) ==> P(Suc(n)), the match will fail


fun term_list f = 
    case view_form f of 
        vPred(_,_,tl) => tl
      | vConn(_,fl) => List.concat (List.map term_list fl)
| 


(*one input is arrangement of variables of formula, candidates can be:

-- all free variables, in order of appear, or in alphabetical order
-- free variables which has certain name
-- variables with certain sort

vlfn should be tlfn ...

this is throwing the problem of what to choose to match to the user... 
*)

fVar_Inst1 ("P",([("a",mem_sort N)],“”))

val l = 
 fVar_Inst1
("P",([("n",mem_sort N)],
 “Sub(Suc(m),Suc(n)) = Sub(m,n)”))
 “P(Suc(a))”

fVar_Inst1
("P",([("n",mem_sort N)],
 “Sub(Suc(m),Suc(n)) = Sub(m,n)”))
 “P(n:mem(N))”


 N_ind_P 
if P(f(a)) matches to (Q1(f(a0)),b), where a |-> a0. 


(*a lambda-abstraction is a (var list,form) pair,
 we can define alpha-equivalent of such pairs
*)

val evd:(string * sort, term) Binarymap.dict = Binarymap.mkDict (pair_compare String.compare sort_compare)

val efvd:(string, (string * sort) list * form) Binarymap.dict = Binarymap.mkDict String.compare 
(*two lambda abstractions with different fvars are definitely not the same*)


(*temp, will edit it so it does not quote inst-form, which will be edited*)
fun inst_vars_form vd f1 = 
    let val env = mk_inst (Binarymap.listItems vd) []
    in inst_form env f1
    end

fun aconv (vl1,f1) (vl2,f2) = 
    let val vd = match_tl essps (List.map mk_var vl1) (List.map mk_var vl2) evd
        val f2' = inst_vars_form vd f1
    in eq_form(f1,f2')
    end

(*can we require that if we want to match to gain a lambda abstraction, then the domain of matching will have all its inputs variables?

so it will not match P(Suc(n)) to anything and conclude what the pred P is . But if the definition of P(n) is given in some dict, then we can inst P(Suc(n)) using the dict.

*)


(*should the key be string, so every string can only associate to one fvar?

P(a:mem(A),b:mem(B))
P(c:mem(A),d:mem(B)) should be the same fvar

so do not think want P and a var list as key, instead, use 

we can have in one formula two diff fvar, just let matching do nothing for them, but can inst them by hand.

how to deal with match of P(f(a))? 
*)
val vlfn0 = (List.map mk_var) o HOLset.listItems o fvf
        
val pat = “!n:mem(N). P(n)” ;
val cf = “!n. Sub(Suc(m),Suc(n)) = Sub(m,n)”

val vd = evd; val fvd = efvd;

val eps = HOLset.empty (pair_compare String.compare $ list_compare (pair_compare String.compare sort_compare))

val vlfn0 = fn (f:form) => [mk_var ("n",mem_sort N)]

match_f vlfn0 essps eps pat cf (evd,efvd)

should the vlfn function take some parameter?

fun pdicts (vd,fvd) = (Binarymap.listItems vd,Binarymap.listItems fvd)

fun match_f (vlfn: form -> term list)
        (nss:(string * sort) set) 
        (ps:(string * (string * sort) list) set) 
        pat cf 
        (vd,fvd:(string, (string * sort) list * form)Binarymap.dict) = 
    case (view_form pat,view_form cf) of
        (vPred(P1,true,l1),vPred(P2,true,l2)) => 
        if P1 <> P2 then 
            raise ERR ("different predicates: ",[],[],[pat,cf])
        else (match_tl nss l1 l2 vd,fvd) 
      | (vConn(co1,l1),vConn(co2,l2)) => 
        if co1 <> co2 then 
            raise ERR ("different connectives: ",[],[],[pat,cf])
        else match_fl vlfn nss ps l1 l2 (vd,fvd)  
      | (vQ(q1,n1,s1,b1),vQ(q2,n2,s2,b2)) => 
        if q1 <> q2 then 
            raise ERR ("different quantifiers: ",[],[],[pat,cf])
        else 
            let val vd1 = match_s nss s1 s2 vd
            in match_f vlfn nss ps b1 b2 (vd1,fvd)
            end
      | (vPred(fm,false,args),_) => 
        let val fvl = vlfn cf
            val laminputs = List.map dest_var args
            val vd1 = match_tl nss args fvl vd
        in case Binarymap.peek(fvd,fm)
            of
               SOME (ags,pf) => 
               if aconv (ags,pf) (laminputs,cf) then 
                   (vd1,fvd)
               else raise simple_fail ("double bind of formula variable: "^ fm)
             | NONE => (vd1,Binarymap.insert(fvd,fm,(laminputs,cf)))
        end 
        handle _ => (vd,fvd)
      | _ => raise ERR ("different formula constructors",[],[],[pat,cf])
fun match_fl vlfn nss ps l1 l2 (vd,fvd) = 
    case (l1,l2) of 
        ([],[]) => (vd,fvd)
      | (h1::t1,h2::t2) =>  
        match_fl vlfn nss ps t1 t2 (match_f vlfn nss ps h1 h2 (vd,fvd))
      | _ => raise simple_fail "incorrect length of list"



fun inst_term' env t = inst_term (vd_of env) t

fun inst_sort' env s = inst_sort (vd_of env) s

fun name_clash n env = 
    let
        val new_terms = List.map snd (pvd (vd_of env))
        val new_names = mapfilter (fst o dest_var) new_terms
    in 
        List.exists (fn n0 => n0 = n) new_names
    end

fun rename_once_need n env = 
    if name_clash n env = false then n else rename_once_need (n^"'") env

fun inst_form env f = 
    case view_term f of
        Pred(P,true,tl) => Pred(P,true,List.map (inst_term' env) tl)
      | Conn(co,fl) => Conn(co,List.map (inst_form env) fl)
      | Quant(q,n,s,b) => 
        let 
            val s' = inst_sort' env s
            val b' = inst_form env b
            val n' = rename_once_need n env 
        in 
            Quant(q,n',s',b')
        end
      | Pred(f,false,tl) => 
        (case lookup_f' env f of
             SOME f' => inst_form env f'
           | NONE => Pred(f,false,List.map (inst_term' env) tl))
    (*  | fVar fvn => 
        (case lookup_f' env fvn of
             SOME f' => f'
           | NONE => f)*)



fun inst_thm env th = 
    if is_wfmenv env then
        let
            val G0 = HOLset.listItems (cont th)
            val G = var_bigunion (List.map (fvt o (inst_term (vd_of env)) o mk_var) G0)
            val A = List.map (inst_form env) (ant th)
            val C = inst_form env (concl th)
        in
            thm(G,A,C)
        end
    else raise simple_fail "bad environment"


(*
goal of this:

fVar should be a case of inst_thm 

need to make sure that bounded variable before inst are still bound.



*)
