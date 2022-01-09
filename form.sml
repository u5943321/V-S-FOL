structure form :> form = 
struct
open term 

datatype form =
Pred of string * bool * term list
| Conn of string * form list
| Quant of string * string * sort * form




(*

datatype form =
Pred of string * bool * term list
| Conn of string * form list
| Quant of string * string * sort * form

eq_psym then ignore the bool   



*)
exception ERR of string * sort list * term list * form list

fun simple_fail s = ERR (s,[],[],[]) 

fun wrap_err s exn = 
    case exn of ERR (s0,sl,tl,fl) => ERR (s^s0,sl,tl,fl)
              | TER (s0,sl,tl) => ERR (s^s0,sl,tl,[])
              | _ => raise simple_fail s 

(*edit same code of pred and fvar*)
fun subst_bound t = 
    let fun subst i (Pred(a,b,ts)) = 
            Pred(a, b,List.map (replacet (i, t)) ts) 
          | subst i (Conn(b,As)) = Conn(b, List.map (subst i) As) 
          | subst i (Quant(q,n,s,b)) =
            Quant(q, n, replaces (i,t) s, subst (i+1) b)
    in subst 0 end


fun substf (V,t2) f = 
    case f of 
        Pred(P,b,tl) => Pred(P,b,List.map (substt (V,t2)) tl)
      | Conn(co,fl) => Conn(co,List.map (substf (V,t2)) fl)
      | Quant(q,n,s,b) => Quant(q,n,substs (V,t2) s,substf (V,t2) b)


fun abstract t = 
    let fun abs i (Pred(a,b,ts)) = Pred(a,b, List.map (substt (t,mk_bound i)) ts) 
          | abs i (Conn(b,As)) = Conn(b, List.map (abs i) As) 
          | abs i (Quant(q,b,s,A)) = 
            Quant(q, b, substs (t, mk_bound (i)) s, abs (i+1) A)
    in abs 0 end;


fun fvf f = 
    case f of 
        Pred(P,b,tl) => fvtl tl
      | Conn(co,fl) => fvfl fl
      | Quant(q,n,s,b) => HOLset.union (fvs s,fvf b)
and fvfl G = 
    case G of [] => essps
            | h :: t => HOLset.union (fvf h,fvfl t)

(*predicate functions*)

fun is_imp f = 
    case f of
        Conn("==>",[f1,f2]) => true
      | _ => false

fun is_dimp f = 
    case f of
        Conn("<=>",[f1,f2]) => true
      | _ => false

fun is_conj f = 
    case f of
        Conn("&",[f1,f2]) => true
      | _ => false

fun is_disj f = 
    case f of
        Conn("|",[f1,f2]) => true
      | _ => false

fun is_neg f = 
    case f of
        Conn("~",[f0]) => true
      | _ => false

fun is_eq f = 
    case f of Pred("=",true,[t1,t2]) => true
            | _ => false

fun is_forall f = 
    case f of 
        Quant("!",_,_,_) => true
      | _ => false


fun is_exists f = 
    case f of 
        Quant("?",_,_,_) => true
      | _ => false

fun is_uex f = 
    case f of 
        Quant("?!",_,_,_) => true
      | _ => false


fun is_quant f = 
    case f of 
        Quant _ => true
      | _ => false

fun is_var f = 
    case f of
        Pred(_,false,_) => true
      | _ => false

fun boundst t = 
    case view_term t of
        vVar(n,s) => boundss s
      | vB i => HOLset.add(HOLset.empty Int.compare,i)
      | vFun(f,s,tl) => HOLset.union(boundss s,bigunion Int.compare (List.map boundst tl))
and boundss s = 
    case dest_sort s of
        (_, tl) => bigunion Int.compare (List.map boundst tl)

(*Really need? tothink if do not allow var |-> bound matching makes everything safe.*)

val TRUE = Pred("T",true,[])

val FALSE = Pred("F",true,[])

fun mk_conn co fl = Conn(co,fl)

fun mk_neg f = Conn("~",[f])

fun mk_conj f1 f2 = Conn("&",[f1,f2])

fun mk_disj f1 f2 = Conn("|",[f1,f2])

fun mk_imp f1 f2 = Conn("==>",[f1,f2])

fun mk_dimp f1 f2 = Conn("<=>",[f1,f2])

fun mk_forall n s b = Quant("!",n,s,abstract (n,s) b)

fun mk_exists n s b = Quant("?",n,s,abstract (n,s) b)

fun mk_uex n s b = Quant("?!",n,s,abstract (n,s) b)

fun mk_quant q n s b = Quant(q,n,s,abstract (n,s) b)

fun mk_P0 p tl = Pred(p,true,tl)

fun mk_fvar f tl = Pred(f,false,tl)

(*destructor functions*)

fun dest_eq f = 
    case f of
        Pred("=",true,[t1,t2]) => (t1,t2)
      | _ => raise ERR ("not an equality: ",[],[],[f])

fun dest_imp f = 
    case f of 
        Conn("==>",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a implication: ",[],[],[f])

fun dest_neg f = 
    case f of
        Conn("~",[f0]) => f0
      | _ => raise ERR ("not a negation: ",[],[],[f])


fun dest_conj f = 
    case f of
        Conn("&",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a conjunction: ",[],[],[f])

fun dest_disj f = 
    case f of
        Conn("|",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a disjunction: ",[],[],[f])
 

fun dest_dimp f = 
    case f of 
        Conn("<=>",[L,R]) => (L,R)
      | _ => raise ERR ("not a double implication: ",[],[],[f])


fun dest_pred f = 
    case f of 
        Pred(p,true,l) => (p,l)
      | _ => raise ERR ("not a predicate: ",[],[],[f])

fun dest_exists f = 
    case f of 
        Quant("?",n,s,b) => 
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not an existantial: ",[],[],[f])


fun dest_f (Quant(q,n,s,b)) = 
let fun dest (f,i) =
    case f of
        Pred(P,bl,tl) => 
        Pred(P,bl,List.map (fn t => dest_t (n,s) (t,i)) tl)
      | Conn("~",[f0]) => 
        Conn("~",[dest (f0,i)])
      | Conn(co,[f1,f2]) => 
        Conn(co,[dest (f1,i),dest (f2,i)])
      | Quant(q0,n0,s0,b0) => Quant(q0,n0,s0,dest (subst_bound (mk_var(n,s)) b0,i+1))
      | _ => raise ERR ("dest.ill-formed formula",[],[],[])
in ((n,s),dest(b,0))
   handle CLASH =>
          let val (n1,s1) = 
                  dest_var (pvariantt (fvf b) (mk_var (n,s)))
          in dest_f (Quant(q,n1,s1,b))
          end
end
  | dest_f _ = raise ERR ("dest_f.not a quantification",[],[],[])


fun dest_uex f = 
    case f of 
        Quant("?!",n,s,b) =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not a unique existantial",[],[],[f])

fun dest_fvar f =
    case f of
        Pred(p,false,args)  => (p,args)
      | _ => raise ERR ("not a formula variable",[],[],[f])

fun eq_form fp = PolyML.pointerEq (fst fp,snd fp) orelse
    case fp of 
        (Pred(P1,b1,tl1),Pred(P2,b2,tl2)) => 
        P1 = P2 andalso b1 = b2 andalso List.all (fn (t1,t2) => t1 = t2) (zip tl1 tl2)
      | (Conn(co1,fl1),Conn(co2,fl2)) => co1 = co2 andalso 
                                         ListPair.all eq_form (fl1,fl2)
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        q1 = q2 andalso s1 = s2 andalso eq_form (b1,b2)
      | _ => false

fun eq_forml (l1:form list) (l2:form list) = 
    case (l1,l2) of 
        ([],[]) => true
      | (h1 :: t1, h2 :: t2) => eq_form(h1,h2) andalso eq_forml t1 t2
      | _  => false

fun fmem f fl = List.exists (curry eq_form f) fl

fun ril i l = 
    case l of [] => []
            | h :: t => 
              if eq_form(h,i) then t else h :: (ril i t)

(*compare functions which help produces HOLsets.*)

type fvd = (string,form)Binarymap.dict
type menv = vd * fvd

(*matching environment: records where are term variables and formula variables matched to*)

fun vd_of ((vd,fvd):menv) = vd

fun fvd_of ((vd,fvd):menv) = fvd

fun mk_menv tenv fenv :menv = (tenv,fenv)

val emptyfvd:fvd = Binarymap.mkDict String.compare

val mempty : menv = (emptyvd,emptyfvd)

fun fv2f fm f (fvd:fvd):fvd = Binarymap.insert(fvd,fm,f)

fun fv2f' fm f menv0: menv = mk_menv (vd_of menv0) (fv2f fm f (fvd_of menv0))
 
fun lookup_f (fvd:fvd) fm = Binarymap.peek (fvd,fm)

fun lookup_f' (menv:menv) fm = Binarymap.peek (fvd_of menv,fm)

fun mk_fenv l :fvd= 
    case l of 
        [] => emptyfvd
      | (n:string,f:form) :: l0 => Binarymap.insert(mk_fenv l0,n,f)

fun mk_inst tl fl = mk_menv (mk_tenv tl) (mk_fenv fl)

fun pmenv (env:menv) = (pvd (vd_of env),Binarymap.listItems (fvd_of env))

fun match_tl' nss l1 l2 env0 = 
    let val (vd0,fvd0) = (vd_of env0,fvd_of env0)
        val vd = match_tl nss l1 l2 vd0 
    in mk_menv vd fvd0
    end


fun match_sort' nss s1 s2 env0 = 
    let val (vd0,fvd0) = (vd_of env0,fvd_of env0)
        val vd = match_sort nss s1 s2 vd0 
    in mk_menv vd fvd0
    end



(*
testing match form:

val f1 = “P(a:set)”
val f2 = “P(Pow(a))”
match_form essps f1 f2 mempty

 <=> (?a:A->B.P(a)) ==> Q(b)
val f0 = “!a:A->B. P(a) ==> Q(b)”;

val f1 = “!a:A->B.(?a0 b.Holds(a,a0,b)) ==> Q(b)”;
match_form essps f0 f1 mempty

does inst_term coincide wth fVar_Inst1 for empty input fVars?

val f0 = “!a. P”;
val env0 = mk_inst [] [("P",“a = a”)] ;

fVar_Inst1 ("P",([],“a = a”)) f0

inst_form env0 f0 not coincide.

val f0 = “!c. !a.P(a,c)”
fVar_Inst1 ("P",([("a",set_sort)],“a = c”)) f0

fVar_Inst1 ("P",([("a",set_sort),("c",set_sort)],“a = c”)) f0

seems that fVar_Inst is wrong for empty case, it is just a constant lambda 


inst_form

P(a:mem(A),b:mem(B))

Q(c:mem(A),d:mem(B))

Q(c:mem(C),d:mem(D))

(*don;t do the inst above in this function, but need to call other functions to do the inst_sort first*)
*)

fun match_form nss ps pat cf env:menv = 
    case (pat,cf) of
        (Pred(P1,true,l1),Pred(P2,true,l2)) => 
        if P1 <> P2 then 
            raise ERR ("different predicates: ",[],[],[pat,cf])
        else match_tl' nss l1 l2 env
      | (Conn(co1,l1),Conn(co2,l2)) => 
        if co1 <> co2 then 
            raise ERR ("different connectives: ",[],[],[pat,cf])
        else match_fl nss ps l1 l2 env
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        if q1 <> q2 then 
            raise ERR ("different quantifiers: ",[],[],[pat,cf])
        else match_form nss ps b1 b2 (match_sort' nss s1 s2 env)
      | (Pred (fm,false,[]),_) => 
        if HOLset.member(ps,fm) then 
            if eq_form(pat,cf) then env
            else raise ERR ("match_form.current fvar is local constant",[],[],[pat])
        else
            (case (lookup_f' env fm) of
                 SOME f => if eq_form(f,cf) then env else
                           raise ERR ("double bind of formula variables",[],[],[pat,f,cf])
               | _ => fv2f' fm cf env)
 (*P(a) <=> Q(a) match to P(f(a)) gives a|-> f(a), obtains
 P(f(a)) <=> Q(f(a)), if in second clause ,match a to a, useless *)
      | (Pred(fm1,false,args1),cf) =>
        (case cf of 
            Pred(fm',false,args') =>
            if fm' = fm1 then match_tl' nss args1 args' env
            else raise ERR ("match_form.attempting match fvar with arguments to concrete formula, which is a formula variable",[],[],[pat])
          | _ => raise ERR ("match_form.attempting match fvar with arguments to concrete formula",[],[],[pat]))
      (*  else *)
 
        (*if HOLset.member(ps,fm1) then 
            case cf of 
                Pred(fm',false,args') =>
                if fm' = fm1 then match_tl' nss args1 args' env
                else raise ERR ("match_form.current fvar is local constant,attempted to match to other formula variable",[],[],[pat])
              | _ => raise ERR ("match_form.current fvar is local constant",[],[],[pat])
        else
        (case cf of 
            Pred(fm2,false,args2) => 
             if fm1 = fm2 then match_tl' nss args1 args2 env
             else env
            | _ => (*if length args1 = 1 andalso 
                      length (HOLset.listItems (fvf cf)) = 1
                   then 
                       match_tl' nss [(hd args1)] 
                                 [mk_var $ hd (HOLset.listItems (fvf cf))]    env
                   else  *)
raise ERR ("attempting to matching fvar with variables to some concrete formula",[],[],[]) (*env *)) *)
      | _ => raise ERR ("different formula constructors",[],[],[pat,cf])
and match_fl nss ps l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl nss ps t1 t2 (match_form nss ps h1 h2 env)
      | _ => raise simple_fail "incorrect length of list"


fun fVars f = 
    case f of
        Pred(P,false,args) => HOLset.add(HOLset.empty String.compare,P)
      | Conn("~",[f0]) => fVars f0
      | Conn(_,[f1,f2]) => HOLset.union(fVars f1,fVars f2)
      | Quant(_,_,_,b) => fVars b
      | Pred(_,true,_) => HOLset.empty String.compare
      |_ => raise ERR ("fVars.ill-formed formula",[],[],[f])

fun fVarsl fl = bigunion String.compare (List.map fVars fl)

(*
want 

(A & B ==> C) <=> (A ==> B ==> C)

Inj(f) & Surj(f) ==> Bij(f) rw into 

Inj(f) ==> Surj(f) ==> Bij(f)

P(a,b) <=> Q(a,b) cannot be auto matched to anything 

*)




(*
fun match_form nss ps pat cf env:menv = 
    case (view_term pat,view_term cf) of
        (vPred(P1,true,l1),vPred(P2,true,l2)) => 
        if P1 <> P2 then 
            raise ERR ("different predicates: ",[],[],[pat,cf])
        else match_tl' nss l1 l2 env
      | (vConn(co1,l1),vConn(co2,l2)) => 
        if co1 <> co2 then 
            raise ERR ("different connectives: ",[],[],[pat,cf])
        else match_fl nss ps l1 l2 env
      | (vQ(q1,n1,s1,b1),vQ(q2,n2,s2,b2)) => 
        if q1 <> q2 then 
            raise ERR ("different quantifiers: ",[],[],[pat,cf])
        else match_form nss ps b1 b2 (match_sort' nss s1 s2 env)
      | (Pred (fm,false,[]),_) => 
        if HOLset.member(ps,fm) then 
            if pat = cf then env
            else raise ERR ("match_form.current fvar is local constant",[],[],[pat,cf])
        else
            (case (lookup_f' env fm) of
                 SOME f => if eq_form(f,cf) then env else
                           raise ERR ("double bind of formula variables",[],[],[pat,f,cf])
               | _ => fv2f' fm cf env)
      | (Pred(fm1,false,args1),cf) => 
        if HOLset.member(ps,fm) then 
            if pat = cf then env
            else raise ERR ("match_form.current fvar is local constant",[],[],[pat,cf])
        else
            (case (lookup_f' env fm) of
                 SOME f => if eq_form(f,cf) then env else
                           raise ERR ("double bind of formula variables",[],[],[pat,f,cf])
               | _ => fv2f' fm cf env)

        (case cf of 
            Pred(fm2,false,args2) => 
             if fm1 = fm2 then match_tl' nss args1 args2 env
             else env
            | _ => if length args1 = 1 andalso 
                      length (HOLset.listItems (fvf cf)) = 1
                   then 
                       match_tl' nss [(hd args1)] 
                                 [mk_var $ hd (HOLset.listItems (fvf cf))]    env
                   else env) 
      | _ => raise ERR ("different formula constructors",[],[],[pat,cf])
and match_fl nss ps l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl nss ps t1 t2 (match_form nss ps h1 h2 env)
      | _ => raise simple_fail "incorrect length of list"

val pat = “(P & Q ==> R)”
val cf = mk_imp (mk_P0 "Inj" (mk_))
match_form 

*)

fun strip_forall f = 
    case f of 
        Quant("!",n,s,b) => 
        let 
            val (b1,l) = 
                strip_forall 
                    (subst_bound (pvariantt (fvf f) (mk_var(n,s))) b) in
            (b1,dest_var (pvariantt (fvf f) (mk_var(n,s))) :: l) end
      | _ => (f,[])


fun strip_forall0 f = 
    case f of 
        Quant("!",n,s,b) => 
        let 
            val (b1,l) = strip_forall0 b in
            (b1,dest_var (pvariantt (fvf f) (mk_var(n,s))) :: l) end
      | _ => (f,[])

fun strip_exists f = 
    case f of 
        Quant("?",n,s,b) => 
        let 
            val (b1,l) = 
                strip_exists 
                    (subst_bound (pvariantt (fvf f) (mk_var(n,s))) b) in
            (b1,dest_var (pvariantt (fvf f) (mk_var(n,s))) :: l) end
      | _ => (f,[])

fun strip_uex f = 
    case f of 
        Quant("?!",n,s,b) => 
        let 
            val (b1,l) = 
                strip_uex
                    (subst_bound (pvariantt (fvf f) (mk_var(n,s))) b) in
            (b1,dest_var (pvariantt (fvf f) (mk_var(n,s))) :: l) end
      | _ => (f,[])

fun strip_quants f = 
    case f of 
        Quant(q,_,_,_) => if q = "!" then strip_forall f 
                          else if q = "?" then strip_exists f 
                          else if q = "?!" then strip_uex f 
                          else raise ERR ("strip_quants.not a quantified formula",[],[],[f])
      | _ => raise ERR ("strip_quants.not a quantified formula",[],[],[f])

fun inst_term' env t = inst_term (vd_of env) t

fun inst_sort' env s = inst_sort (vd_of env) s

fun name_clash n env = 
    let
        val new_terms = List.map snd (pvd (vd_of env))
        val new_names = mapfilter (fst o dest_var) new_terms
    in 
        List.exists (fn n0 => n0 = n) new_names
    end
(*name clash does the same work 

        val new_terms = List.map snd (pvd (vd_of env))
        val new_names = mapfilter (fst o dest_var) new_terms
   
*)



(*
fun rename_once_need nl n = 
    if name_clash nl n = false then n else rename_once_need nl (n^"'") 
*)


(*

x |-> .....f(n)
y |-> ....g(n',j,k,l)

!n. P(n)




*)


fun inst_form env f = 
    case f of
        Pred(P,true,tl) => Pred(P,true,List.map (inst_term' env) tl)
      | Conn(co,fl) => Conn(co,List.map (inst_form env) fl)
      | Quant(q,n,s,b) => Quant(q,n,inst_sort' env s,inst_form env b)
      | Pred(f,false,tl) => 
        (case lookup_f' env f of
             SOME f' => inst_form env f'
           | NONE => Pred(f,false,List.map (inst_term' env) tl))
    


(*
fun inst_form env f = 
    let val new_terms = List.map snd (pvd (vd_of env))
        val new_names = mapfilter (fst o dest_var) new_terms
        fun recurse f =
            case f of
        Pred(P,true,tl) => Pred(P,true,List.map (inst_term' env) tl)
      | Conn(co,fl) => Conn(co,List.map recurse fl)
      | Quant(q,n,s,b) => 
        let 
            val s' = inst_sort' env s
            val b' = recurse b
            val n' = rename_once_need new_names n 
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


fun inst_form env f = 
    let val new_terms = List.map snd (pvd (vd_of env))
        val new_names = mapfilter (fst o dest_var) new_terms
        fun recurse f =
            case f of
        Pred(P,true,tl) => Pred(P,true,List.map (inst_term' env) tl)
      | Conn(co,fl) => Conn(co,List.map recurse fl)
      | Quant(q,n,s,b) => 
        let 
            val s' = inst_sort' env s
            val b' = recurse b
            val n' = rename_once_need new_names n 
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
*)


fun psymsf f = 
    case f of 
        Pred(p,true,_) => HOLset.add(HOLset.empty String.compare,p)
      | Conn("~",[A]) => psymsf A
      | Conn(_,[A,B]) => HOLset.union(psymsf A,psymsf B)
      | Quant(_,_,_,b) => psymsf b
      | _ => raise ERR ("psymsf.ill-formed formula: ",[],[],[f])

fun fsymsf f = 
    case f of 
        Pred(_,_,l) => 
        List.foldr 
            (fn (t,fs) => HOLset.union (fsymst t,fs))
            (HOLset.empty String.compare)
            l
      | Conn("~",[A]) => fsymsf A
      | Conn(_,[A,B]) => HOLset.union(fsymsf A,fsymsf B)
      | Quant(_,_,_,b) => fsymsf b
      | _ => raise ERR ("fsyms.ill-formed formula",[],[],[f])
     (* | _ => raise ERR ("fsymfs.ill-formed formula: ",[],[],[f])*)




fun ok_dpdc (env:menv) ((n:string,s),t) = 
    if sort_of t = inst_sort' env s then true else false
    

fun is_wfmenv menv = 
    let val pairs = pvd (vd_of menv)
    in List.all (ok_dpdc menv) pairs
    end

fun mk_pred0 p tl = Pred (p,true,tl)

fun mk_pred p tl = 
    case lookup_pred (!psyms) p of 
        NONE => raise ERR ("mk_pred.psym not found",[],tl,[]) 
      | SOME l => 
        let val _ = match_tl essps (List.map mk_var l) tl emptyvd
                    handle _ => raise ERR ("mk_pred.wrong input of predicate:" ^ p,List.map sort_of tl,tl,[])
        in Pred(p,true,tl)
        end



fun mk_eq t1 t2 =
    case (sort_of t1,sort_of t2) of 
        (s1,s2) =>
        if s1 = s2 then 
            if has_eq (sort_name s1) then mk_pred0 "=" [t1,t2]
            else
                raise ERR ("mk_eq.the sort: " ^ (sort_name s1) ^ 
                           " does not have equality, attempting to make equality on",[s1,s2],[t1,t2],[])
        else raise ERR ("mk_eq.sorts are not equal",[s1,s2],[t1,t2],[])


datatype form_view =
    vConn of string * form list
  | vQ of string * string * sort * form
  | vPred of string * bool * term list



local exception CLASH
in
fun dest_forall f = 
    let val vs = fvf f
    in
    case f of 
        Quant("!",n,s,b) =>
        (case HOLset.find (fn (n0,s0) => n0 = n) vs of 
             NONE =>((n,s),subst_bound (mk_var (n,s)) b)
           | SOME _ => raise CLASH)
        handle CLASH =>
        let val ns' = dest_var (pvariantt vs (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not a universal",[],[],[f])
    end
end



local 
(*
fun vreplacet (i,(n,s)) t = 
    case view_term t of 
        vVar(n0,s0) => if n0 = n then raise CLASH else 
                       replacet (i,mk_var(n,s)) t
      | vFun(f,s0,tl0) => 
        mk_fun f (List.map (vreplacet(i,(n,s))) tl0)
      | vB j => if i = j then mk_var(n,s) else t
and vreplaces (i,ns) s = 
    case view_sort s of 
        vSrt (name,tl) => 
        mk_sort name (List.map (vreplacet (i,ns)) tl)
*)
fun vsubst_bound ns =  
    let fun vsubst i (Pred(a,b,ts)) = 
            Pred(a, b,List.map (vreplacet (i, ns)) ts) 
          | vsubst i (Conn(b,As)) = Conn(b, List.map (vsubst i) As) 
          | vsubst i (Quant(q,n,s,b)) =
            Quant(q, n, vreplaces (i,ns) s, vsubst (i+1) b)
    in vsubst 0 end
in
fun dest_forall f = 
    (case f of 
        Quant("!",n,s,b) =>
        (((n,s),vsubst_bound (n,s) b)
        handle CLASH  =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',vsubst_bound ns' b)
        end)
      | _ => raise ERR ("not a universal",[],[],[f]))
end

(*think doing it the HOL way*)

fun view_form f =
    case f of
        Conn sfs => vConn sfs
      | Quant(q,n,s,b) => 
        let val (n',s') = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in vQ(q,n',s',subst_bound (mk_var (n',s')) b)
        end
      | Pred pi => vPred pi


fun dest_quant0 f = 
    case f of Quant Qi => Qi
        | _ => raise ERR ("dest_quant0.input is not quantified: ",[],[],[f])

fun dest_forall0 f =
    case dest_quant0 f of 
        ("!",n,s,f) => ((n,s),f)
      | _ => raise ERR ("dest_forall0.not a forall",[],[],[f])


fun dest_exists0 f =
    case dest_quant0 f of 
        ("?",n,s,f) => ((n,s),f)
      | _ => raise ERR ("dest_exists0.not a exists",[],[],[f])

fun dest_uex0 f =
    case dest_quant0 f of 
        ("?!",n,s,f) => ((n,s),f)
      | _ => raise ERR ("dest_uex0.not a unique exists",[],[],[f])


val _ = new_pred "T" [];
val _ = new_pred "F" [];





(*
fun fVar_Inst1 (pair as (P,(argl:(string * sort) list,Q))) f = 
    let val frees = fvf Q
    in
    case view_form f of
        vPred(P0,false,args0) =>
(*ListPair.map ListPair.foldl*)
(*mk_inst (zip argl args0)ListPair. [] *)
        if P0 = P then
            let val venv = match_tl essps (List.map mk_var argl) args0 emptyvd 
            in inst_form (mk_menv venv emptyfvd) Q
            end
(*if the number of arguments is wrong, or the sorts is wrong, then handle the matching exn by returning f *)
        else f
      | vConn(co,fl) => mk_conn co (List.map (fVar_Inst1 pair) fl)
      | vQ(q,n,s,b) => 
        (case HOLset.find (fn (n0,s0) => n0 = n) frees of 
            SOME _ => 
            (let val (n',s') = dest_var (pvariantt frees (mk_var(n,s)))
            in mk_quant q n' s' (fVar_Inst1 pair (substf ((n,s),mk_var(n',s'))b))
            end )
           |_ => mk_quant q n s (fVar_Inst1 pair b)) 
      | vPred (_,true,_) => f
    end
*)

end
