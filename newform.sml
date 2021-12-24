structure form :> form = 
struct
open term 

datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form
| fVar of string * term list;   

exception ERR of string * sort list * term list * form list

fun simple_fail s = ERR (s,[],[],[]) 

fun wrap_err s exn = 
    case exn of ERR (s0,sl,tl,fl) => ERR (s^s0,sl,tl,fl)
              | TER (s0,sl,tl) => ERR (s^s0,sl,tl,[])
              | _ => raise simple_fail s 


fun subst_bound t = 
    let fun subst i (Pred(a,ts)) = Pred(a, List.map (replacet (mk_bound i, t)) ts) 
          | subst i (Conn(b,As)) = Conn(b, List.map (subst i) As) 
          | subst i (Quant(q,n,s,b)) =
            Quant(q, n, replaces (mk_bound (i + 1),t) s, subst (i+1) b)
          | subst i (fVar(a,ts)) =  fVar(a, List.map (replacet (mk_bound i, t)) ts) 
    in subst 0 end


fun substf (V,t2) f = 
    case f of 
        Pred(P,tl) => Pred(P,List.map (substt (V,t2)) tl)
      | Conn(co,fl) => Conn(co,List.map (substf (V,t2)) fl)
      | Quant(q,n,s,b) => Quant(q,n,substs (V,t2) s,substf (V,t2) b)
      | fVar(P,tl) => fVar(P,List.map (substt (V,t2)) tl)

fun abstract t = 
    let fun abs i (Pred(a,ts)) = Pred(a, List.map (substt (t,mk_bound i)) ts) 
          | abs i (Conn(b,As)) = Conn(b, List.map (abs i) As) 
          | abs i (Quant(q,b,s,A)) = 
            Quant(q, b, substs (t, mk_bound (i + 1)) s, abs (i+1) A)
          | abs i (fVar(a,ts)) = fVar(a, List.map (substt (t,mk_bound i)) ts) 
    in abs 0 end;


fun fvf f = 
    case f of 
        Pred(P,tl) => fvtl tl
      | Conn(co,fl) => fvfl fl
      | Quant(q,n,s,b) => HOLset.union (fvs s,fvf b)
      | fVar(P,tl) => fvtl tl
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
    case f of Pred("=",[t1,t2]) => true
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
        fVar _ => true
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

val TRUE = Pred("T",[])

val FALSE = Pred("F",[])

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

fun mk_P0 p tl = Pred(p,tl)

fun mk_fvar f tl = fVar(f,tl)

(*destructor functions*)

fun dest_eq f = 
    case f of
        Pred("=",[t1,t2]) => (t1,t2)
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
        Pred(p,l) => (p,l)
      | _ => raise ERR ("not a predicate: ",[],[],[f])

fun dest_exists f = 
    case f of 
        Quant("?",n,s,b) => 
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not an existantial: ",[],[],[f])


fun dest_forall f = 
    case f of 
        Quant("!",n,s,b) =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not a universal",[],[],[f])

fun dest_uex f = 
    case f of 
        Quant("?!",n,s,b) =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not a unique existantial",[],[],[f])

fun dest_fvar f =
    case f of
        fVar pair => pair
      | _ => raise ERR ("not a formula variable",[],[],[f])

fun eq_form fp = PolyML.pointerEq (fst fp,snd fp) orelse
    case fp of 
        (Pred(P1,tl1),Pred(P2,tl2)) => 
        P1 = P2 andalso List.all (fn (t1,t2) => t1 = t2) (zip tl1 tl2)
      | (Conn(co1,fl1),Conn(co2,fl2)) => co1 = co2 andalso 
                                         ListPair.all eq_form (fl1,fl2)
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        q1 = q2 andalso s1 = s2 andalso eq_form (b1,b2)
      | (fVar fm1,fVar fm2)  => fm1 = fm2
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

fun match_fvar fv f l = 


fun match_form nss pat cf env:menv = 
    case (pat,cf) of
        (Pred(P1,l1),Pred(P2,l2)) => 
        if P1 <> P2 then 
            raise ERR ("different predicates: ",[],[],[pat,cf])
        else match_tl' nss l1 l2 env
      | (Conn(co1,l1),Conn(co2,l2)) => 
        if co1 <> co2 then 
            raise ERR ("different connectives: ",[],[],[pat,cf])
        else match_fl nss l1 l2 env
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        if q1 <> q2 then 
            raise ERR ("different quantifiers: ",[],[],[pat,cf])
        else match_form nss b1 b2 (match_sort' nss s1 s2 env)
      | (fVar (fm,[]),_) => 
            (case (lookup_f' env fm) of
                 SOME f => if eq_form(f,cf) then env else
                           raise ERR ("double bind of formula variables",[],[],[pat,f,cf])
               | _ => fv2f' fm cf env)
      | (fVar (fm,h :: t),_) => env
      | _ => raise ERR ("different formula constructors",[],[],[pat,cf])
and match_fl nss l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl nss t1 t2 (match_form nss h1 h2 env)
      | _ => raise simple_fail "incorrect length of list"


fun strip_forall f = 
    case f of 
        Quant("!",n,s,b) => 
        let 
            val (b1,l) = 
                strip_forall 
                    (subst_bound (pvariantt (fvf f) (mk_var(n,s))) b) in
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

fun rename_once_need n env = 
    if name_clash n env = false then n else rename_once_need (n^"'") env

fun inst_form env f = 
    case f of
        Pred(P,tl) => Pred(P,List.map (inst_term' env) tl)
      | Conn(co,fl) => Conn(co,List.map (inst_form env) fl)
      | Quant(q,n,s,b) => 
        let 
            val s' = inst_sort' env s
            val b' = inst_form env b
            val n' = rename_once_need n env 
        in 
            Quant(q,n',s',b')
        end
      | fVar(f,tl) => 
        (case lookup_f' env f of
             SOME f' => inst_form env f'
           | NONE => fVar(f,List.map (inst_term' env) tl))
    (*  | fVar fvn => 
        (case lookup_f' env fvn of
             SOME f' => f'
           | NONE => f)*)


fun psymsf f = 
    case f of 
        Pred(p,_) => HOLset.add(HOLset.empty String.compare,p)
      | Conn("~",[A]) => psymsf A
      | Conn(_,[A,B]) => HOLset.union(psymsf A,psymsf B)
      | Quant(_,_,_,b) => psymsf b
      | _ => raise ERR ("psymsf.ill-formed formula: ",[],[],[f])

fun fsymsf f = 
    case f of 
        Pred(_,l) => 
        List.foldr 
            (fn (t,fs) => HOLset.union (fsymst t,fs))
            (HOLset.empty String.compare)
            l
      | Conn("~",[A]) => fsymsf A
      | Conn(_,[A,B]) => HOLset.union(fsymsf A,fsymsf B)
      | Quant(_,_,_,b) => fsymsf b
      | fVar(_,l) => 
        List.foldr 
            (fn (t,fs) => HOLset.union (fsymst t,fs))
            (HOLset.empty String.compare)
            l
      | _ => raise ERR ("fsyms.ill-formed formula",[],[],[f])
     (* | _ => raise ERR ("fsymfs.ill-formed formula: ",[],[],[f])*)




fun ok_dpdc (env:menv) ((n:string,s),t) = 
    if sort_of t = inst_sort' env s then true else false
    

fun is_wfmenv menv = 
    let val pairs = pvd (vd_of menv)
    in List.all (ok_dpdc menv) pairs
    end

fun mk_pred0 p tl = Pred (p,tl)

fun mk_pred p tl = 
    case lookup_pred (!psyms) p of 
        NONE => raise ERR ("mk_pred.psym not found",[],tl,[]) 
      | SOME l => 
        let val _ = match_tl essps (List.map mk_var l) tl emptyvd
                    handle _ => raise ERR ("mk_pred.wrong input of predicate:" ^ p,List.map sort_of tl,tl,[])
        in Pred(p,tl)
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
  | vPred of string * term list
  | vfVar of string * term list


fun dest_forall f = 
    case f of 
        Quant("!",n,s,b) =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not a universal",[],[],[f])

fun view_form f =
    case f of
        Conn sfs => vConn sfs
      | Quant(q,n,s,b) => 
        let val (n',s') = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in vQ(q,n',s',subst_bound (mk_var (n',s')) b)
        end
      | Pred pi => vPred pi
      | fVar f => vfVar f

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



end
