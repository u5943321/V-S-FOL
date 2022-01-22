structure term :> term = 
struct

datatype sort = srt of string * term list 
and term =
    Var of string * sort
    | Bound of int
    | Fun of string * sort * term list;

exception TER of string * sort list * term list

exception CLASH

fun mk_sort str tl = srt (str,tl)

(*Any point of not put the line about in the sig?*)

val sorts0:(string, (string * sort) list) Binarymap.dict =
    Binarymap.mkDict String.compare 

val SortDB = ref sorts0

fun new_sort sn depends = 
    SortDB := Binarymap.insert(!SortDB,sn,depends)

fun on_ground st = 
    case Binarymap.peek(!SortDB,st) of 
        SOME tl0 => if tl0 = [] then true else false
      | NONE => raise TER ("no sort with name: " ^ st,[],[])

fun listof_sorts (srts: (string, (string * sort) list) Binarymap.dict) = Binarymap.listItems srts

fun ground_sorts srts = 
    List.filter on_ground $ List.map fst (listof_sorts srts)

val sort_infixes0: (string,string)Binarymap.dict = 
    Binarymap.mkDict String.compare

val SortInx = ref sort_infixes0

fun new_sort_infix st symbol = 
    SortInx := Binarymap.insert(!SortInx,symbol,st)

fun sortname_of_infix syb =
    case Binarymap.peek(!SortInx,syb) of 
        SOME sn => sn
      | _ => raise TER ("sortname_of_infix.no sort with infix symbol: " ^ syb,[],[])


datatype term_view =
    vVar of string * sort
  | vB of int 
  | vFun of string * sort * term list

datatype sort_view = 
         vSrt of string * term list

fun view_term t = 
    case t of
        Var v => vVar v
      | Bound i => vB i (*raise ERR instead, user cannot see it!*)
      | Fun sst => vFun sst

fun view_sort s = 
    case s of 
      srt (str,tl) => vSrt (str,tl)

fun dest_sort s = 
    case s of srt (str,tl) => (str,tl)



fun wrap_ter s sl tl e = case e of TER (s0,sl0,tl0) => TER (s ^ s0,sl @ sl0,tl @ tl0)
                           | _ => e

fun sort_of t = 
    case t of Var (_,s) => s
            | Fun (_,s,_) => s 
            | Bound i => srt ("Bd",[])

fun is_var t = 
    case t of Var _ => true | _ => false

fun is_fun t = 
    case t of Fun _ => true | _ => false

fun is_bound t = 
    case t of Bound _ => true | _ => false

fun sort_name st = fst $ dest_sort st

fun depends_on st = snd $ dest_sort st

fun of_sort str t = 
    if sort_name (sort_of t) = str then true else false

fun dest_var t = 
    case t of Var(n,s) => (n,s)
            | _ => raise TER ("not a variable: ",[],[t])

fun dest_fun t = 
    case  t of 
        Fun(n,s,l) => (n,s,l)
      | _ => raise TER ("not a function: ",[],[t])

fun mk_var (name,st) = Var(name,st)

fun mk_fun0 f s l = Fun(f,s,l)

fun mk_bound i = Bound i

fun mk_const0 n s = mk_fun0 n s []


fun srt2ns st = 
    let val tl = 
            case Binarymap.peek(!SortDB,st) of 
                SOME tl0 => tl0
              | NONE => raise TER ("no sort with name: "^ st,[],[])
    in (st ^ Int.toString 0,mk_sort st $ List.map mk_var tl)
    end


fun replacet (i,new) t = 
    if t=Bound i then new else 
    case t 
     of Fun(f,s,tl) => 
        Fun(f,replaces (i,new) s, List.map (replacet(i,new)) tl) 
      | Var(n,s) => Var(n,replaces (i,new) s)
      | _ => t
(*      | _ => t *)
and replaces (i,new) s = 
    case s of 
        srt (name,tl) => srt (name, List.map (replacet (i,new)) tl)

fun vreplacet (i,(n,s)) t = 
    case t of 
        Var(n0,s0) => if n0 = n then raise CLASH else 
                       Var(n0,vreplaces (i,(n,s)) s0)
      | Fun(f,s0,tl0) => 
        Fun(f,vreplaces(i,(n,s)) s0,
            List.map (vreplacet(i,(n,s))) tl0)
      | Bound j => if i = j then mk_var(n,s) else t
and vreplaces (i,ns) s = 
    case s of 
        srt (name,tl) => 
        srt (name,List.map (vreplacet (i,ns)) tl)

fun eq_term (t1,t2) = 
    case (t1,t2) of 
        (Var(n1,s1),Var(n2,s2)) => 
        n1 = n2 andalso eq_sort(s1,s2)
      | (Fun(f1,s1,l1),Fun(f2,s2,l2)) =>
        f1 = f2 andalso eq_sort(s1,s2) andalso
        List.all eq_term (zip l1 l2)
      | (Bound i1,Bound i2) => i1 = i2
      | _ => false
and eq_sort (s1,s2) = 
    case (s1,s2) of 
        (srt (sn1,tl1),srt (sn2,tl2)) => 
        if sn1 = sn2 andalso
           List.all eq_term (zip tl1 tl2) then true 
        else false




fun substt (V as (m,s:sort),t2) t = 
    case view_term t of
        vVar(n,s') => 
        if m = n andalso (* eq_sort(s,s')*) s = s' then t2 
        else mk_var (n,substs (V,t2) s')
      | vFun(f,s',tl) => mk_fun0 f (substs (V,t2) s') (List.map (substt (V,t2)) tl)
      | _ => t
and substs (V,t2) s = 
    case view_sort s of 
        vSrt (sn,tl) =>
        mk_sort sn (List.map (substt (V,t2)) tl)

fun pair_compare ac bc ((a1,b1),(a2,b2)) = 
    case (ac (a1,a2)) of 
        EQUAL => bc (b1,b2)
      | x => x


fun inv_image_compare f c (x,y) = 
    c (f x, f y)

fun list_compare c (l1,l2) = 
    case (l1,l2) of
        ([],[]) => EQUAL
      | (h1 :: t1, h2 :: t2) => pair_compare c (list_compare c)
                                             ((h1,t1),(h2,t2))
      | ([],_) => LESS
      | (_,[]) => GREATER


fun sort_compare (s1,s2) = 
    if PolyML.pointerEq(s1,s2) then EQUAL else
    case (dest_sort s1,dest_sort s2) of 
        ((sn1,tl1),(sn2,tl2)) =>
        (case String.compare (sn1,sn2) of 
             EQUAL =>
             list_compare term_compare (tl1,tl2) 
           | x =>x)
and term_compare (t1,t2) = 
    if PolyML.pointerEq(t1,t2) then EQUAL else
    case (t1,t2) of 
        (Var ns1,Var ns2) => pair_compare String.compare sort_compare (ns1,ns2)
     | (Var _ , _) => LESS
     | (_,Var _) => GREATER
     | (Bound i1, Bound i2) => Int.compare (i1,i2)
     | (Bound _ , _) => LESS
     | (_, Bound _) => GREATER
     | (Fun fsl1, Fun fsl2) => 
       inv_image_compare (fn (a,b,c) => (a,(b,c))) 
                         (pair_compare String.compare 
                                       (pair_compare sort_compare 
                                                     (list_compare term_compare))) 
                         (fsl1,fsl2)  

val var_ord = (pair_compare String.compare sort_compare)

fun var_ord1 ((n1,s1),(n2,s2)) =
    case String.compare(n1,n2) of 
        EQUAL => sort_compare (s1,s2)
      | x => x

fun sort_cpr (s1,s2) = 
    if PolyML.pointerEq(s1,s2) then EQUAL else
    case (dest_sort s1,dest_sort s2) of 
        ((sn1,tl1),(sn2,tl2)) =>
        (case String.compare (sn1,sn2) of 
             EQUAL =>
             list_compare term_cpr (tl1,tl2) 
           | x => x)
and term_cpr (t1,t2) = 
    if PolyML.pointerEq(t1,t2) then EQUAL else
    case (t1,t2) of 
        (Var (ns1 as (n1,s1)),Var (ns2 as (n2,s2))) =>  
        (case String.compare(n1,n2) of 
            EQUAL => sort_compare (s1,s2)
          | x => x)
     | (Var _ , _) => LESS
     | (_,Var _) => GREATER
     | (Bound i1, Bound i2) => Int.compare (i1,i2)
     | (Bound _ , _) => LESS
     | (_, Bound _) => GREATER
     | (Fun(fsl1 as (f1,s1,l1)), Fun (fsl2 as (f2,s2,l2))) => 
       (case String.compare(f1,f2) of 
           EQUAL => 
           (case sort_cpr(s1,s2) of 
                EQUAL => list_compare term_cpr (l1,l2)
              | x => x)
         | x => x)

val term_compare = term_cpr;
val sort_compare = sort_cpr;




(*empty string-sort-pair set*)
val essps = HOLset.empty var_ord

type vd = ((string * sort),term)Binarymap.dict

fun pvd vd = Binarymap.listItems vd

val emptyvd:vd = Binarymap.mkDict (pair_compare String.compare sort_compare)

fun mk_tenv l = 
    case l of 
        [] => emptyvd
      | ((n,s),t) :: l0 => Binarymap.insert(mk_tenv l0,(n,s),t)

fun v2t (V:string * sort) (t:term) (vd:vd):vd = Binarymap.insert(vd,V,t)

fun lookup_t (vd:vd) V = Binarymap.peek (vd,V)

fun has_bound_t t = 
    case view_term t of 
        vVar (n,s) => has_bound_s s
      | vB _ => true
      | vFun (f,s,tl) => 
        List.exists has_bound_t tl orelse 
        has_bound_s s
and has_bound_s s = 
    case dest_sort s of
        (_,tl) => List.exists has_bound_t tl

        
fun match_term nss pat ct (env:vd) = 
    case (view_term pat,view_term ct) of 
        (vFun(f1,s1,l1),vFun(f2,s2,l2)) => 
        if f1 <> f2 then 
            raise TER("match_term.different function names: ",[],[pat,ct])
        else (match_sort nss s1 s2 (match_tl nss l1 l2 env)  
             handle e => raise wrap_ter "match_term." [s1,s2] [pat,ct] e)
      | (vVar(n1,s1),_) => 
        (*make sure that _ ct cannot include a bound variable*)
        if has_bound_t ct then 
            raise TER ("match_term.attempting matching to a term with bounded variable",[],[]) 
        else  
        if HOLset.member(nss,(n1,s1)) then
            if pat = ct then env 
            else raise TER ("match_term.current term is local constant: ",[],[pat,ct])
        else 
            (case (lookup_t env (n1,s1)) of
                 SOME t => if t = ct then env else
                           raise TER ("match_term.double bind: ",[],[pat,t,ct])
               | _ => 
                 v2t (n1,s1) ct (match_sort nss s1 (sort_of ct) env)
                 handle e => raise wrap_ter "match_term." [] [pat,ct] e)
      | (vB i1,vB i2) => 
        if i1 <> i2 then 
            raise TER ("match_term.bound variables have different levels: ",[],[pat,ct])
        else env
      | _ => raise Fail "match_term.unexpected term constructor"
and match_sort nss sp cs env = 
    case (dest_sort sp,dest_sort cs) of 
        ((sn1,tl1),(sn2,tl2)) =>
        if sn1 = sn2 then
            match_tl nss tl1 tl2 env
        else raise TER ("match_sort.attempting matching two different sorts: "^ sn1 ^ " , " ^ sn2,[sp,cs],[])
and match_tl nss l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_tl nss t1 t2 (match_term nss h1 h2 env)
      | _ => raise TER ("match_sort.incorrect length of list",[],[])



fun inst_term (env:vd) t = 
    case view_term t of 
        vVar(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => mk_var (n,inst_sort env s))
      | vFun(f,s,tl) => mk_fun0 f (inst_sort env s) (List.map (inst_term env) tl)
      | _ => t
and inst_sort env s = 
    case (dest_sort s) of
        (sn,tl) => 
        mk_sort sn (List.map (inst_term env) tl)


fun pvariantt vd t = 
    case t of 
        Var(n,s) => 
        if mem n (List.map fst (HOLset.listItems vd))
        then pvariantt vd (Var(n ^ "'",s))
        else Var (n, s)
      | Fun(f,s,l) => Fun(f,s,List.map (pvariantt vd) l)
      | _ => t

fun bigunion ord setl = 
    case setl of [] => HOLset.empty ord
               | h :: t => HOLset.union(h,bigunion ord t)

fun var_bigunion setl =
    case setl of
        [] => essps
      | h :: t => HOLset.union(h,var_bigunion t)

fun fsymss s = 
    case dest_sort s of
        (_, tl) =>
        bigunion String.compare (List.map fsymst tl)
and fsymst t = 
    case t of
        Var(n,s) => fsymss s
      | Fun(_,s,l) => 
        let val argfs = List.foldr 
                            (fn (t,fs) => HOLset.union (fsymst t,fs))
                            (HOLset.empty String.compare)
                            l
        in HOLset.union(argfs,fsymss s)
        end
      | _ => HOLset.empty String.compare


fun fvt t = 
    case t of 
        Var(n,s) => HOLset.add (fvs s,(n,s)) 
      | Bound i => essps
      | Fun(f,s,tl) => 
        (case tl of 
             [] => essps
           | h :: t => HOLset.union 
                           (HOLset.union ((fvt h),(fvs s)), 
                            fvtl t))
and fvs s = 
    case dest_sort s of 
        (sn,tl) => fvtl tl
and fvtl tl = var_bigunion (List.map fvt tl)


fun fvta a t = 
    case t of 
        Var(p as (n,s)) => fvsa (HOLset.add(a,p)) s
      | Bound _ => a 
      | Fun(f,s,tl) => fvtla (fvsa a s) tl
and fvtla a [] = a
  | fvtla a (t :: ts) = fvtla (fvta a t) ts
and fvsa a (srt(sname,ts)) = 
    fvtla a ts

val fvt = fvta essps

val fvtl = fvtla essps

val fvs = fvsa essps

(*
fun fvt a 


*)


fun fxty i = 
    case i of 
       "<=>" => 100
      | "==>" => 200
      | "|" => 300
      | "&" => 400
      | "=" => 450
      | "==" => 450
      | "o" => 455
      | "@" => 455
      | ":" => 460 (*900*)
      | "->" => 470 (*900*)
      | "~>" => 470 
      | "+" => 500
      | "*" => 600
      | "^" => 700
      | "~" => 900
      | _ => ~1

val eqsorts0: string list = [] 

val EqSorts = ref eqsorts0

fun has_eq sn = mem sn (!EqSorts)


type fsymd = (string, sort * ((string * sort) list)) Binarymap.dict

type psymd = (string, (string * sort) list) Binarymap.dict

fun lookup_pred (pd:psymd) p = Binarymap.peek (pd,p)

fun lookup_fun (fd:fsymd) f = Binarymap.peek (fd,f)


val psyms0:psymd = Binarymap.mkDict String.compare

val fsyms0:fsymd = Binarymap.mkDict String.compare

val fsyms = ref fsyms0
val psyms = ref psyms0


fun mk_fun f tl = 
    case lookup_fun (!fsyms) f of 
        NONE => raise TER ("mk_fun.function: " ^ f ^ " not found",[],tl)
      | SOME(s,l) => 
        let val vd = (match_tl essps (List.map mk_var l) tl emptyvd)
            val s' = inst_sort vd s
        in mk_fun0 f s' tl
        end

fun is_fun sr = 
    case (Binarymap.peek (!fsyms,sr)) of 
        SOME _ => true
      | _ => false

fun is_pred sr =
    case (Binarymap.peek (!psyms,sr)) of
        SOME _ => true
      | _ => false

fun is_const sr = 
    case (Binarymap.peek (!fsyms,sr)) of 
        SOME (_,l) => if length l = 0 then true else false
      | _ => false


fun new_pred p tl = psyms := Binarymap.insert (!psyms,p,tl)

fun new_fun f (s,tl) = fsyms := Binarymap.insert (!fsyms,f,(s,tl))


fun ill_formed_fv (n,s) = 
    case dest_sort s of (_,tl) => 
                        List.exists is_bound tl

val abbrdict0: 
 (string * (term list), string * (term list)) Binarymap.dict = Binarymap.mkDict (pair_compare String.compare (list_compare term_compare))

val abbrdict = ref abbrdict0

val unabbrdict0: (string * (term list), string * (term list)) Binarymap.dict = Binarymap.mkDict (pair_compare String.compare (list_compare term_compare))

val unabbrdict = ref unabbrdict0

(*cannot use 
f (abf,tl1,tl2)

since then cannot capture abbrev such as Exp(X,2) as Pow 

or handle error once the matching fails.

*)

fun new_abbr (f,tl) (abf,tl') =
    let 
        val _ = abbrdict :=
                Binarymap.insert(!abbrdict,(f,tl),(abf,tl'))
        val _ = unabbrdict := 
                Binarymap.insert(!unabbrdict,(abf,tl'),(f,tl))
in () end



(*should we check that they are already registered as function symbols yet before inserting them into the dict?*)


(*
“!f:2 ->A. T”
val _ = new_fun "2" (ob_sort,[])

val _ = new_abbr ("+",[rastt "1",rastt "1"]) ("2",[]) 


val _ = new_fun "Pow" (ob_sort,[("X",ob_sort)])

"Pow" ("Exp",[rastt "X"],[rastt "X",rastt "1 * 1"])

val _ = new_abbr ("Exp",[rastt "X",rastt "1 + 1"]) ("Pow",[rastt "X"]) 

 "Exp" ("Pow",[rastt "X",rastt "1+1"],[rastt "X"])
*)


fun dest_t (n,s) (t,i) = 
    case t of 
        Bound j => if i = j then mk_var(n,s) else t
      | Var(m,st) => if n = m then raise CLASH 
                     else Var(m,dest_s (n,s) (st,i))
      | Fun(f,st,tl) => Fun(f,dest_s (n,s) (st,i),
                            List.map (fn t => dest_t (n,s) (t,i)) tl)
and dest_s (n,s) (st,i) = 
    case st of
        srt(sname,tl) => 
        srt(sname,List.map (fn t => dest_t (n,s) (t,i)) tl)



(*

P(a,b)

match to 

!A B a:mem(A) b:mem(B). P(a,b) <=> R(a,b)
 
    P(B(1),B(0))
sorts are rev [set_sort,set_sort,mem_sort (B(1)),mem_sort (B(1))]

match a |-> B(1) b |-> B(0) 

try to match 

P(x1:mem(X),x2:mem(X)) <=> Q(x1,x2)

want the form after inst to be

Q(B(0),B(1))


P(x1:mem(X1),x2:mem(X2)) <=> Q(x1,x2)

Still Q(B(0),B(1))

but if P(x1:mem(X1),x2:mem(X1)) <=> Q(x1,x2)

and 

!A B a1:mem(A) a2:mem(B). P(a1:mem(B(1)),a2:mem(B(1))) <=> R(a1,a2)

then raise err. since X1 is double bind, to B(1) and ..

match x2 |-> B(0), need to match sort accordingly, dict tells that 

[mem_sort 1,mem_sort 1,set_sort,set_sort] is the list of bounded sorts from

B(0),so B(0), which is the head, has sort mem_sort 1,
then match X1 |-> B(1), 

when matching x1 |-> B(1), need to match sort accordingly, dict tells that

[mem_sort 1,mem_sort 1,set_sort,set_sort] 

so the sort of B(1) is the snd entry, mem_sort 1 the sort need to change 



match x1 |-> B(1), search for the match of X1, 

the dict says [set_sort,set_sort,mem_sort 1,mem_sort 1]

[mem_sort 1,mem_sort 1,set_sort,set_sort]

the (1 + 1) = 2nd entry has sort mem_sort 1, so
match X1 to B(1).

when matching B(0),






!A a1:mem(A) a2:mem(A). P(a1:mem(B(0)),a2:mem(B(1))) <=> R(a1,a2)

*)

fun recover_s i (srt (sname,tl)) = 
    srt (sname,List.map (recover_t i) tl)
and recover_t i t = 
    case t of 
        Var(n,s) => Var(n,recover_s i s)
      | Fun(f,s,l) => Fun(f,recover_s i s, List.map (recover_t i) l)
      | Bound j => Bound (i + j)




fun shift_vd_eval i vd ns = 
    case Binarymap.peek(vd,ns) of 
        SOME t => recover_t i t
      | _ => raise TER ("shift_vd_eval.no value stored for that key",[],[])

fun shift_vd i vd = 
    Binarymap.foldl 
        (fn (ns,t,d) => Binarymap.insert(d,ns,recover_t i t)) vd vd







fun pmatch_t bs nss pat ct (env:vd) = 
    case (pat,ct) of 
        (Fun(f1,s1,l1),Fun(f2,s2,l2)) => 
        if f1 <> f2 then 
            raise TER("match_term.different function names: ",[],[pat,ct])
        else (pmatch_s bs nss s1 s2 (pmatch_tl bs nss l1 l2 env)  
             handle e => raise wrap_ter "pmatch_term." [s1,s2] [pat,ct] e)
      | (Var(n1,s1),Bound i) =>
        let val s2 = el (i + 1) bs
            val s2from0 = recover_s i s2
            val vd1 = pmatch_s bs nss s1 s2from0 (env:vd) 
        in v2t (n1,s1) ct vd1
        end
      | (Var(n1,s1),_) => 
        if HOLset.member(nss,(n1,s1)) then
            if pat = ct then env 
            else raise TER ("match_term.current term is local constant: ",[],[pat,ct])
        else 
            (case (lookup_t env (n1,s1)) of
                 SOME t => if t = ct then env else
                           raise TER ("pmatch_t.double bind: ",[],[pat,t,ct])
               | _ => 
                 v2t (n1,s1) ct (pmatch_s bs nss s1 (sort_of ct) env)
                 handle e => raise wrap_ter "pmatch_t." [] [pat,ct] e)
      | (Bound i1,Bound i2) => 
        if i1 <> i2 then 
            raise TER ("pmatch_t.bound variables have different levels: ",[],[pat,ct])
        else env
      | _ => raise Fail "pmatch_t.unexpected term constructor"
and pmatch_s bs nss sp cs env = 
    case (dest_sort sp,dest_sort cs) of 
        ((sn1,tl1),(sn2,tl2)) =>
        if sn1 = sn2 then
            pmatch_tl bs nss tl1 tl2 env
        else raise TER ("match_sort.attempting matching two different sorts: "^ sn1 ^ " , " ^ sn2,[sp,cs],[])
and pmatch_tl bs nss l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        pmatch_tl bs nss t1 t2 (pmatch_t bs nss h1 h2 env)
      | _ => raise TER ("match_sort.incorrect length of list",[],[])



fun pinst_t (env:vd) t = 
    case  t of 
        Var(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => Var(n,pinst_s env s))
      | Fun(f,s,tl) => 
        Fun(f,pinst_s env s,List.map (pinst_t env) tl)
      | _ => t
and pinst_s env s = 
    case (dest_sort s) of
        (sn,tl) => 
        srt(sn,List.map (pinst_t env) tl)





end
