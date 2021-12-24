structure term :> term = 
struct

datatype sort = srt of string * term list 
and term =
    Var of string * sort
    | Bound of int
    | Fun of string * sort * term list;

exception TER of string * sort list * term list

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


fun replacet (u,new) t = 
    if t=u then new else 
    case t 
     of Fun(f,s,tl) => 
        Fun(f,replaces (u,new) s, List.map (replacet(u,new)) tl) 
      | _=> t
and replaces (u,new) s = 
    case s of 
        srt (name,tl) => srt (name, List.map (replacet (u,new)) tl)

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


fun fxty i = 
    case i of 
       "<=>" => 100
      | "==>" => 200
      | "|" => 300
      | "&" => 400
      | "=" => 450
      | "==" => 450
      | "o" => 455
      | ":" => 460 (*900*)
      | "->" => 470 (*900*)
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

end
