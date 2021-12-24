structure parser :> parser = 
struct
open token pterm_dtype term form 

exception PER of (string * psort list * pterm list)

fun mk_pQuant q n ps pf = pQuant (q,n,ps,pf)

fun mk_pConn co pf1 pf2 = pConn(co,[pf1,pf2])

fun mk_pNeg pf = pConn("~",[pf])

fun mk_pPred P ptl = pPred(P,ptl)

fun mk_pfVar P ptl = pfVar(P,ptl)

structure Env = 
struct
open Binarymap List
type env = (string,pterm)Binarymap.dict * (string,psort)Binarymap.dict * 
           (string,psort)Binarymap.dict * (string,psort)Binarymap.dict * int


(*components:
  1. records where does the ptUVars go to, 
  2. records where does the psvar goes to,
  3. records how names obtained by parsing is associated to a psvar.
  4. records the sort of ptUVars  *)
val empty : env = (Binarymap.mkDict String.compare, 
                   Binarymap.mkDict String.compare,
                   Binarymap.mkDict String.compare,
                   Binarymap.mkDict String.compare,
                   0)

fun insert_ps n s ((dpt,dps,dv,dus,i):env):env = (dpt,insert (dps,n,s),dv,dus,i)
    
fun insert_pt n t ((dpt,dps,dv,dus,i):env):env = (insert (dpt,n,t),dps,dv,dus,i)

fun insert_us Av s ((dpt,dps,dv,dus,i):env):env = (dpt,dps,dv,insert (dus,Av,s),i)

fun dps_of ((dpt,dps,dv,dus,i):env) = dps

fun dpt_of ((dpt,dps,dv,dus,i):env) = dpt

fun dv_of ((dpt,dps,dv,dus,i):env) = dv

fun dus_of ((dpt,dps,dv,dus,i):env) = dus

fun var_of ((dpt,dps,dv,dus,i):env) = i

fun fresh_var ((td,sd,dv,dus,i):env):string * env = (" " ^ Int.toString i,(td,sd,dv,dus,i + 1))

fun lookup_pt ((dpt,_,_,_,_):env) n = peek (dpt,n)

fun lookup_ps ((_,dps,_,_,_):env) n = peek (dps,n)

fun lookup_us ((_,_,_,dus,_):env) n = peek (dus,n)

fun ps_of ((_,_,dv,_,_):env) n:psort option = peek (dv,n)

fun record_ps n s ((dpt,dps,dv,dus,i):env):env = (dpt,dps,insert (dv,n,s),dus,i)

fun clear_ps n ((dpt,dps,dv,dus,i):env):env = 
    case ps_of (dpt,dps,dv,dus,i) n of
        SOME ps => 
        let val (dv1,_) = remove(dv, n) in (dpt,dps,dv1,dus,i) end
      | NONE => (dpt,dps,dv,dus,i)

fun clear_psn n ((dpt,dps,dv,dus,i):env):env = 
    case lookup_ps (dpt,dps,dv,dus,i) n of 
        SOME ps => 
        let val (dps1,_) = remove(dps, n) in (dpt,dps1,dv,dus,i) end
      | NONE => (dpt,dps,dv,dus,i)
end

open Binarymap List Env;

fun enclose a = "(" ^ a ^ ")";

fun conc_list sep l = 
    case l of 
        [] => ""
      | h :: t => sep ^ h ^ conc_list sep t

fun conc_list1 sep l = 
    case l of [] => ""
            | h :: t => h  ^ (conc_list sep t);


fun stringof_pt pt = 
    case pt of 
        pVar (name,ps) => "pv" ^ " " ^ name ^ " : " ^ stringof_ps ps
      | ptUVar a => "ptu" ^ " " ^ a
      | pFun (f,ps,l) => f ^ " " ^ (stringof_ps ps) ^ stringof_args l 
      | pAnno (pt,ps) => enclose (stringof_pt pt ^ "," ^ stringof_ps ps)
and stringof_args [] = ""
  | stringof_args ts = enclose (conc_list1 "," (List.map stringof_pt ts))
and stringof_ps ps = 
    case ps of 
        psvar name => "psv" ^ " " ^ name 
      | psrt (sn,ptl) => sn ^ (stringof_args ptl)

fun psdict (dict:(string,psort) Binarymap.dict) =  Binarymap.foldl (fn (k,v,A) => ("(" ^ k ^ " -> " ^ stringof_ps v ^ ")") :: A) [] dict

fun ptdict (dict:(string,pterm) Binarymap.dict) =  Binarymap.foldl (fn (k,v,A) => ("(" ^ k ^ " -> " ^ stringof_pt v ^ ")") :: A) [] dict

fun pdv (dict:(string,psort) Binarymap.dict) =  Binarymap.foldl (fn (k,v,A) => ("(" ^ k ^ " -> " ^ stringof_ps v ^ ")") :: A) [] dict

fun pdus (dict:(string,psort) Binarymap.dict) =  Binarymap.foldl (fn (k,v,A) => ("(" ^ k ^ " -> " ^ stringof_ps v ^ ")") :: A) [] dict


fun pdict env = (ptdict (dpt_of env),psdict (dps_of env),pdv (dv_of env),pdus (dus_of env),
                var_of env)

fun occs_ps psname env ps = 
    case ps of
        psrt (sn,ptl) =>
        List.exists (occs_pt psname env) ptl
      | psvar s => 
        psname = s orelse 
        (case lookup_ps env s of 
             SOME ps' => occs_ps psname env ps'
           | NONE => false)                       
and occs_pt ptname env pt = 
    case pt of 
        ptUVar n => (case lookup_pt env n of 
                         SOME pt' => occs_pt ptname env pt'
                       | NONE => false)
      | pAnno (pt,ps) => occs_pt ptname env pt orelse  
                         occs_ps ptname env ps
      | pVar (n,ps) => occs_ps ptname env ps
      | pFun (f,ps,l) => exists (occs_pt ptname env) l orelse
                         occs_ps ptname env ps  


fun chasevart pt env = 
    case pt of 
        ptUVar s => (case lookup_pt env s of
                         SOME pt' =>  chasevart pt' env
                       | NONE => pt)
      | _ => pt 
    
fun chasevars ps env = 
    case ps of 
        psvar s => (case lookup_ps env s of
                         SOME ps' =>  chasevars ps' env
                       | NONE => ps)
      | _ => ps

fun term_from_pt env pt = 
    let val sn = hd (ground_sorts (!SortDB))
    in
    if on_ground sn then
        case (chasevart pt env) of 
            ptUVar n =>
            let 
                val s = 
                    case (lookup_us env n) of
                        SOME ps => sort_from_ps env ps 
                      | NONE => mk_sort sn []
            in mk_var(n,s)
            end
          | pVar(n,ps) => mk_var (n,sort_from_ps env ps) 
          | pFun(f,ps,ptl) => 
            mk_fun f (List.map (term_from_pt env) ptl)
          | pAnno(pt,ps) => term_from_pt env pt
    else 
        raise
            simple_fail 
            ("term_from_pt.input sort: " ^ sn ^ " not on ground")
    end
and sort_from_ps env ps = 
    let val sn = hd (ground_sorts (!SortDB))
    in
    if on_ground sn then
        case (chasevars ps env) of
            psvar n =>  mk_sort sn []
          | psrt(stname,ptl) =>
            mk_sort stname (List.map (term_from_pt env) ptl)
    else 
        raise
            simple_fail ("sort_from_ps.input sort: " ^ sn ^ " not on ground")
    end

exception UNIFY of string * (term list)


fun ps_of_pt pt env =
    case pt of 
        ptUVar n =>
        (case lookup_us env n of 
             SOME ps => (ps,env) 
           | _ => 
             let val (Av,env1) = fresh_var env
                 val env2 = insert_us n (psvar Av) env1
             in (psvar Av,env2)
             end)
      | pVar (n,ps) => (ps,env)
      | pFun (n,ps,l) => (ps,env)
      | pAnno(pt,ps) => ps_of_pt pt env

(*TODO: read_ast_f "! A. ! B.! f: A -> B. ! g:A ->B.~(f = g) ==> ? a: 1 -> A. ~(f o a = g o a)";
Exception- UNIFY "occurs check(pt):pv a : psv  4 ptu  4" raised*)



fun unify_ps env (ps1:psort) (ps2:psort):env = 
    case (chasevars ps1 env,chasevars ps2 env) of
        (psvar n1,psvar n2) => 
        if n1 = n2 then env else insert_ps n1 (psvar n2) env
      | (psvar n,ps) =>
        if occs_ps n env ps 
        then raise UNIFY 
                   ("occurs check(ps):" ^ stringof_ps (psvar n) ^ " " ^
                   stringof_ps ps,[])
        else insert_ps n ps env
      | (ps,psvar n) => 
        if occs_ps n env ps 
        then raise UNIFY  
                   ("occurs check(ps):" ^ stringof_ps (psvar n) ^ " " ^
                   stringof_ps ps,[])
        else insert_ps n ps env
      | (psrt (sn1,ptl1),psrt (sn2,ptl2)) => 
        if sn1 = sn2 then 
            List.foldr (fn ((a,b),env) => unify_pt env a b)
                       env (zip ptl1 ptl2)
        else raise UNIFY ("different sorts: " ^ sn1 ^ " , " ^ sn2,[])
and unify_pt env pt1 pt2: env= 
    (*clear up repeated cases?*)
    case (chasevart pt1 env,chasevart pt2 env) of 
        (ptUVar a,ptUVar b) => 
        if a = b then env else 
        let val (psa, env1) = ps_of_pt pt1 env
            val (psb, env2) = ps_of_pt pt2 env1
            val env3 = unify_ps env2 psa psb
        in insert_pt a (ptUVar b) env3
        end
      | (ptUVar a, t) => 
        if occs_pt a env t 
        then raise UNIFY ("occurs check(pt):" ^
             stringof_pt (ptUVar a) ^ " " ^ stringof_pt t,[])
        else 
            let val (ps1, env1) = ps_of_pt pt1 env
                val (ps2, env2) = ps_of_pt pt2 env1
                val env3 = unify_ps env2 ps1 ps2
            in 
                insert_pt a t env3
            end
      | (t, ptUVar a) => 
        if occs_pt a env t 
        then raise UNIFY ("occurs check(pt):" ^
             stringof_pt t ^ " " ^ stringof_pt (ptUVar a),[])
        else
            let val (ps1, env1) = ps_of_pt pt1 env
                val (ps2, env2) = ps_of_pt pt2 env1
                val env3 = unify_ps env2 ps1 ps2
            in 
                insert_pt a t env3
            end
      | (pVar (a1,ps1), pVar (a2,ps2)) => 
        if a1 = a2 then unify_ps env ps1 ps2
        else raise UNIFY ("different variable name",[])
      | (pFun(f,ps1,l1),pFun(g,ps2,l2)) => 
        if f = g andalso length l1 = length l2 
        then (let val env = unify_ps env ps1 ps2 in
                  case (l1,l2) of 
                  ([],[]) => env 
                | (h1::r1,h2::r2) => 
                  let val env1 = unify_pt env h1 h2
                  in unify_pt env1 (pFun(f,ps1,r1)) (pFun(g,ps2,r2))
                  end
                | _ => raise UNIFY ("term list cannot be unified",[(*term_from_pt env pt1,term_from_pt env pt2*)])
              end)
        else raise UNIFY ("different functions:"^ f ^ ", " ^ g ,[])
      | (pAnno(pt,ps),t) => unify_pt env pt t
      | (t,pAnno(pt,ps)) => unify_pt env pt t
      | _ => raise UNIFY ("terms cannot be unified",[(*term_from_pt env pt1,term_from_pt env pt2*)])


fun t2pt t = 
    case view_term t of 
        vVar(n,s) => pVar(n,s2ps s)
      | vFun(f,s,l) => pFun(f,s2ps s,map t2pt l)
      | _ => raise simple_fail "bounded variable cannot be converted into pterm"
and s2ps s = 
    case dest_sort s of
        (sn,tl) => psrt(sn,List.map t2pt tl)

val ns2nps =  (fn (a,b) => (a,s2ps b))

val essd:(string , string) dict = Binarymap.mkDict String.compare


(*the name in the dictionary does not matter, what does matter is that different name corresponds to different unification variables. fgt name functions forgets the name strings and turns them into unification variables which corresponds to natural numbers.*)

fun fgt_name_pt pt (nd:(string , string) dict) env = 
    case pt of
        pVar (name,ps) =>
        (case Binarymap.peek(nd,name) of 
            SOME uv => 
            let val (ps1,nd1,env1) = fgt_name_ps ps nd env
                val env2 = case (lookup_us env1 uv) of 
                               SOME ps2 => unify_ps env ps1 ps2
                             | NONE => insert_us uv ps1 env1
            in 
                (ptUVar uv,nd1,env2)
            end
          | NONE => 
            let val (Av,env1) = fresh_var env
                val nd1 = Binarymap.insert(nd,name,Av)
                val (ps1,nd2,env2) = fgt_name_ps ps nd1 env1
                val env3 = insert_us Av ps1 env2
            in 
                (ptUVar Av, nd2,env3)
            end)
      | pFun(f,ps,ptl) => 
        let val (ptl1,nd1,env1) = 
                foldr 
                    (fn (pt,(l,nd,env)) => 
                        let val (pt',nd',env') = fgt_name_pt pt nd env
                        in (pt':: l,nd',env')
                        end)
                    ([],nd,env)
                    ptl
            val (ps1,nd2,env2) = fgt_name_ps ps nd1 env1
        in
            (pFun(f,ps1,ptl1),nd2,env2)
        end
      | _ => raise simple_fail("unexpected pretype constructor" ^ (stringof_pt pt))
and fgt_name_ps ps nd env = 
    case ps of 
        psrt (sn,ptl) => 
        let val (ptl1,nd1,env1) = 
                foldr 
                    (fn (pt,(l,nd,env)) => 
                        let val (pt',nd',env') = fgt_name_pt pt nd env
                        in (pt':: l,nd',env')
                        end)
                    ([],nd,env)
                    ptl
        in
            (psrt(sn,ptl1),nd1,env1)
        end
      | _ => raise simple_fail "fgt_name_ps.unexpected presort variable"

fun nps2ptUVar (n,ps) nd env = fgt_name_pt (pVar(n,ps)) nd env

fun npsl2ptUVarl l env = 
    foldr (fn (p,(l,nd,env)) => 
              let val (pt,nd1,env1) = nps2ptUVar p nd env
              in (pt :: l,nd1,env1)
              end)
          ([],essd,env)
          l

(*
fun mk_pob A = pVar(A,pob)
*)


fun type_infer_ptl env ptl = 
    List.foldr 
        (fn (pt,env) => 
            let val (ps,env1) = ps_of_pt pt env 
            in type_infer env1 pt ps
            end)
        env ptl
and type_infer_pfun env t ty = 
    case t of 
        pFun(f,ps,ptl) =>
        let 
            val env = type_infer_ptl env ptl
        in
        (case lookup_fun (!fsyms) f of 
             SOME (s,l) => 
             let val (uvs,nd,env1) = npsl2ptUVarl (map ns2nps l) env 
                 val (s1,nd1,env2) = fgt_name_ps (s2ps s) nd env1
                 val tounify = zip ptl uvs
                 val env3 = foldr
                                (fn ((a,b),env) => unify_pt env a b) 
                                env1 tounify
             in
                 unify_ps (unify_ps env3 ty s1) ty ps
             end
           | _ => env)
        end
      | _ => raise simple_fail ("not a function term" ^ (stringof_pt t))
and type_infer env t ty = 
    case t of 
        pFun(f,ps,ptl) => type_infer_pfun env t ty
      | pAnno (pt,ps) => 
        (*order to be think more about*)
        let val env1 = type_infer env pt ps
            val (ps',env1') = (ps_of_pt pt env1)
            val env2 = type_infer env1' pt ps'
        in unify_ps env2 ty ps
        end
      | pVar (name,ps) => 
        (case ps of 
             psrt(sn,ptl) => 
             let val env = type_infer_ptl env ptl
             in unify_ps env ty ps
             end
           | _ => unify_ps env ty ps)
      | ptUVar name => 
        (case lookup_us env name of
             SOME ps => unify_ps env ps ty
          | _ => insert_us name ty env)


fun type_infer_args env pf = 
    case pf of
        pPred("=",[t1,t2]) => 
        let val (ps1,env1) = ps_of_pt t1 env
            val (ps2,env2) = ps_of_pt t2 env1
        in unify_ps env2 ps1 ps2
        end
      | pPred(p,ptl) => 
        (case lookup_pred (!psyms) p of 
             SOME l => 
             let val (uvs,_,env1) = npsl2ptUVarl (map ns2nps l) env 
                 val tounify = zip ptl uvs
             in
                 foldr
                     (fn ((a,b),env) => unify_pt env a b) 
                     env1 tounify
             end
           | _ => foldr (fn (pt,env) => 
                            let val (ps,env1) = ps_of_pt pt env 
                            in type_infer env1 pt ps
                            end)
                        env
                        ptl)
      | pfVar(p,ptl) => 
       foldr (fn (pt,env) => 
                            let val (ps,env1) = ps_of_pt pt env 
                            in type_infer env1 pt ps
                            end)
                        env ptl
      | _ => raise simple_fail "not a predicate or a formula variable" 
   
fun type_infer_pf env pf = 
    case pf of 
        pQuant(q,n,ps,pb) =>
(*edited 11.8*)
        let val env = clear_ps n env
            val (Av,env1) = fresh_var env
            val env2 = record_ps n (psvar Av) env1
            val env3 = insert_ps Av ps env2
            val env4 = type_infer_pf env3 pb
        in
           (*type_infer_pf env1 pb*)
           clear_ps n env4
        end
      | pConn(co,pfl) => 
        (case pfl of 
             [] => env
           | h::t => let val env1 = type_infer_pf env h
                     in type_infer_pf env1 (pConn(co,t))
                     end)
      | pPred(p,ptl) => 
        let val env1 = foldr (fn (pt,env) => 
                                 let val (ps,env0) = (ps_of_pt pt env)
                                 in
                                     type_infer env0 pt ps
                                 end) env ptl
        in
            type_infer_args env1 pf
        end
      | pfVar(p,ptl) => 
        let val env1 = foldr (fn (pt,env) => 
                                 let val (ps,env0) = (ps_of_pt pt env)
                                 in
                                     type_infer env0 pt ps
                                 end) env ptl
        in
            type_infer_args env1 pf
        end

(*delete one of the repeated code in type_infer_pf and args!

let pred and function type-infer share common function*)

fun apfst f (x,tl,env) = (f x, tl,env);

fun cons x xs = x::xs;

fun parse_repeat (a,parsefn) tl env = 
    case tl of 
        (Key(b)::tl1) => if b = a then 
                             parse_repeat1 (a,parsefn) tl1 env
                         else ([],tl,env)
      | _ => ([],tl,env)
and parse_repeat1 (a,parsefn) tl env =
    let val (u,tl1,env1) = parsefn tl env
    in apfst (cons u) (parse_repeat (a,parsefn) tl1 env1)
    end

exception ERROR of string

fun rightparen (x, Key")"::toks,env) = (x, toks,env)
  | rightparen _ = raise ERROR "Symbol ) expected";


fun fprec_of "*" = 2
  | fprec_of "+" = 1
  | fprec_of "o" = 3
  | fprec_of "^" = 4
  | fprec_of _ = ~1 


fun mk_pt_conn env co s1 s2 =
    let val (n,env1) = fresh_var env in 
        (pFun (co,psvar n,[s1,s2]),env1)
    end


datatype ast = 
         aId of string 
         | aApp of string * ast list
         | aInfix of ast * string * ast
         | aBinder of string * ast (*variable and sort*) * ast (*body*)
(*         | aCst of ast * ast *)

(* aCst(x ,s)
   A: X ->Y
aInfix (A,":":str, X->Y)

take a sort and turn it back into an ast


 *)


(*all it have to do is to turn a token list into a tree, do not need add interesting sort/term/form*)


 
fun parse_arepeat (a,parsefn) tl = 
    case tl of 
        (Key(b)::tl1) => if b = a then 
                             parse_arepeat1 (a,parsefn) tl1
                         else ([],tl)
      | _ => ([],tl)
and parse_arepeat1 (a,parsefn) tl =
    let val (u,tl1) = parsefn tl
        val (asts,tl2) =  (parse_arepeat (a,parsefn) tl1)
    in (u::asts,tl2)
    end




fun parse_arptl (parsefn:token list -> ast * token list) tl: ast list * token list =
    let val (u,tl1) = parsefn tl 
        val (asts,tl2) = parse_arptl parsefn tl1 handle _ => ([],tl1)
    in (u::asts,tl2)
    end

exception ERROR of string


fun rparen s (x, Key(s')::toks) = 
    if s = s' then (x, toks) else
    raise ERROR ("Symbol:" ^ (s) ^ " expected")
  | rparen s _ =  raise ERROR ("Symbol:" ^ (s) ^ " expected")



fun parse_ast tl =
    case tl of
        Key"!"::tl =>
        let val (asts,tl1) = parse_arptl parse_ast tl
            fun foldthis (avar,abody) = aBinder("!",avar,abody)
            val tl1' = List.tl tl1 (*remove the Key"." after quantified things*)
            val (b,tl2) = parse_ast tl1'
            val ast = List.foldr foldthis b asts
        in
            (ast, tl2)
        end
      | Key"?"::tl =>
        let 
            val (asts,tl1) = parse_arptl parse_ast tl
            fun foldthis (avar,abody) = aBinder("?",avar,abody)
            val tl1' = List.tl tl1
            val (b,tl2) = parse_ast tl1'
            val ast = List.foldr foldthis b asts
        in
            (ast, tl2)
        end 
      | Key"?!"::tl =>
        let 
            val (asts,tl1) = parse_arptl parse_ast tl
            fun foldthis (avar,abody) = aBinder("?!",avar,abody)
            val tl1' = List.tl tl1
            val (b,tl2) = parse_ast tl1'
            val ast = List.foldr foldthis b asts
        in
            (ast, tl2)
        end 
      | _ => parse_ast_fix 0 (parse_ast_atom tl)
and parse_ast_fix n (ast,tl) = 
    case tl of 
        Key(k) :: tl =>
        if fxty k < n then (ast,Key(k) :: tl)
        else
            let
                val (ast1,tl1) =
                    if List.hd tl = Key "!" orelse 
                       List.hd tl = Key "?" orelse
                       List.hd tl = Key "?!" then 
                        parse_ast tl 
                    else 
                    parse_ast_atom tl
                val (ast2,tl2) = parse_ast_fix (fxty k) (ast1,tl1)
                val ast' = aInfix (ast,k,ast2)
            in parse_ast_fix n (ast',tl2)
            end
      | _ => (ast,tl)
and parse_ast_atom tl = 
    case tl of
        (Key"~"::tl1) =>
        let val (ast,tl2) = parse_ast_atom tl1
        in (aApp("~",[ast]),tl2)
        end (*parse_ast_atom here instead of parse_ast*)
     | Id(a)::Key"("::tl1 => 
       let 
           val (astl,tl2) = rparen ")" (parse_arepeat1 (",",parse_ast) tl1)
       in (aApp(a,astl),tl2)
       end
     | Key"("::tl => rparen ")" (parse_ast tl) 
     | Id(a)::tl => (aId(a),tl)
     | Key"<"::tl => 
       let 
           val (astl,tl2) = rparen ">" (parse_arepeat1 (",",parse_ast) tl)
       in (aApp("Pa",astl),tl2)
       end
     | _ => raise simple_fail""



fun pPred_cons pf pt = 
    case pf of 
        pPred(p,tl) => pPred(p,pt :: tl)
      | _ => raise simple_fail "not a pPred"

fun pFun_cons pt0 pt = 
    case pt0 of 
        pFun(f,ps,tl) => pFun(f,ps,pt :: tl)
      | _ => raise simple_fail"not a pFun"


fun pfVar_cons pf pt = 
    case pf of 
        pfVar(p,tl) => pfVar(p,pt :: tl)
      | _ => raise simple_fail "not a pfVar"

 
fun ps_of_const c = 
    case (Binarymap.peek (!fsyms,c)) of 
        SOME (st,l) => if length l = 0 then s2ps st else raise ERROR ("ps_of_const.not a constant: "^ c)
      | _ =>  raise ERROR ("ps_of_const.not a constant: "^ c)



(*task of ast2pt ast2ps: for each variable, these two functions do not know if they are free or not, so it just assign every variable a psvar. here ps_of function is the only way required to find if the variable is already binded to some psvar. this function does not do type inference, so never call insert_ps,
in the case that pVar is produced, it can only be pVar(name,psvar num)


Later realised that need to do insert_ps when coming across pAnno, because for 
!a:mem(A). P(a), the constructor of pQuant does not allow us to store that a is annotated, we can only use env to remember it.

But now think having pAnno as a constructor and store the psvar is redundant work.
 *)
fun psvar_name ps = case ps of psvar n => n | _ => raise PER ("not a psvar",[],[])

fun ast2pt ast (env,n) = 
    case ast of 
        aId(a) =>
        if is_const a then
            (pFun(a,ps_of_const a,[]),(env,n))
        else
            let val a' = if a = "_" then a ^ Int.toString n else a 
                val n' = if a = "_" then n + 1 else n
            in case ps_of env a' of 
                   NONE => let val (Av,env1) = fresh_var env 
                               val env2 = record_ps a' (psvar Av) env1
                           in (pVar(a',psvar Av),(env2,n'))
                           end
                 | SOME ps => (pVar(a',ps),(env,n'))
            end
      (*that means only produces pVar(a,psvar n)*)
      | aApp(str,astl) => 
        if is_fun str then 
            case astl of
                [] => 
                let val (Av,env1) = fresh_var env
                in (pFun(str,psvar Av,[]),(env1,n))
                end
              | h :: t => 
                let val (pt0,(env1,n1)) = ast2pt (aApp(str,t)) (env,n)
                    val (pt,(env2,n2)) = ast2pt h (env1,n1)
                in (pFun_cons pt0 pt,(env2,n2))
                end 
        else raise simple_fail ("not a function symbol: " ^ str) 
      | aInfix(ast1,str,ast2) => 
        (*the case happens only for pAnno.*)
        if str = ":" then 
            case ast1 of 
                aId(name) => 
                let val (ps0,(env1,n1)) = ast2ps ast2 (env,n)
                in
                    case ps_of env name of 
                        NONE => 
                        let val (Av,env2) = fresh_var env1
                            val env3 = record_ps name (psvar Av) env2
                            val ps = psvar Av
                            val env4 = insert_ps Av ps0 env3
                        in
                            (pAnno(pVar(name,ps),ps0), (env4,n1))
                        end
                      | SOME ps => 
                        let val name0 = psvar_name ps
                            val env2 = insert_ps name0 ps0 env1
                        in
                        (pAnno(pVar(name,ps),ps0),(env2,n1))
                        end
                end
              | _ =>
                let val (ps0,(env1,n1)) = ast2ps ast2 (env,n)
                    val (pt0,(env2,n2)) = ast2pt ast1 (env1,n1)
                in
                    (pAnno(pt0,ps0),(env2,n2))
                        (*It can be pAnno(pAnno(pVar(name,psvar),ps1),ps2)*)
                end 
        else
            if mem str ["*","+","^","o"] then
                let val (pt1,(env1,n1)) = ast2pt ast1 (env,n)
                    val (pt2,(env2,n2)) = ast2pt ast2 (env1,n1)
                    val (Av,env3) = fresh_var env2
                in
                    (pFun(str,psvar Av,[pt1,pt2]),(env3,n2))
                end
            else raise simple_fail ("not an infix operator: " ^ str)
      | aBinder(str,ns,b) => 
        raise simple_fail "quantified formula parsed as a term!"
and ast2ps ast (env,n) = 
    case ast of
        aId(ns) => (psrt(ns,[]),(env,n))
      | aApp(ns,atl) => 
        let val (ptl,(env1,n1)) = 
                foldr 
                    (fn (tast,(l,(env,n))) => 
                        let val (pt1,(env1,n1)) = ast2pt tast (env,n)
                        in (pt1 :: l,(env1,n1))
                        end) ([],(env,n)) atl
        in (psrt(ns,ptl),(env1,n1))
        end
      |aInfix(ast1,inx,ast2) =>
       let 
           val (dom,(env1,n1)) = ast2pt ast1 (env,n)
           val (cod,(env2,n2)) = ast2pt ast2 (env1,n1)
           val sn = sortname_of_infix inx
       in 
           (psrt(sn,[dom,cod]),(env2,n2))
       end
      | _ => raise PER ("ast2ps.wrong attempt of trying to turn an aBinder into a pre-sort",[],[])

(*a |-> psvar n is only used to identify the same occurence of a*)

fun name_of_ast ast = 
    case ast of 
        aId a => a
      | aInfix(a,":",_) => name_of_ast a
      | _ => raise PER ("current ast does not have a name",[],[])

fun contain_aBinder ast n = 
    case ast of aBinder (_,ast1,ast2) => if name_of_ast ast1 = n then true else 
                                        contain_aBinder ast2 n
              | _ => false


fun ast2pf ast (env:env,n) = 
    case ast of 
        aId(a) => 
        if a = "T" then (pPred("T",[]),(env,n)) else 
        if a = "F" then (pPred("F",[]),(env,n)) else
        (pfVar(a,[]),(env,n))
      | aApp("~",[ast]) => 
        let val (pf,(env1,n1)) = ast2pf ast (env,n) in
            (pConn("~",[pf]),(env1,n1))
        end
      | aApp(str,astl) =>
        let val (constr,cconstr) = 
                if is_pred str orelse str = "=" then (pPred,pPred_cons)
                else (pfVar,pfVar_cons)
        in
            case astl of
                 [] => (constr(str,[]),(env,n))
               | h :: t => 
                 let val (pf,(env1,n1)) = ast2pf (aApp(str,t)) (env,n)
                     val (pt,(env2,n2)) = ast2pt h (env1,n1)
                 in (cconstr pf pt,(env2,n2))
                 end
        end
      | aInfix(ast1,str,ast2) => 
        if mem str ["&","|","<=>","==>"] then
            let
                val (pf1,(env1,n1)) = ast2pf ast1 (env,n)
                val (pf2,(env2,n2)) = ast2pf ast2 (env1,n1)
            in
                (pConn(str,[pf1,pf2]),(env2,n2))
            end else 
        if mem str ["=","=="] then
            let
                val (pt1,(env1,n1)) = ast2pt ast1 (env,n)
                val (pt2,(env2,n2)) = ast2pt ast2 (env1,n1)
            in
                (pPred(str,[pt1,pt2]),(env2,n2))
            end else
        raise simple_fail ("not an infix operator: " ^ str)
     | aBinder(str,ns,b) => 
        if mem str ["!","?","?!"] then
            let val name = name_of_ast ns
                val pso = ps_of env name
                val env1 = clear_ps name env
                val (Av,env2) = fresh_var env1 
                val env3 = record_ps name (psvar Av) env2 
                val (pt,(env4,n1)) = ast2pt ns (env3,n) 
                val (ps,env5) = ps_of_pt pt env4
                val (pf,(env6,n2)) = ast2pf b (env5,n1)
                val env7 = clear_ps name env6
                val env8 = case pso of SOME ps => record_ps name ps env7 | _ => env7
            in 
                (mk_pQuant str name ps pf,(env8,n2))
            end
        else raise simple_fail "not a quantifier" 
 

(*
(C ast2pf (empty,0)) $ fst o parse_ast $ lex "!a:mem(A). (!a:mem(B).P(a)) & P(a)";
val it =
   (pQuant
     ("!", "a", psvar " 0",
      pConn
       ("&",
        [pQuant ("!", "a", psvar " 2", pfVar ("P", [pVar ("a", psvar " 2")])),
         pfVar ("P", [pVar ("a", psvar " 4")])])), ((?, ?, ?, ?, 5), 0)):
   pform * (env * int)

that is why the ast2pf in the same level of connective is not a fold.
*)


fun parse_ast_end (x:ast, l:token list) =
    if l = [] then x
    else raise ERROR "Extra characters in formula";

fun read_ast_pf a =
    ast2pf (parse_ast_end (parse_ast (lex a))) (empty,0)

fun read_ast_pt a = 
    ast2pt (parse_ast_end (parse_ast (lex a))) (empty,0)


(*parser may have another flag: parse as fun, as pred *)


fun form_from_pf env pf = 
    case pf of 
        pQuant(q,n,ps,pb) => 
        mk_quant q n (sort_from_ps env ps) 
                 (abstract (n,sort_from_ps env ps) (form_from_pf env pb)) 
      | pConn(co,pfl) => 
        mk_conn co (List.map (form_from_pf env) pfl)
      | pPred(P,ptl) => 
        mk_P0 P (List.map (term_from_pt env) ptl)
      | pfVar(P,ptl) => mk_fvar P (List.map (term_from_pt env) ptl)

(*mk_P0 should be mk_pred! just testing! need to change it back*)
(*val f = "P(a)" edit error message to complain if empty is caused by no sort is declared!*)

fun read_ast_t t = 
    let val (pt,(env,_)) = read_ast_pt t
        val (ps,env0) = ps_of_pt pt env
        val env1 = type_infer env0 pt ps
    in (term_from_pt env1 pt,pdict env1)
    end

fun read_ast_f f = 
    let val (pf,(env,_)) = read_ast_pf f
        val env1 = type_infer_pf env pf
    in (form_from_pf env1 pf,pdict env1)
    end

fun cont2env ct = 
    HOLset.foldr 
        (fn ((n,s),env) => record_ps n (s2ps s) env) 
        empty ct 


(*
fun combine_env env1 env2 = 


fun parse_with_cont sn ct f = 
    let
        val env0 = cont2env ct
        val (pf,env) = read_ast_pf sn f 
*)
(*pretty name environment*)


(*collect all the variables in f. 
use explode to turn string into list, if begin with a space, it means the variable is generated. 

keep a dict or ? to store name correspondence and already used names, not only just the one which has a number mapped to , but also the ones which has already present in the formula.

capital letter for objects, lower case for arrows, add "'" if clashed. 

generating letter which does not clash should be done in the function int 2 name, takes 2 arguments, a number and a set of variables names.

need to ensure does not clash with existing names in the formula.*)

type pne = (string,int)Binarymap.dict * int


fun n2l n = 
    if n > 0 then n :: (n2l (Int.-(n, 1))) else [] 
  

fun bad_name (n,s:sort) = if List.hd (explode n) = #" " then true else false

fun try_until_ok n uns = 
    if HOLset.member(uns,str(chr (n+64))) = false then str(chr (n+64)) else try_until_ok (n + 1) uns

fun map_HOLset f s order = 
    let val l = HOLset.listItems s
        val l' = List.map f l
    in HOLset.fromList order l'
    end
(*
fun pretty_form f = 
    let val s0 = fvf f 
        val bad_names = rev (HOLset.listItems (HOLset.filter bad_name s0))
        val used_names0 = HOLset.filter (fn ns => not (bad_name ns)) s0
(*bad name list, used names, *) 
        val l = zip (List.map fst bad_names) (n2l (List.length bad_names))
        fun foldfun ((bn,n), (uns,nr)) = 
            let val gn = try_until_ok n uns
                val uns' = HOLset.add(uns,gn)
                val nr' = (bn,gn) :: nr 
            in
                (uns',nr')
            end
        val envl = snd (List.foldr foldfun (map_HOLset fst used_names0 String.compare,[]) l)
        val env0 = mk_tenv (List.map (fn (n1,n2) => ((n1,mk_ob_sort),mk_var n2 mk_ob_sort)) envl)
        val env = mk_menv env0 emptyfvd
    in
        inst_form env f
    end
*)




fun check_wffv fvs = 
    case fvs of 
        [] => true
      | h :: t => if ill_formed_fv h then
                      raise ERR ("ill-formed free variable",[snd h],[mk_var h],[])
                  else check_wffv t


fun rapf0 f = (fst (read_ast_f f))

fun rapf str = 
    let val f = rapf0 str 
        val fvs = HOLset.listItems (fvf f)
        val _ = check_wffv fvs 
    in f
    end

val rastt = fst o read_ast_t


fun readfq [QUOTE s] = rapf s


fun ast_of_term t = 
    case view_term t of 
        vVar(n,s) => aInfix(aId(n),":",ast_of_sort s)
      | vFun(f,s,l) => aApp (f,List.map ast_of_term l)
      | vB i => 
        raise simple_fail
              "ast_of_term.input is a bounded variable"
and ast_of_sort s = 
    case dest_sort s of 
        (n,tl) => aApp(n, List.map ast_of_term tl)

fun anno_ast (ns as (n,s)) ast = 
    case ast of
        aId a => 
        if a = n then 
            aInfix (aId(a),":",ast_of_sort s)
        else ast
      | aApp (s,astl) => 
        aApp(s,List.map (anno_ast ns) astl)
      | aInfix (ast1,str,ast2) =>
        aInfix (anno_ast ns ast1,str, anno_ast ns ast2)
      | aBinder (str,bns,ast1) => 
        aBinder (str,anno_ast ns bns, anno_ast ns ast1)

fun anno_cont_ast ct ast = 
    HOLset.foldr (uncurry anno_ast) ast ct



fun parse_term_with_cont ct tstr = 
    let val ast0 = parse_ast_end (parse_ast (lex tstr))
        val ast1 = anno_cont_ast ct ast0
        val (pt,(env,_)) = ast2pt ast1 (empty,0)
        val (ps,env1) = ps_of_pt pt env
        val env1 = type_infer env1 pt ps
    in 
        term_from_pt env1 pt 
    end

fun parse_form_with_cont ct fstr = 
    let val ast0 = parse_ast_end (parse_ast (lex fstr))
        val ast1 = anno_cont_ast ct ast0
        val (pf,(env,_)) = ast2pf ast1 (empty,0)
        val env1 = type_infer_pf env pf
    in 
        form_from_pf env1 pf
    end


(*
fun qmatch_parse0 ct fq fl = 
    let val f0 = rapf $ q2str fq
        fun mfn _ asm = 
            let val menv = match_form essps f0 asm mempty
            in SOME asm
                    (*only care about the fact that it can match, do not care about the menv, what to write in this case?*)
            end
            handle _ => NONE
    in case first_opt mfn fl of
           NONE => raise simple_fail "qmatch_parse.no match"
         | SOME f => f
    end
*)


fun match_parse ct fl fq = 
    let val f0 = parse_form_with_cont ct fq
        fun mfn _ asm = 
            let val menv = match_form essps f0 asm mempty
            in SOME asm
                    (*only care about the fact that it can match, do not care about the menv, what to write in this case?*)
            end
            handle _ => NONE
    in case first_opt mfn fl of
           NONE => raise simple_fail "qmatch_parse.no match"
         | SOME f => f
    end
 
end



structure Parse = struct open parser val Term=readfq end


