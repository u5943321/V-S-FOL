
datatype tlabel
    = V
    | Fn of string


datatype 'a tnet
    = LEAF of (term * 'a) list
    | NODE of (tlabel * 'a tnet) list;



fun tlabel_of tm =
   if is_var tm then V else 
   let val (f,_,_) = dest_fun tm
   in Fn f
   end

val empty = NODE [];

fun is_empty (NODE[]) = true
  | is_empty    _     = false;


fun net_assoc label =
 let fun get (LEAF _) = raise simple_fail "net_assoc.LEAF: no children"
       | get (NODE subnets) =
            case assoc1 label subnets
             of NONE => empty
              | SOME (_,net) => net
 in get
 end

fun overwrite (p as (a,_)) =
  let fun over [] = [p]
        | over ((q as (x,_))::rst) =
            if (a=x) then p::rst else q::over rst
  in over
  end;



local
  fun mtch tm (NODE []) = []
    | mtch tm net =
       let val label = tlabel_of tm
           val Vnet = net_assoc V net
           val nets =
            case label
             of V => []
              | Fn f =>
                let val (_,s,ts) = dest_fun tm
                    val net0 = net_assoc label net
                in itlist mtchs (rev ts) [net0]
                end
       in itlist (fn NODE [] => I | net => cons net) nets [Vnet]
       end
  and mtchs t [] = []
    | mtchs t (nhd :: ntl) = append (mtch t nhd) (mtchs t ntl)
in
fun match tm net =
  if is_empty net then []
  else
    itlist (fn LEAF L => append (List.map #2 L) | _ => fn y => y)
           (mtch tm net) []
end;



fun insert (pair as (tm,_)) N =
let fun enter _ _  (LEAF _) = raise simple_fail "insert.LEAF: cannot insert"
   | enter defd tm (NODE subnets) =
      let val label = tlabel_of tm
          val child =
             case assoc1 label subnets of NONE => empty | SOME (_,net) => net
          fun exec [] (LEAF L)  = LEAF(pair::L)
            | exec [] (NODE _)  = LEAF[pair]
            | exec (h::rst) net = enter rst h net
          val new_child =
              case label
               of Fn f =>  
                  let val (_,_,ts) = dest_fun tm
                  in if ts = [] then exec defd child
                     else enter ((tl ts) @ defd) (hd ts) child
                  end
              | _ => exec defd child
      in
         NODE (overwrite (label,new_child) subnets)
      end
in enter [] tm N
end;



datatype flabel
    = Q of string
    | Cn of string
    | fV
    | Pr of string
  (*  | tV
| tFn of string *)


datatype 'a fnet
    = fLEAF of (form * 'a) list
    | fNODE of (flabel * 'a fnet) list;


val fempty = fNODE [];

fun is_fempty (fNODE[]) = true
  | is_fempty    _     = false;



fun flabel_of fm =
    case view_form fm of
        vPred (P,true,_) => Pr P
      | vPred (P,false,_) => fV
      | vConn(co,_) => Cn co
      | vQ(q,_,_,_) => Q q




fun fnet_assoc label =
 let fun get (fLEAF _) = raise simple_fail "fnet_assoc.fLEAF: no children"
       | get (fNODE subnets) =
            case assoc1 label subnets
             of NONE => fempty
              | SOME (_,net) => net
 in get
 end

fun dest_quant f = 
    case view_form f of
        vQ(q,_,_,_) => 
        if q = "!" then dest_forall f else
        if q = "?" then dest_exists f else
        if q = "?!" then dest_uex f 
        else raise ERR ("dest_quant.ill-formed formula",[],[],[f])
      | _ => raise ERR ("dest_quant.not a quantified formula",[],[],[f])


fun dest_conn f = 
    case view_form f of 
        vConn(co,[f1,f2]) =>
        if co = "&" then dest_conj f else
        if co = "|" then dest_disj f else
        if co = "==>" then dest_imp f else
        if co = "<=>" then dest_dimp f  else
        raise ERR ("dest_conn.ill-formed formula",[],[],[f])
      | _ => raise ERR ("dest_conn.not a (binary) connective",[],[],[f])
 


local
  fun fmtch fm (fNODE []) = []
    | fmtch fm net =
       let val label = flabel_of fm
           val Vnet = fnet_assoc fV net
           val nets =
            case label
             of fV => [fnet_assoc label net]
              | Pr _ => [fnet_assoc label net]
              | Q _    => fmtch (#2 (dest_quant fm)) (fnet_assoc label net)
              | Cn co   => 
                if co = "~" then 
                    fmtch (dest_neg fm) (fnet_assoc label net)
                else 
                    let val (lf,rf) = dest_conn fm
                          in itlist(append o fmtch rf)
                                   (fmtch lf (fnet_assoc label net)) []
                           end
       in itlist (fn fNODE [] => I | net => cons net) nets [Vnet]
       end
in
fun fmatch fm net =
  if is_fempty net then []
  else
    itlist (fn fLEAF L => append (List.map #2 L) | _ => fn y => y)
           (fmtch fm net) []
end;


fun finsert (pair as (fm,_)) N =
let fun fenter _ _  (fLEAF _) = raise simple_fail ("finsert.LEAF: cannot insert")
   | fenter defd fm (fNODE subnets) =
      let val label = flabel_of fm
          val child =
             case assoc1 label subnets of NONE => fempty 
                                        | SOME (_,net) => net
          val new_child =
            case label
             of Cn co =>
                if co = "~" then 
                    fenter defd (dest_neg fm) child
                else 
                    let val (lf,rf) = dest_conn fm
                       in fenter (rf::defd) lf child end
              | Q _ => fenter defd (#2 (dest_quant fm)) child
              | _   => let fun exec [] (fLEAF L)  = fLEAF(pair::L)
                             | exec [] (fNODE _)  = fLEAF[pair]
                             | exec (h::rst) net = fenter rst h net
                       in
                          exec defd child
                       end
      in
         fNODE (overwrite (label,new_child) subnets)
      end
in fenter [] fm N
end;



fun add_trewrites net thl = 
    itlist insert
                (List.map (fn th => ((#1 o dest_eq o concl) th, rewr_conv th)) (flatten (mapfilter rw_tcanon thl)))
                net




fun add_frewrites fnet thl = 
    itlist finsert
                (List.map (fn th => ((#1 o dest_dimp o concl) th, rewr_fconv th)) (flatten (mapfilter rw_fcanon thl)))
                fnet



fun rewrites_conv net tm = first_conv (match tm net) tm 

fun rewrites_fconv fnet fm = first_fconv (fmatch fm fnet) fm 


fun gen_rewrite_conv (rw_func:conv -> conv) net thl = 
    rw_func (rewrites_conv (add_trewrites net thl))

fun gen_rewrite_fconv (rw_func:conv-> fconv -> fconv) net fnet thl =
   rw_func (rewrites_conv (add_trewrites net thl))
           (rewrites_fconv (add_frewrites fnet thl));



fun REWR_FCONV thl = (gen_rewrite_fconv basic_fconv empty fempty thl)



fun REWR_TAC thl = 
fconv_tac (gen_rewrite_fconv basic_fconv empty fempty thl)

val rw = REWR_TAC





