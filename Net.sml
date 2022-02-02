

open Lib Feedback KernelTypes

val ERR = mk_HOL_ERR "Net";



fun mk_clos (s, Bv i) =
      (case (Subst.exp_rel(s,i))
        of (0, SOME t) => t
         | (k, SOME t) => mk_clos (Subst.shift(k,Subst.id), t)
         | (v, NONE)   => Bv v)
  | mk_clos (s, t as Fv _)     = t
  | mk_clos (s, t as Const _)  = t
  | mk_clos (s,Clos(Env,Body)) = Clos(Subst.comp mk_clos (s,Env), Body)
  | mk_clos (s,t)              = Clos(s, t)
;

fun push_clos (Clos(E, Comb(f,x))) = Comb(mk_clos(E,f), mk_clos(E,x))
  | push_clos (Clos(E, Abs(v,M)))  = Abs(v, mk_clos (Subst.lift(1,E),M))
  | push_clos _ = raise ERR "push_clos" "not a subst"
;



local
open KernelSig
in
fun break_abs(Abs(_,Body)) = Body
  | break_abs(t as Clos _) = break_abs (push_clos t)
  | break_abs _ = raise ERR "break_abs" "not an abstraction";

fun dest_thy_const (Const(id,ty)) =
      let val {Name,Thy} = name_of_id id
      in {Thy=Thy, Name=Name, Ty=to_hol_type ty}
      end
  | dest_thy_const _ = raise ERR"dest_thy_const" "not a const"

fun break_const (Const p) = (I##to_hol_type) p
  | break_const _ = raise ERR "break_const" "not a const"

fun dest_const (Const(id,ty)) = (name_of id, to_hol_type ty)
  | dest_const _ = raise ERR "dest_const" "not a const"
end



datatype label
    = V
    | Cmb
    | Lam
    | Cnst of string * string ;  (* name * segment *)


datatype tlabel
    = V
    | Fn



datatype flabel
    = Q
    | Conn
    | fV
    | Pr




(*---------------------------------------------------------------------------*
 *   Tags corresponding to the underlying term constructors.                 *
 *---------------------------------------------------------------------------*)

datatype label
    = V
    | Cmb
    | Lam
    | Cnst of string * string ;  (* name * segment *)

(*---------------------------------------------------------------------------*
 *    Term nets.                                                             *
 *---------------------------------------------------------------------------*)

datatype 'a net
    = LEAF of (term * 'a) list
    | NODE of (label * 'a net) list;


val empty = NODE [];

fun is_empty (NODE[]) = true
  | is_empty    _     = false;

(*---------------------------------------------------------------------------*
 * Determining the top constructor of a term. The following is a bit         *
 * convoluted, since doing a dest_abs requires a full traversal to replace   *
 * the bound variable with a free one. Therefore we make a separate check    *
 * for abstractions.                                                         *
 *---------------------------------------------------------------------------*)



fun is_bvar (Bv _)    = true | is_bvar _  = false;
fun is_var  (Fv _)    = true | is_var _   = false;
fun is_const(Const _) = true | is_const _ = false;
fun is_comb(Comb _) = true | is_comb(Clos(_,Comb _)) = true | is_comb _ = false
fun is_abs(Abs _) = true | is_abs(Clos(_,Abs _)) = true | is_abs _ = false;




fun label_of tm =
   if is_abs tm then Lam else
   if is_bvar tm orelse is_var tm then V else
   if is_comb tm then Cmb
   else let val {Name,Thy,...} = dest_thy_const tm
        in Cnst (Name,Thy)
        end


fun net_assoc label =
 let fun get (LEAF _) = raise ERR "net_assoc" "LEAF: no children"
       | get (NODE subnets) =
            case assoc1 label subnets
             of NONE => empty
              | SOME (_,net) => net
 in get
 end


fun dest_comb (Comb r) = r
  | dest_comb (t as Clos _) = dest_comb (push_clos t)
  | dest_comb _ = raise ERR "dest_comb" "not a comb"


local
  fun mtch tm (NODE []) = []
    | mtch tm net =
       let val label = label_of tm
           val Vnet = net_assoc V net
           val nets =
            case label
             of V => []
              | Cnst _ => [net_assoc label net]
              | Lam    => mtch (break_abs tm) (net_assoc Lam net)
              | Cmb    => let val (Rator,Rand) = dest_comb tm
                          in itlist(append o mtch Rand)
                                   (mtch Rator (net_assoc Cmb net)) []
                           end
       in itlist (fn NODE [] => I | net => cons net) nets [Vnet]
       end
in
fun match tm net =
  if is_empty net then []
  else
    itlist (fn LEAF L => append (map #2 L) | _ => fn y => y)
           (mtch tm net) []
end;

(*---------------------------------------------------------------------------*
 *        Adding to a term net.                                              *
 *---------------------------------------------------------------------------*)

fun overwrite (p as (a,_)) =
  let fun over [] = [p]
        | over ((q as (x,_))::rst) =
            if (a=x) then p::rst else q::over rst
  in over
  end;

fun insert (p as (tm,_)) N =
let fun enter _ _  (LEAF _) = raise ERR "insert" "LEAF: cannot insert"
   | enter defd tm (NODE subnets) =
      let val label = label_of tm
          val child =
             case assoc1 label subnets of NONE => empty | SOME (_,net) => net
          val new_child =
            case label
             of Cmb => let val (Rator,Rand) = dest_comb tm
                       in enter (Rand::defd) Rator child end
              | Lam => enter defd (break_abs tm) child
              | _   => let fun exec [] (LEAF L)  = LEAF(p::L)
                             | exec [] (NODE _)  = LEAF[p]
                             | exec (h::rst) net = enter rst h net
                       in
                          exec defd child
                       end
      in
         NODE (overwrite (label,new_child) subnets)
      end
in enter [] tm N
end;

val t0 = Fv ("x",Tyv "b")

val n0 = insert (t0,t0) empty;

val t1 = Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "b"))

val n1 = insert (t1,t1) n0;

val t2 = Abs (Comb (Fv ("f",Tyv "a"),Fv ("f",Tyv "a'")),Fv ("x",Tyv "b"))

val n2 = insert (t2,t2) n1;

val t3 = Abs (Fv ("x",Tyv "b"),Comb (Fv ("f",Tyv "a"),Fv ("f",Tyv "a'")))

val n3 = insert (t3,t3) n2;

val t4 = Abs (Fv ("x",Tyv "b"),Comb (Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "b")),Fv ("f",Tyv "a'")))

val n4 = insert (t4,t4) n3;

val t5 = Comb (Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "b")),Fv ("f",Tyv "a'"))

val n5 = insert (t5,t5) n4;

val t6 = Comb (Fv ("f",Tyv "a'"),Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "b")))

val n6 = insert (t6,t6) n5;


val t1 = (Comb (Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "b")),Fv ("k",Tyv "b")))

val t2 = Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "b"))

val t3 = Abs (Fv ("f",Tyv "b"),Fv ("x",Tyv "b"))

val t4 = Abs (Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "b")),Fv ("k",Tyv "b"))

val t5 = Abs (Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "b")),
              Abs (Fv ("f",Tyv "a"),Fv ("x",Tyv "k")))


GEN_REWRITE_CONV Conv.TOP_DEPTH_CONV
 (implicit_rewrites()) thl
= 
 Conv.TOP_DEPTH_CONV (REWRITES_CONV (add_rewrites  (implicit_rewrites()) thl));

“isLim(fam)”
