structure proofmanager = 
struct
open goalstack

exception NO_PROOFS;

open abbrev History

type tactic = abbrev.tactic
datatype proof = GOALSTACK of goalstack.gstk history
datatype proofs = PRFS of proof list;


fun initial_proofs() = PRFS[];

fun add p (PRFS L) = PRFS (p::L);


fun drop (PRFS (_::rst)) = PRFS rst
  | drop (PRFS []) = raise NO_PROOFS;

fun current_proof (PRFS (p::_)) = p
  | current_proof (PRFS []) = raise NO_PROOFS;



fun rotl (a::rst) = rst@[a]
  | rotl [] = raise simple_fail "rotl: empty list"

fun rotate_proofs i (PRFS []) = PRFS []
  | rotate_proofs i (PRFS L) =
      if i<0 then raise simple_fail "rotate_proofs: negative rotation"
      else if i > length L
           then raise simple_fail "rotate_proofs: more rotations than proofs"
           else PRFS(funpow i rotl L);


fun hd_opr f (PRFS (p::t)) = PRFS(f p::t)
  | hd_opr f otherwise = raise NO_PROOFS;

fun hd_proj f (PRFS (p::_)) = f p
  | hd_proj f otherwise = raise NO_PROOFS;


fun new_history_default obj = new_history{obj=obj, limit=15}
fun new_goalstack g = GOALSTACK(new_history_default (goalstack.new_goal g));

fun set_goal g = new_goalstack g;  



fun backup (GOALSTACK s) = GOALSTACK(undo s)

fun set_backup i (GOALSTACK s) = GOALSTACK(set_limit s i)

fun restore (GOALSTACK s) = GOALSTACK(History.restore s)

fun save (GOALSTACK s) = GOALSTACK(History.save s)

fun forget_history (GOALSTACK s) = GOALSTACK(remove_past s)

fun expandf (tac:tactic.tactic) (GOALSTACK s) = GOALSTACK (apply (goalstack.expandf tac) s)

fun expand (tac:tactic.tactic) (GOALSTACK s) = GOALSTACK (apply (goalstack.e0 tac) s)

fun top_thm (GOALSTACK s) = project goalstack.proved_th s
  

(*
fun rotate i (GOALSTACK s) = GOALSTACK(apply (C goalstack.rotate i) s)

fun flatn i (GOALSTACK s) = GOALSTACK(apply (C goalStack.flatn i) s)
  | flatn i (GOALTREE t) = raise ERR "flatn"
                               "not implemented for goal trees";

may later
*)

fun restart (GOALSTACK s) = GOALSTACK (new_history_default (initialValue s))

(*---------------------------------------------------------------------------*)
(* Prettyprinting of goalstacks and goaltrees.                               *)
(*---------------------------------------------------------------------------*)

fun pp_proof (GOALSTACK s) = project goalstack.ppgstk s





end

structure proofManagerLib = struct 
open abbrev proofmanager

type tactic = tactic.tactic

type proof = proofmanager.proof
type proofs = proofmanager.proofs


val the_proofs = ref (proofmanager.initial_proofs());

fun proofs() = !the_proofs;
fun top_proof() = proofmanager.current_proof(proofs());


(*
fun new_goalstack g f = GOALSTACK(new_history_default (goalStack.new_goal g f));

fun new_goalstack g f =
   (the_proofs := Manager.add (Manager.new_goalstack g f) (proofs());
    proofs());

fun set_goal g = new_goalstack g Lib.I;

fun g q = set_goal([],Parse.Term q);

*)

fun new_goalstack g =
   (the_proofs := proofmanager.add (proofmanager.new_goalstack g) (proofs());
    proofs());

fun set_goal g:proofmanager.proofs = new_goalstack g;



fun g q = set_goal(fvf (Parse.Term q),[],Parse.Term q);

fun restart() =
   (the_proofs := hd_opr proofmanager.restart (proofs());
    top_proof());

fun backup () =
   (the_proofs := proofmanager.hd_opr proofmanager.backup (proofs());
    top_proof());

fun restore () =
   (the_proofs := proofmanager.hd_opr proofmanager.restore (proofs());
    top_proof());

fun save () =
   (the_proofs := proofmanager.hd_opr proofmanager.save (proofs());
    top_proof());

val b = backup;

fun set_backup i =
  (the_proofs := proofmanager.hd_opr (proofmanager.set_backup i) (proofs()));

fun forget_history () =
  (the_proofs := proofmanager.hd_opr (proofmanager.forget_history) (proofs()));

fun restart() =
   (the_proofs := proofmanager.hd_opr proofmanager.restart (proofs());
    top_proof());


fun drop_all () =
    (the_proofs := proofmanager.initial_proofs(); !the_proofs)

fun expand (tac:tactic.tactic) =
   (the_proofs := proofmanager.hd_opr (proofmanager.expand tac) (proofs());
    top_proof())

val e = expand;

fun ppproof (GOALSTACK s) = project goalstack.ppgstk s

fun PPproof printdepth _ (prf:proofmanager.proof) =
    let
        val s = ppproof prf
        val SOME (pretty,_,_) = lower s ()
    in pretty
    end

val _ = PolyML.addPrettyPrinter PPproof

end


