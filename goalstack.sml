structure goalstack :> goalstack = 
struct
open term form logic abbrev tactic parser smpp pp


fun prove f tac = 
    let
        val (subgoals,vfn) = tac (fvf f,[],f)
    in
        case (subgoals) of 
            [] => vfn []
          | h :: t => raise simple_fail "remaining subgoals"
    end

type tac_result = {goals      : goal list,
                   validation : thm list -> thm}

datatype proposition = POSED of goal
                     | PROVED of thm * goal;

datatype gstk = GSTK of {prop  : proposition,
                         stack : tac_result list}

fun new_goal g = GSTK{prop=POSED g, stack=[]}

fun form_goal f = new_goal (fvf f,[]:form list,f)


fun rapg f = 
    let val f0 = rapf f in new_goal (fvf f0,[]:form list,f0) end

fun proved_th (GSTK{prop:proposition,...}) = 
    case prop of
        PROVED (th,_) => th
      | _ => raise simple_fail "goal is not proved yet"

fun current_tac_result (GSTK{prop,stack:tac_result list}) = 
    case stack of
        [] => raise simple_fail "no remaining goal"
      | h :: t => h

fun current_goal ({goals:goal list,validation:validation}:tac_result) = hd goals


fun return(GSTK{stack={goals=[],validation}::rst, prop as POSED g}) =
    let val th = validation []
    in case rst
        of [] => GSTK{prop=PROVED (th,g), stack=[]}
         | {goals = _::rst_o_goals, validation}::rst' =>
           (
             return(GSTK{prop=prop, 
                         stack={goals=rst_o_goals,
                                validation=fn thl => validation(th::thl)}::rst'})
           )
         | otherwise => raise simple_fail ""
    end
  | return gstk = gstk

fun say s = print s

fun add_string_cr s = say (s^"\n")
fun cr_add_string_cr s = say ("\n"^s^"\n")
fun imp_err s =
    raise simple_fail ("expandf or expand_listf" ^ "implementation error: "^s)

fun expand_msg dpth (GSTK{prop = PROVED _, ...}) = ()
  | expand_msg dpth (GSTK{prop, stack as {goals, ...}::_}) =
    let val dpth' = length stack
    in if dpth' > dpth
       then if (dpth+1 = dpth')
            then add_string_cr
                     (case (length goals)
                       of 0 => imp_err "1"
                        | 1 => "1 subgoal:"
                        | n => Int.toString n^" subgoals:")
            else imp_err "2"
       else cr_add_string_cr "Remaining subgoals:"
    end
  | expand_msg _ _ = raise simple_fail "3" ;

fun expandf _ (GSTK{prop=PROVED _, ...}) =
    raise simple_fail "expandf: goal has already been proved"
  | expandf tac (GSTK{prop as POSED g, stack}) =
     let val arg = (case stack of [] => g | tr::_ => hd (#goals tr))
         val (glist,vf) = tac arg
         val dpth = length stack
         val gs = return(GSTK{prop=prop,
                              stack={goals=glist, validation=vf} :: stack})
     in expand_msg dpth gs ; gs end

 
fun e0 tac = expandf (valid tac) 


fun ppintf (n,f) = add_string (Int.toString n) >> add_string"." >>
                   block HOLPP.CONSISTENT 10 (ppform false (LR (NONE,NONE)) f)

fun n2l n = 
    if n > 0 then n :: (n2l (n - 1)) else [] 



type ThmDataBase = (string,thm)Binarymap.dict 

val ThmDB0: ThmDataBase = Binarymap.mkDict String.compare

val ThmDB = ref ThmDB0

fun store_thm (thname,th) = 
    ThmDB := Binarymap.insert(!ThmDB,thname,th)


fun find_th str = 
    Binarymap.foldr (fn (thname,th,l0) => if String.isSubstring str thname then 
                                              (thname,th) :: l0 else l0)  [] (!ThmDB)
      
fun prove_store (n,g0) = 
    let 
        val th = proved_th g0
        val _ = store_thm(n,th)
    in
        th 
    end




fun store_as name th = 
let val _ = store_thm(name, th)
in th
end


fun store_ax (name,f) = store_as name (new_ax f)




(*partitition into three things or multiple things *)

fun cons_insert (ns:string * sort) dict = 
    let val sn = sort_name (snd ns)
    in case Binarymap.peek(dict,sn) of
           SOME l => Binarymap.insert(dict,sn,ns :: l)
         | NONE => Binarymap.insert(dict,sn,[ns])
    end


fun partition_cont ct = 
 HOLset.foldr (fn ((n,s),d) => cons_insert (n,s) d) (Binarymap.mkDict String.compare) ct



fun ppns (ns as (n,s)) = 
    if on_ground (sort_name s) then ppterm false (LR(NONE,NONE)) (mk_var ns)
    else ppterm true (LR(NONE,NONE)) (mk_var ns)

fun ppnsl nsl = 
    case nsl of [] => add_string ""
              | h :: t => ppnsl t >> ppns h  

fun ppcont ct =
    Binarymap.foldr (fn (sn,nsl,a) => (a >> ppnsl nsl)) 
    (add_string "") (partition_cont ct)

fun ppgoal (G,A,C) = 
    let
        val Gvl = List.map mk_var (HOLset.listItems G)
    in
        ppcont G >> add_newline >>
               (pr_list ppintf (add_break (1,0)) (rev(zip (n2l (List.length A)) A))) >>
                add_newline >>
                add_string "----------------------------------------------------------------------" >>
                add_newline >>
                block HOLPP.CONSISTENT 10
                (ppform false (LR (NONE,NONE)) C)
    end 

fun PPgoal printdepth _ th = let val s = ppgoal th
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end


fun ppprop prop = 
    case prop of 
        POSED g => ppgoal g
      | PROVED (th,g) => add_string "PROVED!" >> ppthm th 


fun PPprop printdepth _ th = let val s = ppprop th
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

                                 
val _ = PolyML.addPrettyPrinter PPprop

fun ppgoals goals = 
    case goals of [] => add_string ""
                | h :: t => (ppgoal h) >> add_newline >> (ppgoals t)

fun pptac_result ({goals:goal list,validation:thm list -> thm}) = ppgoals (rev goals)
    

fun PPtac_result printdepth _ rst = let val s =  pptac_result rst
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end


fun ppgstk (GSTK{prop:proposition, stack: tac_result list}) = 
    case stack of [] => ppprop prop | h :: t => pptac_result h


fun PPgstk printdepth _ (gstk:gstk) = let val s = ppgstk gstk
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end


(*print out the hd of tac result list, do not print out the prop*)
val _ = PolyML.addPrettyPrinter PPgstk


val cg = current_goal o current_tac_result 

end
