signature goalstack =
sig
    include abbrev
    type tac_result 
    datatype proposition = POSED of abbrev.goal
                       | PROVED of logic.thm * abbrev.goal
    datatype gstk = GSTK of {prop  : proposition,
                             stack : tac_result list}
    val prove: form.form -> tactic.tactic -> logic.thm
    val new_goal: abbrev.cont * form.form list * form.form -> gstk
    val rapg: string -> gstk
    val proved_th: gstk -> logic.thm
    val expandf: tactic.tactic -> gstk -> gstk
    val e0: tactic.tactic -> gstk -> gstk
    val current_goal: tac_result -> abbrev.goal
    val current_tac_result: gstk -> tac_result
    val cg: gstk -> abbrev.goal
    val form_goal: form -> gstk
    val find_th: string -> (string * thm) list
    val prove_store: string * gstk -> thm
    val store_thm: string * thm -> unit
    val ppgstk: gstk -> ('a, unit) smpp.t
end
