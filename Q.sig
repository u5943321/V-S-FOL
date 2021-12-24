signature Q = 
sig
type term = term.term 
type form = form.form
val q2str: 'a frag list -> string
val qabbrev_tac: form frag list -> tactic
val qby_tac: form frag list -> tactic
val qexists_tac: term frag list -> tactic
val qexistsl_tac: term frag list list -> tactic
val qform_tac:
   (form -> (string * sort) set * form list * form -> goal list * validation)
     -> form frag list -> tactic
val qgen: term frag list -> thm -> thm
val qparse_form_with_cont: (string * sort) set -> form frag list -> form
val qparse_term_with_cont: (string * sort) set -> term frag list -> term
val qpick_assum: form frag list -> thm_tactic -> tactic
val qpick_x_assum : form frag list -> thm_tactic -> tactic
val qspecl_then : term frag list list -> thm_tactic -> thm -> tactic
val qsuff_tac : form frag list -> tactic
val qterm_tac :
   (term -> (string * sort) set * form list * form -> goal list * validation)
     -> term frag list -> tactic
val qterml_tac :
   (term list ->
     (string * sort) set * form list * form -> goal list * validation) ->
     term frag list list -> tactic
val qterml_tcl :
   (term list -> thm_tactic -> thm_tactic) ->
     term frag list list -> thm_tactic -> thm -> tactic
val qspec: term frag list -> thm -> thm
val qspecl: term frag list list -> thm -> thm
val qterm_rule: (term -> thm -> thm) -> term frag list -> thm -> thm
val qterml_rule:
   (term list -> thm -> thm) -> term frag list list -> thm -> thm

end
