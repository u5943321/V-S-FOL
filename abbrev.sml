structure abbrev :> abbrev =
struct
  type thm          = logic.thm
  type term         = term.term
  type sort         = term.sort
  type form         = form.form
  type conv         = term -> thm
  type fconv        = form -> thm
  type rule         = thm -> thm
  type cont         = (string * sort) set
  type goal         = cont * form list * form
  type validation   = thm list -> thm
  type tactic       = goal -> goal list * validation
  type thm_tactic   = thm -> tactic
  type thm_tactical = thm_tactic -> thm_tactic
end
