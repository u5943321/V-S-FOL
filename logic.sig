signature logic = 
sig
type thm
datatype thm_view = vThm of ((string * sort) set * form list * form) 
val EQ_fsym: string -> thm list -> thm
val EQ_psym: string -> thm list -> thm
val add_cont: (string * sort) set -> thm -> thm
val allE: term -> thm -> thm
val allI: string * sort -> thm -> thm
val ant: thm -> form list
val asml_U: form list list -> form list
val assume: form -> thm
val concl: thm -> form
val conjE1: thm -> thm
val conjE2: thm -> thm
val conjI: thm -> thm -> thm
val cont: thm -> (string * sort) set
val contl_U: (string * sort) set list -> (string * sort) set
val depends_on: string * sort -> term -> bool
val dest_thm: thm -> (string * sort) set * form list * form
val dimpE: thm -> thm
val dimpI: thm -> thm -> thm
val disch: form -> thm -> thm
val disjE: thm -> thm -> thm -> thm
val disjI1: form -> thm -> thm
val disjI2: form -> thm -> thm
val eq_thm: thm -> thm -> bool
val existsE: string * sort -> thm -> thm -> thm
val existsI: string * sort -> term -> form -> thm -> thm
val falseE: form list -> form -> thm
val inst_thm: menv -> thm -> thm
val mk_fth: form -> thm
val mk_thm: (string * sort) set * form list * form -> thm
val mp: thm -> thm -> thm
val negE: thm -> thm -> thm
val negI: form -> thm -> thm
val refl: term -> thm
val sym: thm -> thm
val tautI: form -> thm
val trans: thm -> thm -> thm
val trueI: form list -> thm
val view_thm: thm -> thm_view
val uex_def:form -> thm
val define_pred: form -> thm 

end
