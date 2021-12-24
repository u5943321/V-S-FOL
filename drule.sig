signature drule = 
sig
val F_conj1: form -> thm
val F_conj2: form -> thm
val F_conj_1: thm
val F_conj_2: thm
val F_dimp1: form -> thm
val F_dimp2: form -> thm
val F_dimp_1: thm
val F_dimp_2: thm
val F_disj1: form -> thm
val F_disj2: form -> thm
val F_disj_1: thm
val F_disj_2: thm
val F_imp: form -> thm
val F_imp1: form -> thm
val F_imp2: form -> thm
val F_imp_1: thm
val F_imp_2: thm
val T_conj1: form -> thm
val T_conj2: form -> thm
val T_conj_1: thm
val T_conj_2: thm
val T_dimp1: form -> thm
val T_dimp2: form -> thm
val T_dimp_1: thm
val T_dimp_2: thm
val T_disj1: form -> thm
val T_disj2: form -> thm
val T_disj_1: thm
val T_disj_2: thm
val T_imp1: form -> thm
val T_imp2: form -> thm
val T_imp_1: thm
val T_imp_2: thm
val add_assum: form -> thm -> thm
val cj_imp1: form -> thm
val cj_imp2: form -> thm
val conj_T: thm
val conj_iff: thm -> thm -> thm
val conj_imp_equiv: form -> form -> form -> thm
val contra2any: form -> form -> thm
val contraF: form -> thm
val depends_on: string * sort -> term -> bool
val dimp_iff: thm -> thm -> thm
val dimp_mp_l2r: thm -> thm -> thm
val dimp_mp_r2l: thm -> thm -> thm
val dimpl2r: thm -> thm
val dimpr2l: thm -> thm
val disj_comm: form -> form -> thm
val disj_iff: thm -> thm -> thm
val disj_imp_distr: form -> form -> form -> thm
val disj_imp_distr1: form -> form -> form -> thm
val disj_imp_distr2: form -> form -> form -> thm
val disj_imp_distr_th: thm -> thm
val disj_imp_equiv: form -> form -> thm
val disj_swap: form -> form -> thm
val double_neg: form -> thm
val eqF_intro: thm -> thm
val eqF_intro_form: form -> thm
val eqT_intro: thm -> thm
val eqT_intro_form: form -> thm
val equivT: thm -> thm
val exists_false: string * sort -> thm
val exists_false_sort: string -> thm
val exists_iff: string * sort -> thm -> thm
val exists_imp: string -> sort -> term -> form -> form -> thm
val forall_false: string * sort -> thm
val forall_true: string * sort -> thm
val forall_true_sort: string -> thm
val frefl: form -> thm
val iff_swap: thm -> thm
val iff_trans: thm -> thm -> thm
val imp_disj_distr: form -> form -> form -> thm
val imp_iff: thm -> thm -> thm
val imp_trans: thm -> thm -> thm
val nT_equiv_F: thm
val neg_iff: thm -> thm
val prove_hyp: thm -> thm -> thm
val simple_exists: string * sort -> thm -> thm
val simple_fail: string -> exn
val spec_all: thm -> thm
val specl: term list -> thm -> thm
val tautT: form -> thm
val undisch: thm -> thm
val undisch_all: thm -> thm
val CONJ_ASSOC: thm
val CONJ_IMP_IMP: thm
val F2f: form -> thm
val NEG_CONJ2IMP_NEG: thm
val NEG_CONJ2IMP_NEG0: form -> form -> thm
val abstl: (string * sort) list -> thm -> thm
val conjIl: thm list -> thm
val conj_all_assum: thm -> thm
val conj_assoc: form -> form -> form -> thm
val conj_assum: form -> form -> thm -> thm
val contr: form -> thm -> thm
val contrapos: thm -> thm
val depends_s: string * sort -> sort -> bool
val depends_t: string * sort -> term -> bool
val disch_all: thm -> thm
val dischl: form list -> thm -> thm
val double_neg_elim: thm
val double_neg_th: thm -> thm
val edges_from_fvs:
   (string * sort) set -> ((string * sort) * (string * sort)) list
val edges_from_fvs0:
   (string * sort) set -> ((string * sort) * (string * sort)) list
val edges_from_fvs1:
   string * sort ->
     (string * sort) list -> ((string * sort) * (string * sort)) list
val elim_double_neg: thm -> thm
val exists_forall: string * sort -> thm
val find_var: (string * 'a) list -> string -> string * 'a
val gen_all: thm -> thm
val gen_disch_all: thm -> thm
val gen_dischl: form list -> thm -> thm
val genl: (string * sort) list -> thm -> thm
val mk_conjl: form list -> form
val mk_disjl: form list -> form
val nF2T: thm
val nT2F: thm
val neg_disch: form -> thm -> thm
val notf_f2F: form -> thm

(*
open SymGraph
val order_of: (key * sort) set -> key list
val order_of_fvs: form -> key list

better have it here but have error
drule.sig:125: error: end expected but open was found
drule.sig:127: error: = expected but val was found
*)
val pe_cl1: string * sort -> thm
val pe_cl2: string * sort -> thm
val pe_cl3: string * sort -> thm
val simple_genl: (string * sort) list -> thm -> thm
val split_assum: thm -> thm
val split_assum0: form -> thm -> thm
val strip_all_and_imp: thm -> thm
val strip_neg: thm -> thm
val forall_iff: (string * sort) -> thm -> thm
val CONJ_COMM:thm
end
