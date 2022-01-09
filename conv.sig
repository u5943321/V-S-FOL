signature conv = 
sig
include abbrev
val all_conv: conv
val all_fconv: fconv
val arg_conv: conv -> conv
val changed_conv: conv -> conv
val depth_conv: conv -> conv
val first_conv: conv list -> conv 
val land_conv: conv -> conv
val no_conv: conv 
val orelsec: conv * conv -> conv
val part_fmatch: (thm -> form) -> thm -> fconv
val part_tmatch: (thm -> term) -> thm -> conv
val rand_conv: conv -> conv 
val redepth_conv: conv -> conv
val repeatc: conv -> conv
val rewr_conv: thm -> conv
val rewr_fconv: thm -> fconv
val simp_trace: bool ref
val thenc: conv * conv -> conv
val thenfc: fconv * fconv -> fconv
val top_depth_conv: conv -> conv
val try_conv: conv -> conv
val GSYM: thm -> thm
val basic_fconv: conv -> fconv -> fconv
val basic_once_fconv: conv -> fconv -> fconv
val basic_taut_fconv: fconv
val changed_fconv: fconv -> fconv
val conj_fconv: fconv -> fconv
val conv_rule: fconv -> thm -> thm
val depth_fconv: conv -> fconv -> fconv
val dimp_fconv: fconv -> fconv
val disj_fconv: fconv -> fconv
val double_neg_fconv: fconv
val f2f: thm
val f2f_T: thm
val first_fconv: fconv list -> fconv
val imp_fconv: fconv -> fconv
val land_fconv: conv -> fconv -> fconv
val lconj_fconv: fconv -> fconv
val ldimp_fconv: fconv -> fconv
val ldisj_fconv: fconv -> fconv
val limp_fconv: fconv -> fconv
val lpred_fconv: conv -> fconv
val nFT_fconv: fconv
val neg_fconv: fconv -> fconv
val neg_neg_elim: thm -> thm
val no_fconv: 'a -> 'b
val once_depth_conv: conv -> conv
val once_depth_fconv: conv -> fconv -> fconv
val orelsefc: ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
val pred_fconv: conv -> fconv
val rand_fconv: conv -> fconv -> fconv
val rconj_fconv: fconv -> fconv
val rdimp_fconv: fconv -> fconv
val rdisj_fconv: fconv -> fconv
val redepth_fconv: conv -> fconv -> fconv
val refl_fconv: string list -> fconv
val repeatfc: fconv -> fconv
val right_imp_forall_fconv: fconv
val rimp_fconv: fconv -> fconv
val rpred_fconv: conv -> fconv
val sub_fconv: conv -> fconv -> fconv
val sym_fconv: fconv
val taut_conj_fconv: fconv
val taut_dimp_fconv: fconv
val taut_disj_fconv: fconv
val taut_fconv: fconv
val taut_imp_fconv: fconv
val top_depth_fconv: conv -> fconv -> fconv
val try_fconv: fconv -> fconv
val exists_fconv: (form -> thm) -> form -> thm
val forall_fconv: (form -> thm) -> form -> thm
val uex_fconv: (form -> thm) -> form -> thm


end
