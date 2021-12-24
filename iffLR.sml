fun eq_imp_rule th = (dimpl2r th,dimpr2l th)

datatype AI = imp of form | fa of {orig:string * sort, new:string * sort}


fun spec t = specl [t]

fun AIdestAll th =
    case total dest_forall (concl th) of
        NONE => NONE
      | SOME ((n,s),b) =>
        let
          val hfvs = fvfl (ant th)
        in
          if HOLset.member(hfvs, (n,s)) then
            let val new = dest_var (pvariantt hfvs (mk_var(n,s)))
            in
              SOME (fa{orig=(n,s),new=new}, spec (mk_var new) th)
            end
          else
            SOME (fa{orig=(n,s),new=(n,s)}, spec (mk_var(n,s)) th)
        end




fun all_rename x f = 
    case view_form f of
        vQ("!",n,s,b) =>
        let 
            val l2r =  assume f |> allE (mk_var(x,s)) |> allI (x,s) |> disch_all
            val r2l =  assume (mk_forall x s b) |> allE (mk_var(n,s)) |> allI (n,s) |> disch_all
        in dimpI l2r r2l
        end
      | _ => raise ERR ("all_rename.not a forall",[],[],[f])


fun restore hs (acs, th) =
    case acs of
        [] => rev_itlist add_assum hs th
      | imp t :: rest => restore hs (rest, disch t th)
      | fa{orig,new} :: rest =>
        if fst orig = fst new andalso eq_sort(snd orig,snd new) then
          restore hs (rest, allI orig th)
        else
          restore hs (rest, th |> allI new |> conv_rule (all_rename (fst orig)))
 

fun underAIs f th =
    let
      fun getbase A th =
          case AIdestAll th of
              NONE => (case total dest_imp (concl th) of
                           NONE => (A, f th)
                         | SOME (l,r) => getbase (imp l :: A) (undisch th))
            | SOME (act,th') => getbase (act::A) th'
    in
      restore (ant th) (getbase [] th)
    end

val iffLR = underAIs (#1 o eq_imp_rule)
val iffRL = underAIs (#2 o eq_imp_rule)



fun strip_all_and_imp th = 
    if is_forall (concl th) then 
        strip_all_and_imp (spec_all th)
    else if is_imp (concl th) then 
        strip_all_and_imp (undisch th)
    else th
