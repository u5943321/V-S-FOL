structure Portable =
struct

fun f $ x = f x;
fun fst (a,b) = a
fun snd (a,b) = b

fun zip l1 l2 = ListPair.zip(l1,l2)

fun mem x [] = false
  | mem x (h::t) = x = h orelse mem x t

(* counts from 1!!! *)
fun el _ [] = raise Fail "el: on empty list"
  | el 1 (h::t) = h
  | el n (h::t) = el (n - 1) t

fun curry f x y = f(x,y)

fun total f x = SOME (f x) handle Fail _ => NONE

fun mapfilter f = List.mapPartial (total f)

fun op_mem eq_func i = List.exists (eq_func i)

fun op_insert eq_func =
   let
      val mem = op_mem eq_func
   in
      fn i => fn L => if (mem i L) then L else i :: L
   end

fun op_mk_set eqf =
   let
      val insert = op_insert eqf
      fun mkset [] = []
        | mkset (a :: rst) = insert a (mkset rst)
   in
      mkset
   end

fun op_union eq_func =
   let
      val mem = op_mem eq_func
      val insert = op_insert eq_func
      fun un [] [] = []
        | un a [] = a
        | un [] a = a
        | un (a :: b) c = un b (insert a c)
   in
      un
   end

end
