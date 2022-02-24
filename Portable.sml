structure Portable =
struct

(* function application *)
fun I x = x
fun C f x y = f y x
fun K x y = x

fun f $ x = f x
fun x |> f = f x
fun total f x = SOME (f x) handle Interrupt => raise Interrupt | _ => NONE
fun can f x = (ignore (f x); true) handle Interrupt => raise Interrupt | _ => false
fun (b ? f) x = if b then f x else x
fun funpow n f arg = 
    case n of 0 => arg
            | _ => funpow (n - 1) f (f arg) 



(* pairs *)
fun fst (a,b) = a
fun snd (a,b) = b
fun curry f x y = f(x,y)
fun uncurry f(x,y) = f x y
fun pair x y = (x,y)
fun apfst f (x,y) = (f x, y)
fun apsnd f (x,y) = (x, f y)
fun (x,y) |>> f = (f x, y)
fun (x,y) ||-> f = f x y
fun (f ## g) (x, y) = (f x, g y)


(* lists *)
fun mem x [] = false
  | mem x (h::t) = x = h orelse mem x t
fun filter_out P = List.filter (not o P)

(* counts from 1!!! *)
fun el _ [] = raise Fail "el: on empty list"
  | el 1 (h::t) = h
  | el n (h::t) = el (n - 1) t

fun these (SOME x) = x | these NONE = []
fun zip l1 l2 = ListPair.zip(l1,l2)

fun mapfilter f = List.mapPartial (total f)
fun cons x y = x::y

fun foldl' f L A =
    let fun recurse L A =
            case L of
                [] => A
              | h::t => recurse t (f h A)
    in
      recurse L A
    end
val rev_itlist = foldl'

fun foldr' f L A =
    let fun recurse L =
            case L of
                [] => A
              | h::t => f h (recurse t)
    in
      recurse L
    end
val itlist = foldr'
fun append l1 l2 = l1 @ l2
fun assoc1 item =
   let
      fun assc ((e as (key, _)) :: rst) =
            if item = key then SOME e else assc rst
        | assc [] = NONE
   in
      assc
   end
val flatten = List.concat

fun first_opt f =
   let
      fun fo n [] = NONE
        | fo n (a :: rst) =
            let
               val vo = f n a handle Interrupt => raise Interrupt | _ => NONE
            in
               if isSome vo then vo else fo (n + 1) rst
            end
   in
      fo 0
   end

fun pluck P =
   let
      fun pl _ [] = raise Fail "pluck: predicate not satisfied"
        | pl A (h :: t) =
            if P h then (h, List.revAppend (A, t)) else pl (h :: A) t
   in
      pl []
   end

fun split_after n list =
   if n >= 0
      then let
              fun spa 0 (L, R) = (rev L, R)
                | spa n (L, a :: rst) = spa (n - 1) (a :: L, rst)
                | spa _ _ = raise Fail "split_after: index too big"
           in
              spa n ([], list)
           end
   else raise Fail "split_after: negative index"


fun mapshape [] _ _ =  []
  | mapshape (n :: nums) (f :: funcs) all_args =
     let
        val (fargs, rst) = split_after n all_args
     in
        f fargs :: mapshape nums funcs rst
     end
  | mapshape _ _ _ = raise Fail "mapshape: irregular lists"


(* lists as sets, with explicit equality functions as parameters *)
fun op_mem eq_func i = List.exists (eq_func i)
fun op_remove eq x list =
  if op_mem eq x list then
    List.filter (fn y => not (eq x y)) list
  else list
fun op_update eq x xs = x :: op_remove eq x xs

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

(* strings *)
fun mlquote s = "\"" ^ String.toString s ^ "\""

val pointer_eq = Systeml.pointer_eq

end
