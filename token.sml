structure token :> token =
struct 
datatype token = Key of string | Id of string;


(*new stuff *)
exception TER of string

fun is_char(l,i,u) = l <= i andalso i <= u;

(*fun is_symbol c = 
let val cl = List.map ord [#"=",#"<",#">",#"-",#":",#"*",#"(",#")"]
in  mem c cl
end
*)


(*
 [] {} (*  *) make

<<a,b>,c>

Key "<" Key "<"

2 (( lexer see it and generate 2 tokens "(" and "(", not "(("

but if see aaa, will just gen Id"aaa"


Key "{" Key "=" =+" 

Key "{" Key"=+"

==> 
<=> 



*)

val letter_or_digits0 = HOLset.empty Int.compare

val letter_or_digits = ref letter_or_digits0

fun add_range (a,b) s = 
    if b < a then raise TER "add_range.bad input" else
        if a = b then HOLset.add(s,b)
        else let val s0 = HOLset.add(s,a)
             in add_range (a + 1,b) s0
             end

fun add_parse c = letter_or_digits := HOLset.add(!letter_or_digits,c)

fun add_parse_range (a,b) =letter_or_digits := add_range (a,b) (!letter_or_digits)


(*
fun letter_or_digit0 c = 
    is_char(ord #"A",c,ord #"Z") orelse is_char(ord #"a",c,ord #"z") orelse is_char(ord #"0",c,ord #"9") orelse
    is_char(913,c,937) orelse is_char(945,c,969) orelse is_char(8320,c,8329) orelse 
    c = 0x00B9 orelse c = 0x00B2 orelse c = 0x00B3 orelse is_char(0x2074,c,0x2079) orelse 
    c = ord #"'" orelse c = ord #"_";

val letter_or_digit = ref letter_or_digit0;


fun add_parsable c = 
    let val _ = letter_or_digit := (fn c0 => !letter_or_digit c0 orelse c0 = c)
    in () end

*)

(*
fun is_letter_or_digit c =
    is_char(ord #"A",c,ord #"Z") orelse is_char(ord #"a",c,ord #"z") orelse is_char(ord #"0",c,ord #"9") orelse
    is_char(913,c,937) orelse is_char(945,c,969) orelse is_char(8320,c,8329) orelse 
    c = 0x00B9 orelse c = 0x00B2 orelse c = 0x00B3 orelse is_char(0x2074,c,0x2079) orelse 
    c = ord #"'" orelse c = ord #"_";

*)

fun int_of s = 
    case UTF8.getChar s of 
        NONE => raise TER "int_of.empty string"
      | SOME ((_,n),_) => n

val _ = add_parse_range (ord #"A",ord #"Z")
val _ = add_parse_range (ord #"a",ord #"z")
val _ = add_parse_range(ord #"0",ord #"9")
val _ = add_parse_range(913,937) 
val _ = add_parse_range(945,969) 
val _ = add_parse_range(8320,8329) 
val _ = add_parse 0x00B9 
val _ = add_parse 0x00B2
val _ = add_parse 0x00B3 
val _ = add_parse_range(0x2074,0x2079)
val _ = add_parse (ord #"'")
val _ = add_parse (ord #"_");

val _ = add_parse (int_of "∀");
val _ = add_parse (int_of "∃");
val _ = add_parse (int_of "⇔");
val _ = add_parse (int_of "∨");
val _ = add_parse (int_of "∧");
val _ = add_parse (int_of "⇒");


fun is_letter_or_digit c = HOLset.member(!letter_or_digits,c)



fun token_of a = if mem a ["o","!","?","?!","==>","<=>",":","->","(*","*)","==","=>"] then (Key a) else (Id a); 

fun getN s n = 
    if n <= 0 then ([], s)
    else case UTF8.getChar s of
             NONE => ([], s)
           | SOME ((cs,_), s') =>
             let val (css, s'') = getN s' (Int.-(n ,1))
             in
                 (cs::css, s'')
             end

(*

(* abcde*) P(a) <=> Q(c)

PQ(A) 

"==="




*)(*string list * string -> token * string*)



(*discard the comment (* *) symbols and do not scan them as key (*, 
 and make the comment depth stuff here. *)
 *)


(*
fun scan_symbol s = 
    let 
        val (l1,s1) = getN s 1
        val (l2,s2) = getN s 2
        val (l3,s3) = getN s 3
        val syml = 
            ["=","<",">","-",":","*","(",")","|","&","~"]
    in 
        if l3 = ["=","=",">"] then (Key "==>",s3) else
        if l3 = ["<","=",">"] then (Key "<=>",s3) else
        if l2 = ["(","*"] then eat_comment 1 s2    else    
        if l2 = ["-",">"] then (Key "->",s2) else
        if l2 = ["=","="] then (Key "==",s2) else
        if l2 = ["?","!"] then (Key "?!",s2) else
        if mem (List.hd l1) syml then (Key $ List.hd l1,s1) else
        raise TER "no symbol detected"(*(Id (List.hd l1),s)*)
    end
and eat_comment n str = 
    let val (l1,s1) = getN str 1
        val (l2,s2) = getN str 2 
    in if l2 = ["(","*"] then eat_comment (n + 1) s2 
       else if l2 = ["*",")"] then 
           if n = 1 then scan_symbol s2
           else eat_comment (Int.-(n,1)) s2
       else eat_comment n s1
    end  
 
*)
(* lex "P (* a*) + Q";
val it = [Id "P", Key "+", Id "Q"]: token list

 lex "P (* a*) * Q";
val it = [Id "P", Key "*", Id "Q"]: token list

old scan symbol can do
*)
(*
fun scan_symbol (front, s) =
    case UTF8.getChar s of 
        NONE => 
        (token_of (String.concat $ rev front),s)
      | SOME ((s0,i),rest) => 
        if is_symbol i then 
            scan_symbol (s0 :: front,rest)
        else 
            (token_of (String.concat $ rev front),s)
*)


fun scan_ident (front, s) =
    case UTF8.getChar s of 
        SOME ((s0,i),rest) => 
        if mem s0 [" ","\n","\t"] andalso front = [] then
            scan_ident (front,rest)
        else
            (case UTF8.getChar s of 
                 NONE => 
                 (token_of (String.concat $ rev front),s)
               | SOME ((s0,i),rest) => 
                 if is_letter_or_digit i then 
                     scan_ident (s0 :: front,rest)
                 else 
                     (case getN s 2 of 
                          (["(","*"],s1) => eat_id_comment 1 s1
                        | _ => 
                          if front = [] then raise TER "scan_ident.generating empty token"
                          else (token_of (String.concat $ rev front),s)))
      | _ => if front = [] then raise TER "scan_ident.generating empty token"
             else (token_of (String.concat $ rev front),s)
and eat_id_comment n str = 
    let val (l1,s1) = getN str 1
        val (l2,s2) = getN str 2 
    in if l2 = ["(","*"] then eat_id_comment (n + 1) s2 
       else if l2 = ["*",")"] then 
           if n = 1 then scan_ident ([],s2)
           else eat_id_comment (Int.-(n,1)) s2
       else eat_id_comment n s1
    end  


fun scan_symbol s = 
    case UTF8.getChar s of 
        SOME ((s0,i),rest) => 
        if mem s0 [" ","\n","\t"] then
            scan_symbol rest
        else
            let 
                val (l1,s1) = getN s 1
                val (l2,s2) = getN s 2
                val (l3,s3) = getN s 3
                val syml = 
                    ["=","<",">","-",":","*","+","⟨","⟩","[","]","(",")","!","?",".","|","&","~",",","⇔","⇒","∧","¬","∨","∀","∃","@"]
            in 
                if l3 = ["=","=",">"] then (Key "==>",s3) else
                if l3 = ["<","=",">"] then (Key "<=>",s3) else
                if l2 = ["(","*"] then eat_comment 1 s2    else    
                if l2 = ["-",">"] then (Key "->",s2) else
                if l2 = ["~",">"] then (Key "~>",s2) else
                if l2 = ["=","="] then (Key "==",s2) else
                if l2 = ["=",">"] then (Key "=>",s2) else
                if l2 = ["?","!"] then (Key "?!",s2) else
                if l2 = ["∃","!"] then (Key "?!",s2) else
                if l1 = ["∧"] then (Key "&",s1) else
                if l1 = ["∨"] then (Key "|",s1) else
                if l1 = ["⇒"] then (Key "==>",s1) else
                if l1 = ["⇔"] then (Key "<=>",s1) else
                if l1 = ["¬"] then (Key "~",s1) else
                if l1 = ["∀"] then (Key "!",s1) else
                if l1 = ["∃"] then (Key "?",s1) else
                if mem (List.hd l1) syml then (Key $ List.hd l1,s1) else
                raise TER "no symbol detected"(*(Id (List.hd l1),s)*)
            end 
      | _ => raise TER "scan_symbol.unexpected end of string"
and eat_comment n str = 
    let val (l1,s1) = getN str 1
        val (l2,s2) = getN str 2 
    in if l2 = ["(","*"] then eat_comment (n + 1) s2 
       else if l2 = ["*",")"] then 
           if n = 1 then scan_symbol s2
           else eat_comment (Int.-(n,1)) s2
       else eat_comment n s1
    end  


fun scan (front_toks,s) = 
    if can scan_symbol s then 
        let val (tok,rest) = scan_symbol s
        in scan(tok :: front_toks,rest)
        end
    else if can scan_ident ([],s) then
        let val (tok,rest) = scan_ident ([],s)
        in scan(tok :: front_toks,rest)
        end
    else rev front_toks


fun enclose a = "(" ^ a ^ ")";

fun tokentoString tok = 
    case tok of 
        Key s => "Key" ^ enclose s
      | Id s => "Id" ^ enclose s

fun lex s = scan ([],s)



end

