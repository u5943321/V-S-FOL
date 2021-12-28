(*
To define a rel by recursion.
P(a0,b0) <=> R(a0,b0) & 
(!a b. P(a,b) ==> !a' b'. Q(a,b,a',b') ==> 
 P(a',b'))

!a b. P(a,b) <=>
 !ss. (R(a0,b0) <=> IN(Pair(a0,b0),ss)) &
      !a1 b1. IN(Pair(a1,b1),ss) ==>
      !a1' b1'. Q(a1,b1,a1',b1') ==> 
      IN(Pair(a1',b1'),ss)


P_ind
ind principle:
((R(a0,b0) ==> P1(a0,b0)) &
!a b. P1(a,b) ==> 
  !a' b'. Q(a,b,a',b') ==> P1(a',b')) ==>
!a b. P(a,b) ==> P1(a,b)

P_rules:

(R(a0,b0) ==> P(a0,b0)) & 
!a b. P(a,b) ==> 
 !a' b'.Q(a,b,a',b') ==> P(a',b')


P_cases:

!a b. P(a,b) <=> 
 (R(a,b)) |
 ?a0 b0. Q(a0,b0,a,b) & P(a0,b0)


*)
