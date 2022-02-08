signature Net = 
sig
type 'a tnet
val empty: 'a tnet
val match: term -> 'a tnet -> 'a list
val tinsert: term * 'a -> 'a tnet -> 'a tnet
type 'a fnet
val fempty: fconv fnet
val fmatch: form -> fconv fnet -> fconv list
val finsert: form * fconv -> fconv fnet -> fconv fnet
end
