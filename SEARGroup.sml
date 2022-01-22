val Assoc_def = define_pred
“!A m:A * A ~>A. Assoc(m) <=> 
 !a1 a2 a3. App(m,Pair(App(m,Pair(a1,a2)),a3)) = 
App(m,Pair(a1,App(m,Pair(a2,a3))))”


val Grp0_def = define_pred
“!G e:mem(G) m: G * G ~> G i:G ~>G. 
 Grp0(G,e,m,i) <=> Assoc(m) & 
 (!x. App(m,Pair(x,e)) = x & App(m,Pair(e,x)) = x) &
 ”







(*define topspace type to be 
 a set, and a function Pow(X) -> 2, or a mono to Pow(X). or an element of Pow(Pow(X)).

 a topospace is a mono to Pow(X).

there is a biginter function Pow(Pow(X)) -> Pow(X)

 a presheaf is a function that associate each mem of the domain of the mono a set, and hence associate the mono with a family of sets. 

so 

Psh(OX:Opens >--> Pow(X), B--> W)
*)
