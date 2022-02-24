
exception Interrupt = SML90.Interrupt;
use "Binarymap.sig";
use "Binarymap.sml";
use "Binaryset.sig";
use "Binaryset.sml";
use "Redblackset.sig";
use "Redblackset.sml";
use "HOLPP.sig";
use "HOLPP.sml";
use "UTF8.sig";
use "UTF8.sml";
use "smpp.sig";
use "smpp.sml";
use "HOLset.sig";
use "HOLset.sml";

infixr 1 $ ?;
infix |> >> |>> ||->;
infix 3 ##;
use "Portable.sml";
open Portable;

use "AList.sig";
use "AList.sml";
use "Table.sml";
use "Graph.sml";
use "SymGraph.sml";
type 'a set = 'a HOLset.set;


use "term.sig";
use "term.sml";
open term;


use "form.sig";
use "form.sml";
open form;



use "logic.sig";
use "logic.sml";
open logic;


use "pp.sig";
use "pp.sml";
open pp;




use "token.sig";
use "token.sml";
open token;

use "pterm_dtype.sml";
open pterm_dtype;

(*
use "parser.sig";
use "parser.sml";
open parser;
*)


use "drule.sig";
use "drule.sml";
open drule;


use "infixes.sml";
use "abbrev.sig";
use "abbrev.sml";
open abbrev;


use "conv.sig"; 
use "conv.sml";
open conv;

use "Net.sig"; 
use "Net.sml";
open Net;



use "tactic.sig";
use "tactic.sml";
open tactic;
 

use "parser.sig";
use "parser.sml";
open parser;



use "goalstack.sig";
use "goalstack.sml";
open goalstack;

use "iffLR.sml";
use "irule_canon.sml";


use "Q.sig";
use "Q.sml";
open Q;

use "History.sig";
use "History.sml";
use "proofmanager.sml";


(*Binarymap HOL/tools-poly/poly 
 smpp src/portableML 
 HOLset  RedBlackset  src/portableML  
 UTF8 portableML*)
