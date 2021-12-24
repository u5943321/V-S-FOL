structure pterm_dtype = 
struct

datatype psort = psrt of string * pterm list
               | psvar of string
and pterm =
          ptUVar of string
         | pVar of string * psort
         | pFun of string * psort * pterm list
         | pAnno of pterm * psort
datatype pform =
         pPred of string * pterm list
         | pConn of string * pform list
         | pQuant of string * string * psort * pform
         | pfVar of string * pterm list ;  

end


