import Hyper.HyperReal
open HyperReals

-- Directly compute what cos(0) should give
-- It starts with sum=zero, adds terms

#eval! cos (fromFloat 0.1)  -- Try non-zero
#eval! sin (fromFloat 0.1)  
