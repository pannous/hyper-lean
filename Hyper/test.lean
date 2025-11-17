import Hyper.HyperReal

open HyperReals

-- Test basic operations
#eval zero
#eval one
#eval ε
#eval ω
#eval one + one
#eval one + ε
#eval ε * ω
#eval ω * ε
#eval ω ^ 2
#eval ε ^ 2
#eval ε ^ (-1)
#eval one / ε

-- Test exp
#eval exp zero
#eval exp one

-- Test sin/cos
#eval sin zero

-- Derivative test
def square (x : Hyper) : Hyper := x * x
#eval derivative square one
