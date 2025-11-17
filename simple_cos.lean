import Hyper.HyperReal
open HyperReals

-- Manually compute cos(0) = 1 + 0 + 0 + ... = 1
-- Terms: 1/0!, -0²/2!, +0⁴/4!, ...

#eval! zero + one  -- Start with sum=0, add term 1
#eval! fromNat 2
#eval! fromFloat (-1.0)
#eval! ipow zero 2
#eval! (fromFloat (-1.0) * ipow zero 2) / fromNat 2  -- Should be 0
#eval! one + ((fromFloat (-1.0) * ipow zero 2) / fromNat 2)  -- Should be 1

-- Actual cos
#eval! cos zero
