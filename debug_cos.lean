import Hyper.HyperReal
open HyperReals

-- Manually compute first term of cos(0)
-- cos(x) = 1 - x²/2! + x⁴/4! - ...
-- First term: (-1)^0 * 0^0 / 0! = 1 * 1 / 1 = 1

def testTerm : Hyper :=
  let x := zero
  let n := 0
  let sign := if n % 2 == 0 then 1.0 else -1.0  -- 1.0
  let power := ipow x (2 * n)  -- 0^0
  let fact := 1  -- 0!
  let term := (fromFloat sign * power) / fromNat fact
  term

#eval! testTerm
#eval! ipow zero 0
#eval! fromNat 1
#eval! (fromFloat 1.0 * ipow zero 0) / fromNat 1
