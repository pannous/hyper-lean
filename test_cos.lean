import Hyper.HyperReal
open HyperReals

#eval factorial 0  -- should be 1
#eval factorial 1  -- should be 1
#eval factorial 2  -- should be 2

def testCos : Hyper :=
  let x := zero
  let power := ipow x 0  -- x^0 = 1
  let fact := factorial 0  -- 0! = 1
  IO.println s!"power = {repr power}"
  IO.println s!"fact = {fact}"
  (fromFloat 1.0 * power) / fromNat fact

#eval testCos
#eval cos zero
