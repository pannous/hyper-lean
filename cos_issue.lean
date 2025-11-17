import Hyper.HyperReal
open HyperReals

-- Check if the issue is the initial call
def cosManual : Hyper :=
  let x := zero
  -- Term 0: 1*x^0/0! = 1/1 = 1
  let t0 := (fromFloat 1.0 * ipow x 0) / fromNat 1
  -- Term 1: -1*x^2/2! = -1*0/2 = 0  
  let t1 := (fromFloat (-1.0) * ipow x 2) / fromNat 2
  -- Sum
  t0 + t1

#eval! cosManual

-- Now try a non-partial version
def cosSimple (x : Hyper) (terms : Nat) : Hyper :=
  match terms with
  | 0 => zero
  | n + 1 =>
    let prevSum := cosSimple x n
    let sign := if n % 2 == 0 then 1.0 else -1.0
    let power := ipow x (2 * n)
    let fact := factorial (2 * n)
    let term := (fromFloat sign * power) / fromNat fact
    prevSum + term

#eval! cosSimple zero 10
