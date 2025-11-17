import Hyper.HyperReal
open HyperReals

partial def cosDebug (x : Hyper) : Hyper :=
  let rec cosHelper (n : Nat) (sum : Hyper) : IO Hyper := do
    if n >= 3 then  -- Just do 3 terms for debug
      return sum
    else
      let sign := if n % 2 == 0 then 1.0 else -1.0
      let power := ipow x (2 * n)
      let fact := factorial (2 * n)
      IO.println s!"n={n}, sign={sign}, power={repr power}, fact={fact}"
      let term := (fromFloat sign * power) / fromNat fact
      IO.println s!"  term={repr term}, sum so far={repr sum}"
      cosHelper (n + 1) (sum + term)
  unsafeIO (cosHelper 0 zero)

#eval! cosDebug zero
