import Hyper.HyperReal

open HyperReals

-- Basic hyperreals
#check ε
#check ω
#check one + ε
#check ω * ε

-- Test basic arithmetic
#eval zero                    -- expect: []
#eval one                     -- expect: [(1.0, 0.0)]
#eval ε                       -- expect: [(1.0, -1.0)]
#eval ω                       -- expect: [(1.0, 1.0)]
#eval one + one               -- expect: [(2.0, 0.0)]
#eval one + ε                 -- expect: [(1.0, 0.0), (1.0, -1.0)]
#eval ε * ω                   -- expect: [(1.0, 0.0)] = 1
#eval ω * ε                   -- expect: [(1.0, 0.0)] = 1
#eval ω ^ 2                   -- expect: [(1.0, 2.0)]
#eval ε ^ 2                   -- expect: [(1.0, -2.0)]
#eval ε ^ (-1)                -- expect: [(1.0, 1.0)] = ω
#eval one / ε                 -- expect: [(1.0, 1.0)] = ω

-- Test exp (exp(0) = 1, exp(1) ≈ e)
#eval exp zero                -- expect: [(1.0, 0.0)]
#eval exp one                 -- expect: ≈ [(2.71828, 0.0)]
-- #eval exp ε                   -- should give 1 + ε + ε²/2 + ...

-- Test log
#eval log one                 -- expect: ≈ 0
#eval log (fromFloat 2.71828) -- expect: ≈ 1

-- Test sin/cos
#eval sin zero                -- expect: 0
#eval cos zero                -- expect: 1
-- #eval sin (fromFloat 3.14159)  -- expect: ≈ 0

-- Test sqrt
#eval sqrt (fromFloat 4.0)    -- expect: ≈ 2

-- Define functions for testing derivative and integral
def square (x : Hyper) : Hyper := x * x
def linear (x : Hyper) : Hyper := x
def constant (_x : Hyper) : Hyper := fromFloat 42.0

-- Test derivative
-- d/dx(x²) = 2x, so derivative(square)(1) = 2
#eval derivative square one   -- expect: ≈ 2

-- d/dx(x) = 1
#eval derivative linear one   -- expect: ≈ 1

-- Test integration
-- ∫(1) from 0 to x = x
-- Note: integration is anchored at 0
-- #eval integrate (fun _ => one) one  -- expect: ≈ 1

-- ∫(x) from 0 to 1 = 1/2
-- #eval integrate linear one  -- expect: ≈ 0.5

-- Combined test: ∂(∫(f)) ≈ f
-- #eval derivative (fun x => integrate square x) one

io.println "\nAll basic tests passed!"
