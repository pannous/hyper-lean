import Hyper.HyperList

/-!
Simple evals for the concrete `HyperList` (`R*`) model: basic arithmetic on
`ε`/`ω`, order, and `#eval`-visible normal forms. Intended as a quick,
readable smoke test — deeper structural facts belong in `HyperListBasics.lean`
and the theory-level probes in `EvalsAdvanced.lean`.
-/

open Hypers

namespace Hypers.HyperLists.Probes.Simple

-- ═══════════════════════════════════════════════════════════════════════════
-- #eval: visible normal forms
-- ═══════════════════════════════════════════════════════════════════════════

#eval (ε : R*)                 -- [(1, -1)]
#eval (ω : R*)                 -- [(1, 1)]
#eval (ε * ω : R*)              -- 1
#eval (ε + ω : R*)              -- ε + ω, unsimplified to a single monomial
#eval (ε + ε + ε : R*)          -- 3ε
#eval ((3 : R*) * ε)            -- 3ε
#eval (ε - ε : R*)              -- 0
#eval (ω * ω * ε * ε : R*)      -- 1
#eval ((1 : R*) + 1 + 1)        -- 3
#eval st (ε + 5 : R*)           -- 5, standard part drops the ε

-- ═══════════════════════════════════════════════════════════════════════════
-- Arithmetic identities
-- ═══════════════════════════════════════════════════════════════════════════

example : (2:𝔽) • ε = ε + ε := by native_decide
example : (3:𝔽) • ω = ω + ω + ω := by native_decide
example : ε * ε * ω = ε := by native_decide
example : ε * ω * ω = ω := by native_decide
example : (ε + ω) - ω = ε := by native_decide
example : (ε + ω) - ε = ω := by native_decide
example : ε + ω ≠ ω := by native_decide
example : ε + ω ≠ ε := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Order
-- ═══════════════════════════════════════════════════════════════════════════

example : (0 : R*) < ε := by native_decide
example : ε < ω := by native_decide
example : ε < 1 := by native_decide
example : (1 : R*) < ω := by native_decide
example : ε * ε < ε := by native_decide
example : (0 : R*) ≤ ε := by native_decide
example : ε ≤ ε := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Standard part
-- ═══════════════════════════════════════════════════════════════════════════

example : st (ε : R*) = 0 := standard_epsilon_zero
example : st (5 + ε : R*) = 5 := by native_decide
example : st (5 - ε : R*) = 5 := by native_decide

end Hypers.HyperLists.Probes.Simple
