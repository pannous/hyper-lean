import Hyper.HyperList

/-!
Basic sanity properties of the concrete `HyperList` (`R*`) model:
scalar multiples of `ε`/`ω`, cancellation, and simple distinctness facts.
Companion to the deeper order/gauging lemmas already proved in `HyperList.lean`.
-/

open Hypers

namespace Hypers.HyperLists.Probes

example : ε + ε = 2ε := by native_decide
example : ε + ε + ε = 3ε := by native_decide
example : (2:𝔽) • ε + ε = 3ε := by native_decide
example : ω + ω = 2ω := by native_decide
example : ω + ω + ω = 3ω := by native_decide
example : (0:𝔽) • ε = 0 := by native_decide

example : -ε + ε = 0 := by native_decide
example : ε - ε = 0 := by native_decide
example : ω - ω = 0 := by native_decide
example : ε + 0 = ε := by native_decide
example : (0:R*) + ω = ω := by native_decide

example : ε * ω = 1 := by native_decide
example : ω * ε = 1 := by native_decide
example : ε * ε * ω * ω = 1 := by native_decide

example : ε ≠ ω := by native_decide
example : ε ≠ (0:R*) := by native_decide
example : ε * ε ≠ ε := by native_decide
example : (2ε : R*) ≠ ε := by native_decide

example : (1:R*) + 1 = 2 := by native_decide
example : (2:R*) + 2 = 4 := by native_decide

end Hypers.HyperLists.Probes
