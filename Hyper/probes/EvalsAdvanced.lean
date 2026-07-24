import Hyper.HyperList
import Hyper.HyperReal
import Hyper.DartPointProbZero

/-!
More advanced evals, exercising the theory as far as it currently reaches:

* higher-degree polynomial identities in `ε`/`ω` on the concrete `R*` model,
  beyond the single-term facts in `EvalsSimple.lean`;
* the implementation-independent `IsHyperReal` interface, resolved for the
  concrete model through `Hyper/HyperReal.lean`;
* the dart-probability theorems (`Hyper/DartPointProbZero.lean`) at parameter
  values beyond the `A = L = 1` sanity check already there.

⚠️ Deliberately NOT using the `ring` tactic here: `R*` carries two distinct
routes to `Add`/`Mul` — the direct `instance : Add R* := ⟨merge⟩` used by `+`
notation, and the separate `fieldAdd`/`fieldMul` bundled inside the `Field R*`
instance (`Hyper/HyperList.lean:931`) — an unresolved diamond (confirmed:
`ring`/`ring_nf` fails even on `x + y = y + x` because it normalizes via the
Field-bundled operations while the goal's `+` resolves to the other
instance). Every identity below is instead a closed computation over
`ε`/`ω`/rationals, settled by `native_decide` exactly like the rest of the
project's probes.
-/

open Hypers
open Hypers.HyperLists

namespace Hypers.HyperLists.Probes.Advanced

-- ═══════════════════════════════════════════════════════════════════════════
-- Higher-degree polynomial identities in ε, ω.
-- ═══════════════════════════════════════════════════════════════════════════

example : (ε + ω) * (ε + ω) = ε * ε + 2 * (ε * ω) + ω * ω := by native_decide
example : ((ε : R*) * ω) ^ 2 = 1 := by native_decide
example : (ε + 1 : R*) ^ 3 = ε * ε * ε + 3 * (ε * ε) + 3 * ε + 1 := by native_decide
example : (ω - 1 : R*) * (ω + 1) = ω * ω - 1 := by native_decide
example : (ω * ω : R*) * (ε * ε) = 1 := gauging_2d

-- ═══════════════════════════════════════════════════════════════════════════
-- IsHyperReal, resolved for the concrete HyperReal model — same theorem
-- statements as `Hyper/HyperBasics.lean`, no re-proof, pure instance search.
-- ═══════════════════════════════════════════════════════════════════════════

open IsHyperReal in
example : (eps : HyperReal) < omega := eps_lt_omega
open IsHyperReal in
example : (eps : HyperReal) * eps ≠ eps := eps_sq_ne_eps
open IsHyperReal in
example : (eps : HyperReal) + eps + eps = (1 + 1 + 1) * eps := eps_add_eps_add_eps

-- ═══════════════════════════════════════════════════════════════════════════
-- Dart probabilities at parameters beyond the A = L = 1 sanity check.
-- ═══════════════════════════════════════════════════════════════════════════

example : (0 : R*) < pointMass 4 := point_prob_pos (by norm_num)
example : (0 : R*) < lineMass 3 4 := line_prob_pos (by norm_num) (by norm_num)
example : pointMass 4 < lineMass 3 4 := point_lt_line (by norm_num) (by norm_num)
example : st (pointMass 4) = 0 := point_prob_standard_zero (by norm_num)
example : st (lineMass 3 4) = 0 := line_prob_standard_zero (by norm_num) (by norm_num)

-- A smaller region makes the same point strictly more probable — probability
-- scales as 1/A, comparing two genuinely hyperreal-valued measures.
example : pointMass 4 < pointMass 1 := by native_decide

-- Scaling the region's measure back up recovers the unit point mass —
-- `pointMass A * A = pointMass 1`, the ε²/A definition made concrete.
example : pointMass 4 * embedQ (4 : ℚ) = pointMass 1 := by native_decide

end Hypers.HyperLists.Probes.Advanced
