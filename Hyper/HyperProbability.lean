/-
  A general dimensional hierarchy for hyperreal probability.
  =============================================================

  `Hyper/DartPointProbZero.lean` proves two concrete instances — a point
  (codimension 2 in a disc) has probability `ε²/A`, a line (codimension 1)
  has probability `L·ε/A` — and that the line strictly beats the point. This
  file generalizes both to arbitrary codimension `k`, proving the pattern
  once instead of once per shape.

  See `notes/hyperreal-probability-foundations.md` for the full design
  discussion this formalizes a fragment of: why codimension-indexed
  infinitesimal orders can stand in for a measure altogether, and what's
  still missing (expectation via a general Riemann-sum `∑`/`∫`, conditional
  probability across mixed-order events, σ-algebras/Loeb measure if and only
  if you want to push a result back down to classical probability via `st`).
-/
import Hyper.DartPointProbZero

namespace Hypers
namespace HyperLists

-- ═══════════════════════════════════════════════════════════════════════════
-- εᵏ by repeated multiplication (independent of `Field R*`'s `^`, same
-- reasoning as `Hyper/HyperTranscendental.lean`'s `hpow`).
-- ═══════════════════════════════════════════════════════════════════════════

/-- `x ^ n` by repeated multiplication. -/
def hpow (x : R*) : ℕ → R*
  | 0 => 1
  | (n + 1) => x * hpow x n

lemma hpow_epsilon (n : ℕ) : hpow ε n = ([(1, -(n : 𝔽))] : R*) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ε * hpow ε n = _
    rw [ih]
    show normalize (([(1, -1)] : List (𝔽 × 𝔽)).product [(1, -(n : 𝔽))] |>.map _) = _
    push_cast
    norm_num [normalize, simplify, mergeAdjacent, List.product]

-- ═══════════════════════════════════════════════════════════════════════════
-- The general "atom mass": a codimension-`k` region of ordinary content `c`
-- (a length, an area, a count — whatever `c` measures in the ambient ordinary
-- geometry), inside an ambient space of total measure `A`, gets hyperreal
-- probability `c · εᵏ / A`.
-- ═══════════════════════════════════════════════════════════════════════════

/-- `regionMass 1 2` is `pointMass` (a point has codimension 2 in a disc);
    `regionMass L 1` is `lineMass L` (a line has codimension 1). -/
def regionMass (c : 𝔽) (k : ℕ) (A : 𝔽) : R* := embedQ c * hpow ε k * (embedQ A)⁻¹

lemma embedQ_mul_hpow_epsilon {c : 𝔽} (hc : c ≠ 0) (k : ℕ) :
    embedQ c * hpow ε k = ([(c, -(k : 𝔽))] : R*) := by
  rw [hpow_epsilon]
  show normalize (([(c, 0)] : List (𝔽 × 𝔽)).product [(1, -(k : 𝔽))] |>.map _) = _
  simp [normalize, simplify, mergeAdjacent, List.product, hc]

lemma regionMass_eq {c A : 𝔽} (k : ℕ) (hc : c ≠ 0) (hA : A ≠ 0) :
    regionMass c k A = ([(c * A⁻¹, -(k : 𝔽))] : R*) := by
  show embedQ c * hpow ε k * (embedQ A)⁻¹ = _
  rw [embedQ_mul_hpow_epsilon hc, embedQ_inv hA]
  show normalize (([(c, -(k : 𝔽))] : List (𝔽 × 𝔽)).product [(A⁻¹, 0)] |>.map _) = _
  simp [normalize, simplify, mergeAdjacent, List.product, hc, inv_ne_zero hA]

-- `regionMass` unifies `pointMass`/`lineMass` as its `k = 2` / `k = 1` cases.
example : regionMass 1 2 1 = pointMass 1 := by
  rw [regionMass_eq 2 one_ne_zero one_ne_zero, pointMass_eq one_ne_zero]; norm_num
example (L A : 𝔽) (hL : L ≠ 0) (hA : A ≠ 0) : regionMass L 1 A = lineMass L A := by
  rw [regionMass_eq 1 hL hA, lineMass_eq hL hA]; norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- The dimensional hierarchy, in full generality.
-- ═══════════════════════════════════════════════════════════════════════════

/-- A higher-codimension region is *strictly less probable* than a
    lower-codimension one, however much bigger its ordinary content `c` is —
    no amount of standard-real content outweighs one extra order of
    infinitesimal smallness. `point_lt_line` (`Hyper/DartPointProbZero.lean`)
    is the `k₁ = 2, k₂ = 1` case of this. -/
theorem regionMass_mono {c₁ c₂ A : 𝔽} {k₁ k₂ : ℕ} (hk : k₂ < k₁)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hA : 0 < A) :
    regionMass c₁ k₁ A < regionMass c₂ k₂ A := by
  have hc₁A : (0 : 𝔽) < c₁ * A⁻¹ := mul_pos hc₁ (inv_pos.mpr hA)
  have hc₂A : (0 : 𝔽) < c₂ * A⁻¹ := mul_pos hc₂ (inv_pos.mpr hA)
  have hlt : -(k₁ : 𝔽) < -(k₂ : 𝔽) := by exact_mod_cast (neg_lt_neg_iff.mpr (by exact_mod_cast hk))
  have hab : regionMass c₁ k₁ A - regionMass c₂ k₂ A
      = ([(-(c₂ * A⁻¹), -(k₂ : 𝔽)), (c₁ * A⁻¹, -(k₁ : 𝔽))] : R*) := by
    rw [regionMass_eq k₁ hc₁.ne' hA.ne', regionMass_eq k₂ hc₂.ne' hA.ne']
    show merge ([(c₁ * A⁻¹, -(k₁ : 𝔽))] : R*) (Neg.neg ([(c₂ * A⁻¹, -(k₂ : 𝔽))] : R*)) = _
    show simplify (([(c₁ * A⁻¹, -(k₁ : 𝔽))] : List (𝔽 × 𝔽)) ++ [(-(c₂ * A⁻¹), -(k₂ : 𝔽))]) = _
    have := (simplify_pair (r₁ := -(c₂ * A⁻¹)) (r₂ := c₁ * A⁻¹) (e₁ := -(k₂ : 𝔽)) (e₂ := -(k₁ : 𝔽))
      hlt (neg_ne_zero.mpr hc₂A.ne') hc₁A.ne').2
    simpa using this
  exact lt_of_lead_pair hab hlt (neg_ne_zero.mpr hc₂A.ne') hc₁A.ne' (neg_neg_of_pos hc₂A)

-- Two sanity instances beyond point/line: a codim-3 "sub-point" (an even
-- rarer event than a point) loses to a point regardless of content, and
-- content genuinely can't compensate for a codimension gap even when it's
-- lopsided in the "wrong" direction (content 3 vs content 1).
example : regionMass 1 3 1 < regionMass 1 2 1 := regionMass_mono (by norm_num) one_pos one_pos one_pos
example : regionMass 3 2 5 < regionMass 1 1 5 :=
  regionMass_mono (by norm_num) (by norm_num) one_pos (by norm_num)

end HyperLists
end Hypers
