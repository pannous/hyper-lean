/-
  Rarity orders derived from algebraic hyperfinite counts.
  =======================================================

  `Hyper/DartPointProbZero.lean` proves two concrete instances — a point
  (codimension 2 in a disc) has probability `ε²/A`, a line (codimension 1)
  has probability `L·ε/A` — and that the line strictly beats the point. This
  file generalizes both to arbitrary codimension `k`, proving the pattern
  once instead of once per shape.

  See `notes/hyperreal-probability-foundations.md` for the corrected design:
  probability is a normalized symbolic count.  An event count `c·ωᵈ` inside
  a sample-space count `A·ωⁿ` yields `(c/A)·ε^(n-d)`.  The codimension formula
  below is therefore a derived algebraic pattern, not the primitive notion.
-/
import Hyper.DartPointProbZero
import Hyper.AlgebraicProbability

namespace Hypers
namespace HyperLists

open AlgebraicProbability

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
-- A uniform event with count coefficient `c` and rarity order `k`, inside a
-- sample space with normalization coefficient `A`, has probability `c·εᵏ/A`.
-- ═══════════════════════════════════════════════════════════════════════════

/-- The probability obtained after simplifying a symbolic count ratio
    `c·ωᵈ / (A·ωⁿ)`, where `k = n-d`. -/
def uniformEventProbability (c : 𝔽) (k : ℕ) (A : 𝔽) : R* :=
  embedQ c * hpow ε k * (embedQ A)⁻¹

lemma embedQ_mul_hpow_epsilon {c : 𝔽} (hc : c ≠ 0) (k : ℕ) :
    embedQ c * hpow ε k = ([(c, -(k : 𝔽))] : R*) := by
  rw [hpow_epsilon]
  show normalize (([(c, 0)] : List (𝔽 × 𝔽)).product [(1, -(k : 𝔽))] |>.map _) = _
  simp [normalize, simplify, mergeAdjacent, List.product, hc]

lemma uniformEventProbability_eq {c A : 𝔽} (k : ℕ) (hc : c ≠ 0) (hA : A ≠ 0) :
    uniformEventProbability c k A = ([(c * A⁻¹, -(k : 𝔽))] : R*) := by
  show embedQ c * hpow ε k * (embedQ A)⁻¹ = _
  rw [embedQ_mul_hpow_epsilon hc, embedQ_inv hA]
  show normalize (([(c, -(k : 𝔽))] : List (𝔽 × 𝔽)).product [(A⁻¹, 0)] |>.map _) = _
  simp [normalize, simplify, mergeAdjacent, List.product, hc, inv_ne_zero hA]

/-- The rarity-order formula is exactly the probability obtained from
    favorable count `c` and sample-space count `A·ωᵏ`. -/
theorem uniformEventProbability_from_counts {c A : 𝔽} (k : ℕ)
    (hc : c ≠ 0) (hA : A ≠ 0) :
    uniformEventProbability c k A =
      probability ⟨c, 0⟩ ⟨⟨A, k⟩, hA⟩ := by
  rw [uniformEventProbability_eq k hc hA]
  unfold probability
  rw [monomial_of_ne (mul_ne_zero hc (inv_ne_zero hA))]
  push_cast
  congr 2
  ring

-- The general count ratio specializes to the point/line Dart probabilities.
example : uniformEventProbability 1 2 1 = pointProbability 1 := by
  rw [uniformEventProbability_eq 2 one_ne_zero one_ne_zero,
    pointProbability_eq one_ne_zero]
  norm_num
example (L A : 𝔽) (hL : L ≠ 0) (hA : A ≠ 0) :
    uniformEventProbability L 1 A = lineProbability L A := by
  rw [uniformEventProbability_eq 1 hL hA, lineProbability_eq hL hA]
  norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- The dimensional hierarchy, in full generality.
-- ═══════════════════════════════════════════════════════════════════════════

/-- A higher-codimension region is *strictly less probable* than a
    lower-codimension one, however much bigger its ordinary content `c` is —
    no amount of standard-real content outweighs one extra order of
    infinitesimal smallness. `point_lt_line` (`Hyper/DartPointProbZero.lean`)
    is the `k₁ = 2, k₂ = 1` case of this. -/
theorem uniformEventProbability_rarity_order {c₁ c₂ A : 𝔽} {k₁ k₂ : ℕ}
    (hk : k₂ < k₁)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hA : 0 < A) :
    uniformEventProbability c₁ k₁ A < uniformEventProbability c₂ k₂ A := by
  have hc₁A : (0 : 𝔽) < c₁ * A⁻¹ := mul_pos hc₁ (inv_pos.mpr hA)
  have hc₂A : (0 : 𝔽) < c₂ * A⁻¹ := mul_pos hc₂ (inv_pos.mpr hA)
  have hlt : -(k₁ : 𝔽) < -(k₂ : 𝔽) := by exact_mod_cast (neg_lt_neg_iff.mpr (by exact_mod_cast hk))
  have hab : uniformEventProbability c₁ k₁ A - uniformEventProbability c₂ k₂ A
      = ([(-(c₂ * A⁻¹), -(k₂ : 𝔽)), (c₁ * A⁻¹, -(k₁ : 𝔽))] : R*) := by
    rw [uniformEventProbability_eq k₁ hc₁.ne' hA.ne',
      uniformEventProbability_eq k₂ hc₂.ne' hA.ne']
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
example : uniformEventProbability 1 3 1 < uniformEventProbability 1 2 1 :=
  uniformEventProbability_rarity_order (by norm_num) one_pos one_pos one_pos
example : uniformEventProbability 3 2 5 < uniformEventProbability 1 1 5 :=
  uniformEventProbability_rarity_order (by norm_num) (by norm_num) one_pos (by norm_num)

end HyperLists
end Hypers
