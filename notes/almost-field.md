# Almost Field Theory for HGReal

## Why HGReal isn't a Field
`HGReal = Lex(AddMonoidAlgebra ℝ ℤ)` — finite Laurent polynomials. Elements like
`(1+ε)` have no exact inverse because `(1+ε)⁻¹ = 1 - ε + ε² - ...` is infinite.

## Why HGReal isn't a Local Ring or Valuation Ring
`(1+ε)/2 + (1-ε)/2 = 1` but neither summand is a unit (both have 2+ terms).
Local ring requires: `a + b = 1 ⟹ a or b is a unit`. Violated.

## What HGReal IS
- **CommRing** with **LinearOrder** (lex on indices) — fully proved
- **Integral domain** (no zero divisors in AddMonoidAlgebra ℝ ℤ)
- **AlmostField**: every nonzero element has inverse to arbitrary precision
- The **fraction field** (Laurent series) is a true valued field

## AlmostField Class
```
class AlmostField (R : Type*) [CommRing R] where
  negligible : R → ℕ → Prop
  negligible_mono : m ≤ n → negligible x n → negligible x m
  approx_inv : ∀ a ≠ 0, ∀ n, ∃ b, negligible (a * b - 1) n
```

## Related Mathematical Concepts
1. **Almost mathematics** (Faltings, Gabber-Ramero) — ring ops mod negligible ideal
2. **Topological rings / valued fields** — completion gives exact inverses
3. **Henselian rings** — lift approximate inverses to better ones
4. **Valuation rings** — HGReal's fraction field has natural ℤ-valuation

## Key Theorems
All proved (0 sorry) unless noted:
- `HG_geom_identity`: `(1+ε) · ∑(-ε)^k = 1 - (-ε)^n`
- `HG_one_add_ε_approx_inv`: `(1+ε) · partialInv(n) ≈ₕ 1`
- `HG_one_add_ε_approx_order`: `(1+ε) · partialInv(n) ≈[n] 1`
- `HG_neg_ε_pow_infinitesimal`: remainder is infinitesimal
- `support_pow_lower_bound`: support(x^n) ⊆ {k≥n} if support(x) ⊆ {k≥1}
- `HG_infinitesimal_pow_negligible`: δ infinitesimal → δ^n negligible at order n
- `HG_approxInv_negligible`: a·approxInv(a,n) - 1 negligible at order n
- `instance AlmostField HGReal`: fully wired up

## Remaining Sorry
`HG_factor_infinitesimal`: every nonzero a factors as monomial·(1+δ) with δ infinitesimal.
Needs: Finsupp.support_single_mul_eq_image to shift support by leading index,
then Finset.min' to show minimum shifts to 0, then subtract 1 to get positive-index only.
Routine Finsupp manipulation, not mathematical content.
