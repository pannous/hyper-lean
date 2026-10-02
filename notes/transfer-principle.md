# Transfer principle vs. our algebraic model

## Verdict
Keisler's full transfer (Axiom D: every real f has an extension f*, plus Axiom E)
is **false** for every model in this repo (`HyperList`, `ℝ(ε)` fraction field,
Hahn series). A **restricted transfer** is true and provable without Tarski or
ultrafilters: the *germ transfer* below.

## Why full transfer fails (concrete counterexamples)
- `∀x>0 ∃y, y² = x` holds in ℝ, but `√(1+ε)` is not a finite list / not in ℝ(ε).
- `sin(ω)`, `⌊sin ω⌋`, `exp(ω)` (> every ωⁿ) are not representable.
- Keisler's Axiom D demands an extension for *every* real function; models of that
  are not explicit (ultrapower, or Kanovei–Shelah's definable but huge construction).
- Truncated Taylor `hexp` breaks `exp(a+b)=exp a·exp b` exactly, so that equation
  does not transfer either.

## Key observation: Axiom E is only about universal sentences
"Every real solution of S is a solution of T" is `∀x⃗ (S(x⃗) → T(x⃗))`.
Keisler gets the ∀∃ facts (roots, floor, …) only via Axiom D (functions act as
Skolem functions). Drop D → you lose ∀∃, but E for universal sentences remains true.

## Germ transfer (the provable close equivalent)
Read ε as "a sufficiently small real t > 0":
`eval : R* → Germ (𝓝[>] 0) ℝ`, term `(a, e) ↦ a · t^(-e)` (ε = (1,-1), ω = (1,1)).
- It is a ring hom (rpow laws for t > 0).
- `x > 0` in R* ⟺ `eval x` eventually > 0: lowest-order term dominates, which is
  *exactly* the HyperList order. Every element has an eventually-constant sign.
- Hence every quantifier-free formula in (+,−,·,⁻¹,<, constants) is eventually
  true or eventually false, and universal sentences transfer:
  `(∀ x⃗ ∈ ℝⁿ, φ x⃗) → (∀ x⃗ ∈ R*ⁿ, φ x⃗)` for quantifier-free φ.
- Works for any extra function whose germ stays eventually signed (Hardy field):
  exp, log, √ on positives, restricted analytic functions — if the model is
  extended exactly (not by truncation) with those germs.
- Fails precisely for oscillating germs like `sin(1/t)` = `sin ω`: deciding its
  sign needs a non-principal ultrafilter. That is the exact boundary between
  "algebraic" hyperreals and Robinson/Keisler.

## Larger routes (not started)
- ℝ((ε^ℚ)) Hahn field is real closed ⇒ by Tarski ℝ ≼ it, full first-order
  transfer for ordered-field statements (incl. ∀∃). Needs RCF quantifier
  elimination — not in Mathlib v4.34.1. Noncomputable (see hahn-series-tradeoff.md).
- exp/log: transseries (van den Dries–Macintyre–Marker, Wilkie) — research level.
- Full Keisler: ultrapower ℝ^ℕ/U with Mathlib `ModelTheory.Ultraproducts` (Łoś) —
  gives everything but abandons the computable, explicit ε.
