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

## Root-closed model + transfer — PROVED (2026-10-02)
`Hyper/HyperAlgebraic.lean`: `Number` = germs at s→+∞ (ω read as a large real s) that are
(1) eventually continuous and (2) algebraic over ℝ(ω) (`IsAlgebraic (RatFunc ℝ)`).
- Roots are symbolic: √(1+ω) is the germ s ↦ √(1+s), fixed by y²-(1+ω)=0. No series.
  Membership of φ(x) only needs φ continuous and φ(r)ⁿ linear on each sign class;
  algebraicity then comes free from Mathlib `IsAlgebraic.of_pow`.
- Key lemma `eventually_sign_eq`: a continuous algebraic germ has an eventual sign.
  Factor P = Yᵐ·Q with Q(0) ≠ 0; at a zero s₀ of y, Q(s,y(s)) → Q(s₀,0) ≠ 0, so y ≡ 0 near s₀.
  So the zero set is open and closed in (s₁,∞) → sign locally constant → constant (connected).
- Field via germ inverse (`IsAlgebraic.invOf`), order = inherited germ order (eventual ≤),
  total by the sign lemma. ℝ(ω) embeds via `ofBase` (order preserving).
- Proved: `sqrt_mul_self`, `exists_pow_eq_of_nonneg` (every n-th root of x ≥ 0),
  `exists_pow_eq_of_odd` (odd roots of everything).
`Hyper/AlgebraicTransfer.lean`: transfer for quantifier-free formulas over `+ · - ⁻¹ √`,
real constants, `=`, `<` — `√` as function symbol is Keisler's Axiom D for √.
Term evaluation commutes with reading at s *exactly* (germs are pointwise).
Demos `Hyper/probes/TransferExamples.lean`: ε+ω ≥ 2, 1 < ω, √ε·√ω = 1, ∛(-ω), ⁵√ε.
The former `no_sqrt_omega` (√ω ∉ ℝ(ω)) was dropped: that boundary no longer applies.
`Hyper/EventualValue.lean`: reading ℝ(ω) at s, ring hom `toGerm` into germs.
Not yet: real-closedness (roots of arbitrary odd-degree polynomials, not just radicals) —
needs a continuous root branch for large s; and decidable equality (would need resultants).

## HyperList bridge — PROVED (2026-10-02)
`Hyper/HyperListBridge.lean`: `toNumber : HyperList → Number`, term (c,q) ↦ s ↦ c·s^q
(rational q fine: (c·s^q)^den = c^den·ω^num is algebraic). Built as
`laurentGerm ∘ HyperListSemantics.interpret` (`AddMonoidAlgebra.liftNCRingHom`).
- `toNumber_add/neg/sub/mul` for the R* operations (`merge`, map-negate, fieldMul body).
- `toNumber_eq_iff`: equal in Number ⟺ equal `coeffAt` ⟺ equal `simplify` (decidable).
- `lt_iff_toNumber_lt`, `le_iff_toNumber_le`: the list order (`leadSign`) IS the Number order;
  proof: highest-order term dominates (`eventually_sign_listValue`, s^(q-e) → 0).
- So `native_decide` on lists ⇒ theorems in Number; demos
  `Hyper/probes/HyperListBridgeExamples.lean`: √ω < ω, ω^(1/2) list = symbolic √ω,
  non-canonical [(1,0),(-1,0)] = 0.
⚠️ Decide list equality with `toNumber_eq_of_decide` (uses `List`'s DecidableEq), NOT `=` on R*:
`HyperList.lean`'s `DecidableEq R*` rests on `axiom eq_of_simplify_eq`, which is inconsistent
(proves False, see `probes/bridge_axioms.lean`). Audit with `#print axioms`.

## Germ transfer (original sketch)
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
