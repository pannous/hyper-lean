# Can exp/log be expressed algebraically on R*?

Prompted by: does `HyperList.R*` (finite `List (ℚ×ℚ)` monomials) support exact
`exp`/`log`, the way `hyper.jl`'s Taylor series does numerically
(`TERM_PRECISION = 60`)?

## Short answer
Not exactly, on the current finite-support representation — but there are two
genuinely different ways to get there, and neither needs real-analytic limits.

## Path 1: truncated, doable now with "basics"
Fix a max order `N`, define `exp h := ∑_{k=0}^{N} h^k / k!` as an ordinary
finite `R*` sum. Exact up to `O(h^{N+1})`, which is dropped/approximated —
same idea `hyper.jl` uses numerically, just symbolic and order-bounded
instead of float-bounded. `exp(a+b) = exp(a)*exp(b)` only holds up to the
truncation order, not on the nose.

This is close in spirit to the **AlmostField** approach already explored in
`notes/almost-field.md` for the (different, superseded-model) `HGReal`:
instead of requiring exact inverses, define `negligible x n` and prove
identities hold "up to order n". Same trick would let a truncated `exp`/`log`
have honestly-stated, honestly-proved theorems instead of silently-wrong
`R*`-typed values past the truncation order.

## Path 2: exact, needs infinite support (formal power series)
An *exact* `exp(ε) = 1 + ε + ε²/2! + ε³/3! + …` needs infinitely many terms —
impossible in `List (ℚ×ℚ)` (finite by construction), but fine in a
well-ordered-support representation (`HahnSeries`/`PowerSeries`, see
`notes/` — this is the same representation swap discussed for fixing
`Field R*`'s `mul_inv_cancel` sorry).

The interesting part: this doesn't require real-analytic convergence
reasoning at all. Mathlib's `PowerSeries.exp` is a *formal* power series
identity — `exp(f + g) = exp(f) * exp(g)` is proved by manipulating
coefficients combinatorially (it's an algebraic identity in any ℚ-algebra),
not by taking limits. So swapping `R*`'s representation to `HahnSeries ℚ ℚ`
would plausibly give exact, algebraically-proved `exp`/`log` satisfying the
usual laws "for free" from Mathlib — same payoff category as the `Field`
instance discussed for that swap, not a separate undertaking.

## Bottom line
- Truncated/approximate exp-log: buildable now, basics-level, same style as
  the rest of `HyperList.lean`.
- Exact exp-log with proved algebraic laws: needs the `HahnSeries`/
  `PowerSeries` representation swap already motivated by `mul_inv_cancel` —
  formal, not real-analytic, so still "no higher math" in the limits/analysis
  sense, just a different (infinite-support) data representation.
