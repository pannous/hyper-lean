# Plan: adjoin π and e as formal generators (multivariate extension of R*)

## Goal

Extend the existing single-generator model (`R* = List (ℚ × ℚ)`, monomials
`coefficient · ε^exponent`) to also carry `π` and `e` as independent formal
generators, the same way `ε`/`ω` are already handled — not as approximated
real numbers, and not by moving to a richer coefficient field (real algebraic
numbers don't contain π or e anyway; they're transcendental). `ℚ(π)` as an
abstract field extension is isomorphic to `ℚ(x)` (a fresh indeterminate)
since π is transcendental — so "adjoin a new formal symbol" is not a hack,
it's the mathematically exact description of what that extension *is*.

## Design

- **New file, `Hyper/HyperConstants.lean`. Do not touch `Hyper/HyperList.lean`.**
  That file has ~1250 lines and dozens of proved theorems (order,
  `Field R*` instance, dart-probability results elsewhere depend on it).
  Generalizing its term type in place risks breaking all of it for a
  demonstration feature. A new, smaller, self-contained file proves the
  concept without that risk.

- **Term representation**: instead of `(coefficient, ε-exponent) : ℚ × ℚ`,
  use `(coefficient, εExp, πExp, eExp) : ℚ × ℚ × ℚ × ℚ` — a fixed-arity
  tuple, not a general `Finsupp`/`MvPolynomial` machinery. With only three
  named generators, a plain tuple keeps `DecidableEq`, `Repr`, and all the
  list-based `simplify`/`mergeAdjacent`/`Mul` logic essentially copy-adapted
  from `HyperList.lean`, rather than needing Mathlib's general multivariate
  polynomial infrastructure.

- **Operations to port** (same shape as `HyperList.lean`, generalized from
  one exponent to three): `simplify`/`mergeAdjacent` (merge terms with
  identical `(εExp, πExp, eExp)` triples), `Add`/`Neg`/`Sub` (list
  append/map + simplify), `Mul` (cartesian product, multiply coefficients,
  **add exponent triples componentwise** — this is where independence lives:
  there is no rule that ever lets a `π`-exponent bleed into an `ε`-exponent
  or vice versa), `Zero`/`One`, and the four generators `epsilon`, `omega`,
  `piGen`, `eGen` as singleton terms.

- **Deliberately not doing**: no numeric evaluation (no plugging in π's
  digits), no `Inv`/`Field` instance beyond termwise-monomial inverse
  (same documented limitation as `R*`), no assumed relations between the
  generators. In particular — **do not add any rewrite rule relating π and
  e** (e.g. nothing resembling `e^(iπ) = -1`, which needs `i` too and isn't
  the point here anyway). Whether π and e are even algebraically independent
  is a genuine open problem in number theory; treating them as free
  generators is the only mathematically honest default, and it costs
  nothing — a real relation, if one is ever proven, can always be added
  later as an explicit rewrite without contradicting anything built on the
  free version.

## Concrete deliverables

1. `Hyper/HyperConstants.lean`: term type, `simplify`, `Add`/`Neg`/`Sub`/`Mul`
   instances, `epsilon`/`omega`/`piGen`/`eGen` constants, `DecidableEq`.
2. A handful of `native_decide`/`#eval`-checked sanity facts:
   - `piGen ≠ 0`, `eGen ≠ 0`, `piGen ≠ eGen`
   - `piGen * piGen⁻¹ = 1` (termwise monomial inverse, exact for a single
     generator — same style as `ε * ω = 1`)
   - independence is structural, not proved as a theorem about ℝ: a mixed
     product like `(ε + π) * (ε + π)` genuinely produces a 3-term result
     (`ε² + 2·ε·π + π²`, no collapsing), demonstrating that cross terms
     survive rather than silently canceling — that's what "independent
     generator" *means* at the term-representation level.
3. `lake build` clean, no `sorry`.
4. A short note (extending or alongside the existing
   `notes/hyperreal-probability-foundations.md`-style notes) recording why
   this design was chosen over (a) real algebraic numbers as the coefficient
   field, (b) trying to represent π/e as approximated real values.

## Explicit non-goals (this pass)

- Not merging this into `R*`/`HyperList.lean` — it's a separate,
  standalone proof of concept.
- Not building numeric evaluation/approximation.
- Not attempting any theorem that would require knowing whether π, e are
  algebraically independent (an open problem) — nothing here should
  accidentally assume or "prove" something equivalent to resolving it.
