# Adjoining π and e as formal generators

`Hyper/HyperConstants.lean`, implemented 2026-08-26 from `cleanup.md`'s plan.

## The question this answers

Algebraic numbers (the natural "richer but still decidable" upgrade from ℚ
discussed for the coefficient field) **cannot** contain π or e — both are
transcendental (Lindemann 1882, Hermite 1873), i.e. by definition not the
root of any nonzero rational polynomial. So getting π/e into the system
can't be a coefficient-field upgrade. It has to be something else.

## The actual answer: adjoin them the way ε already is

`ℚ(π)`, as an abstract field extension, is isomorphic to `ℚ(x)` — the field
of rational functions in a fresh indeterminate — precisely *because* π is
transcendental: there's no algebraic relation to quotient by, so adjoining
it is formally identical to adjoining any new free symbol. That is exactly
what `Hyper/HyperList.lean` already does for ε (`R* = ℚ[ε, ω]/(εω=1)`, a
Laurent-polynomial ring in one variable). So the fix isn't a new coefficient
field — it's the same trick, one more time: give π and e their own exponent
tracks, the same way ε already has one.

## What was built

`Hyper/HyperConstants.lean`: terms are now `(coefficient, εExp, πExp, eExp)`
quadruples instead of `HyperList.lean`'s `(coefficient, εExp)` pairs.
Multiplication adds exponent triples **componentwise** — the three tracks
never mix, which is precisely what "independent generator" means at the
representation level. `simplify`/`mergeAdjacent`/`Add`/`Mul`/`Inv` are the
same recipe as `HyperList.lean`, generalized from one exponent to three.

Proved (all `native_decide`, no `sorry`): π, e nonzero and mutually
distinct; `π · π⁻¹ = 1` and `e · e⁻¹ = 1` (monomial inverse, same
single-term-only caveat `HyperList.lean`'s `Inv` already has); and the point
of the exercise — `(ε + π)²` expands to three genuinely distinct terms
(`ε² + 2επ + π²`, `#eval`-visible), no collapsing, because nothing in the
representation *could* collapse a cross term between independent tracks.

## Why a separate file, not a `HyperList.lean` change

`HyperList.lean` is ~1250 lines with a proved order, a `Field R*` instance,
and other files (`DartPointProbZero.lean`, `HyperProbability.lean`) built on
top of it. Generalizing its term type in place to carry three exponents
would touch all of that for a demonstration feature. `HyperConstants.lean`
proves the same idea stands on its own, at a fraction of the size, with zero
risk to what's already proved. Merging the two (if warranted later) is a
separate, bigger decision.

## What was deliberately left out

- **No relation between π and e.** Whether they're even algebraically
  independent — whether any nonzero rational polynomial in both vanishes —
  is an open problem in number theory. Treating them as free generators is
  the only honest default; nothing here claims or depends on independence
  being *proven*, only on not silently assuming a relation that isn't.
- **No numeric evaluation.** `piGen` is a formal marker, not an
  approximation of 3.14159...; there's no bridge to `Real.pi`'s digits here.
- **No merge into `R*`/`HyperList.lean`.** Explicitly out of scope for this
  pass — see above.
