# Setting the coefficient field to a real algebraic field

`Hyper/QuadField.lean` + `Hyper/HyperQuadField.lean`, implemented 2026-08-26
from `cleanup.md`'s (corrected) plan.

## Course correction

The previous pass (`Hyper/HyperConstants.lean`) adjoined π and e as extra
*exponent* dimensions, keeping the coefficient field `𝔽 = ℚ` untouched. That
answered a different question than the one asked: "set our field `𝔽` to
your special field" means the coefficient field itself — the type that
`HyperList.lean`'s `𝔽` (`notation "𝔽" => ℚ`) currently pins to `ℚ` — should
become the richer, still-decidable field discussed earlier (real algebraic
numbers, the ceiling of what stays computable). `HyperConstants.lean` is
still correct for what it does; it just wasn't this.

## Scoped honestly: quadratic, not fully general

The *general* field of real algebraic numbers (arbitrary-degree roots,
canonical minimal-polynomial + isolating-interval representation, decidable
comparison via Sturm sequences) is a serious multi-week undertaking — Sage's
`QQbar`, Mathematica's `Root`. Mathlib has nothing ready-made for it
(confirmed by searching the vendored copy: `AlgebraicClosure` is
classical/noncomputable, `IsAlgebraic` is a bare `Prop`, no
`DecidableEq`/`DecidableLE` instance exists anywhere for a computable
real-algebraic type).

What *is* fully buildable and genuinely correct: **`Quad d = ℚ(√d)`**, for a
fixed non-square integer `d`. This really is a field of real algebraic
numbers (`√d` is a root of `x² - d`) with completely exact, decidable
arithmetic and order:

- Elements are pairs `(a, b)` meaning `a + b√d`.
- `+`, `-`, `*` are closed-form, no case analysis needed.
- `Inv` divides by the field norm `a² - d·b²`, nonzero for every
  `(a,b) ≠ (0,0)` precisely because `d` isn't a perfect square.
- **Order is decided exactly, never numerically**: same-sign (or one-zero)
  coefficients settle it directly; opposite-sign cases reduce to comparing
  `a²` against `d·b²` in `ℚ` — `√d` itself is never approximated or
  evaluated to a decimal anywhere.

Proved via `native_decide` (`Hyper/QuadField.lean`): `(√2)² = 2`,
`√2⁻¹·√2 = 1`, `(1+√2)(1-√2) = -1`, `1 < √2 < 2`, the golden ratio
`φ = (1+√5)/2` satisfies `φ² = φ+1` and `1 < φ < 2` exactly.

## Threading it into the hyperreal structure

`Hyper/HyperQuadField.lean` reruns `HyperList.lean`'s term/`simplify`/`merge`/
`Mul` recipe with the coefficient slot changed from `ℚ` to `Quad d` (the
exponent slot stays `ℚ` — fractional orders like `ε^(1/2)` still mean the
same thing regardless of what coefficients are made of). This makes `√2 · ε`
a genuine first-class hyperreal value rather than an approximated scalar
bolted on afterward: `√2·ε·ω = √2` and `(√2·ε)² = 2·ε²` both check out
exactly.

## Why still a separate file

Same reasoning as `HyperConstants.lean`: `HyperList.lean` is ~1250 lines
with a proved order and a `Field R*` instance; generalizing its coefficient
type in place would touch all of that for a demonstration. A parallel file
proves the idea stands on its own with zero risk to what's already proved.

## What was deliberately left out

- **No full `Field`/`LinearOrderedField` Mathlib typeclass instance for
  `Quad d`.** Matches this project's existing style — `HyperList.lean`
  itself doesn't have a complete one either (`mul_inv_cancel := sorry`,
  documented as structurally hard). The goal here was a correct, tested,
  computable structure with targeted proved facts, not full abstract-algebra
  citizenship.
- **Not the general real-algebraic-number field.** Flagged above as a real,
  much bigger, separate undertaking — root isolation, not a coefficient
  swap.

## Composing with the π/e extension

`Hyper/HyperConstants.lean` (π/e as extra exponent tracks, over plain ℚ
coefficients) and this file's coefficient-field swap act on two different,
non-interacting slots of a term — coefficient vs. exponent — so they compose
freely. `Hyper/HyperQuadConstants.lean` does both at once: `Quad d`
coefficients *and* independent π/e exponent tracks, checked exactly
(`(√2·π)² = 2·π²`, no cross-collapse between the two mechanisms).

**What still doesn't work, and can't**: `Quad d` itself can never contain π
or e. `Quad d` is an algebraic extension (`√d` is a root of `x² - d`); π and
e are transcendental by definition, so no algebraic extension reaches them,
regardless of `d`. π/e can only ever enter as exponent-track generators
(formal symbols, as `HyperConstants.lean` already does), never as `Quad`
elements — that boundary is exact, not a current implementation gap.
