# Plan (corrected): set the coefficient field `𝔽` to a real algebraic field

## Course correction

The previous pass (`Hyper/HyperConstants.lean`) adjoined π and e as extra
*exponent* dimensions, keeping the coefficient field `𝔽 = ℚ`. That's not
what was asked for: the actual request is to replace `𝔽` itself with the
"special field" discussed earlier — a genuine, decidable field of real
algebraic numbers, richer than ℚ. `HyperConstants.lean` stays (it's correct
for what it does, and doesn't conflict with this), but it's not this task.

## What's actually achievable, honestly

The *general* field of real algebraic numbers (arbitrary-degree roots,
canonical representation as minimal-polynomial + isolating interval,
decidable comparison between roots of *different* polynomials via Sturm
sequences) is a serious, multi-week undertaking — the kind of thing Sage's
`QQbar` or Mathematica's `Root` objects are. Mathlib has no ready-made
computable instance for this (confirmed by searching the vendored copy:
`AlgebraicClosure` exists but is classical/noncomputable, `IsAlgebraic` is a
bare `Prop`, nothing with `DecidableEq`/`DecidableLE`).

What *is* fully achievable, correct, and a genuine (if narrower) instance of
"decidable real algebraic numbers": **quadratic field extensions `ℚ(√d)`**,
for a fixed non-square integer `d`. Elements are pairs `(a, b)` meaning
`a + b·√d`; arithmetic is closed-form (no case explosion); the field norm
`a² - d·b²` gives an exact `Inv`; and order is decidable by comparing `a²`
against `d·b²` in `ℚ` — no numeric approximation of `√d` is ever computed,
the comparison is exact. This genuinely contains `√2`, the golden ratio
`(1+√5)/2`, etc. — real, irrational, algebraic numbers with fully exact,
decidable arithmetic and order.

## Concrete deliverables

1. `Hyper/QuadField.lean`: `Quad (d : ℤ)` — `a + b√d` — with `Zero`/`One`/
   `Add`/`Neg`/`Sub`/`Mul`/`Inv`/`Div`, `DecidableEq`, and a decidable
   `LT`/`LE` via exact rational comparison (`cmp`, case-split on the sign of
   `a`, `b`, falling back to comparing `a²` vs `d·b²` when they disagree).
   `native_decide`-checked: `(√2)² = 2`, `√2⁻¹·√2 = 1`,
   `(1+√2)(1-√2) = -1`, `1 < √2 < 2`, the golden ratio's `φ² = φ + 1` and
   `1 < φ < 2`.
2. `Hyper/HyperQuadField.lean`: hyperreal terms `Quad d × ℚ` — same
   `simplify`/`merge`/`Mul` recipe as `HyperList.lean`, coefficient type
   swapped from `ℚ` to `Quad d`. This is the actual ask: `ε`/`ω` with
   irrational scalar coefficients, e.g. `√2 · ε`, checked exactly
   (`√2·ε·ω = √2`, `(√2·ε)·(√2·ε) = 2·ε²`).
3. `lake build` clean, no `sorry`.
4. Update/extend the notes with why this is the honest scope (quadratic,
   not fully general algebraic) and how it differs from the discarded
   π/e-as-exponents approach.

## Non-goals

- Not the fully general real-algebraic-number field (root isolation,
  Sturm sequences) — flagged as a real but much bigger separate task.
- Not touching `Hyper/HyperList.lean` or `Hyper/HyperConstants.lean` —
  another standalone file, same reasoning as before (don't risk ~1250 lines
  of proved work for a demonstration).
- Not proving a full `Field`/`LinearOrderedField` Mathlib instance for
  `Quad d` — matching this project's existing style (`HyperList.lean`
  itself doesn't have one either, `mul_inv_cancel` is a documented `sorry`
  there), the goal is a correct, tested, computable structure with targeted
  proved facts, not full abstract-algebra typeclass citizenship.
