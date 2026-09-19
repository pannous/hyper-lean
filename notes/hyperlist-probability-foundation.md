# Grounding algebraic probability in HyperLists

19 September 2026. This grounds the current theory in finite lists and their
fractions; it does not change the selected geometric content or the separate
[alternatives note](algebraic-probability-alternatives.md).

The answer is **yes for all current probability formulas**. The necessary
completion is a fraction of two HyperLists. A single finite list represents
a Laurent expression and is not closed under reciprocals of mixed sums.

## The algebraic construction

Fix a coefficient field K. Interpret an integer-order HyperList by

```
[(a₁,n₁), …, (aₘ,nₘ)] ↦ a₁ωⁿ¹ + … + aₘωⁿᵐ,       ε = ω⁻¹.
```

The exponent is the power of **ω**, matching the original backend. Thus
`[(1,-1)]` is ε, and `[(1,1)]` is ω.

Addition appends the terms. Multiplication convolves them:
`(a,n)·(b,m) = (ab,n+m)`. Negation changes coefficient signs.
Normalization can sort, combine equal exponents, and delete zero terms.
These are changes of presentation. For example,

```
[(1,-1),(1,-1)] ≠ [(2,-1)]       as raw lists,
[(1,-1),(1,-1)] ≡ [(2,-1)]       as numbers.
```

The numerical equality is indispensable. Literal list equality cannot serve
as field equality. The existing `eq_of_simplify_eq` axiom tries to identify
raw lists and is not used by the new results.

Now represent a number as `[A / B]`, where A and B are finite lists and B has
nonzero value. Identify `[A/B]` and `[C/D]` when `AD ≡ CB`. Define

```
[A/B] + [C/D] = [(AD+CB)/(BD)]
[A/B] · [C/D] = [(AC)/(BD)]
[A/B]⁻¹      = [B/A]                    when A has nonzero value.
```

The whole numerator and denominator swap. Reciprocating individual terms
would incorrectly make `1+ω` the inverse of `1+ε`; their product is
`2+ω+ε`, not 1. This failure has a checked regression theorem.

Every rational function has finite numerator and denominator polynomials,
so **every element of the current exact field K(ω) has this presentation**.
Conversely, evaluating each finite list gives an element of K(ω). Quotienting
fractions by value equality produces a genuine field equivalent to K(ω).
The Lean field instance on this quotient is obtained through that proved
equivalence. No new field axiom, infinite series, or transfer principle is
introduced.

The already checked order on K(ω) determines the order of these values. The
implementation currently uses that order through interpretation, rather than
installing a separate ordered-field instance on the list-fraction quotient.
For a nonzero list, the leading term means the nonzero coefficient of the
largest exponent **after collecting equal exponents**. For a fraction, the
sign is the ratio of numerator and denominator leading signs. This describes
the algebraic order; an optimized executable leading-term comparator on the
new quotient is not supplied here.

## What this means for the integral

In one fixed finite observable context Ω, write its region contents as cᵢ and
an observable as fᵢ. Each cᵢ and fᵢ is represented by a list fraction. Compute

```
Z       = sum of the cᵢ list fractions
N       = sum of the fᵢ·cᵢ list fractions
∫_Ω f   = N · reciprocal(Z).
```

The positivity condition on the context proves Z ≠ 0. These operations are
implemented, and their interpreted value is proved to equal the existing
context integral for **every** finite context and observable over K(ω).
In particular, `∫_Ω 1 = 1` holds exactly. Event probabilities are the same
integral applied to indicator functions; conditioning and delta calculations
retain their existing meaning through this equality.

This is a representation of the integral's arithmetic. It does not pretend
that listing a region's symbolic content enumerates all points in that region.
A list of three monomials and a partition into three observable regions are
different kinds of list.

## The dart contents as actual lists

With coefficients in ℝ:

| Object | Finite list for its raw content |
|---|---|
| Closed unit interval | `[(1,0),(1,-1)]` |
| Closed unit square | `[(1,0),(2,-1),(1,-2)]` |
| Closed unit cube | `[(1,0),(3,-1),(3,-2),(1,-3)]` |
| Closed planar segment, length L | `[(L,-1),(1,-2)]` |
| Point in d dimensions | `[(1,-d)]` |
| Unit disk | `[(π,0),(π,-1),(1,-2)]` |
| Unit solid ball | `[(4π/3,0),(2π,-1),(4,-2),(1,-3)]` |

The square and cube are obtained by convolving the interval list. Their raw
contents are `(1+ε)²` and `(1+ε)³`; the probability of the whole space is its
content divided by itself, exactly 1. No geometry or normalization rule has
changed.

The calibrated point probability in a closed unit interval is the list fraction

```
η = [(1,-1)] / [(1,0),(1,-1)] = ε/(1+ε).
```

Product contexts therefore still give η, η², η³ for a coordinate surface,
axis crossing, and point in the cube. A diagonal's √2 coefficient is an
ordinary coefficient of its length term; no special diagonal axiom appears.
For a disk point the explicit fraction is

```
[(1,-2)] / [(π,0),(π,-1),(1,-2)].
```

The generic coefficient parameter matters: the active original HyperList uses
ℚ coefficients, so π and √2 cannot be represented there as coefficients.
Using the same finite-list construction over ℝ solves this representation
issue. As before, arbitrary real coefficients are noncomputable data in Lean;
this is not a claim of an executable normalizer for every real expression.

## Rational exponents in the original backend

The actual historical HyperList permits rational exponents, not just integers.
There is a separate sound interpretation for that existing representation:

```
HyperList → AddMonoidAlgebra ℚ ℚ → FractionRing (AddMonoidAlgebra ℚ ℚ).
```

The middle object is the algebra of **finitely supported** rational-exponent
formal sums. It is not a space of infinite series. It is an integral domain,
so its fraction field is available from the checked mathlib construction.

The adapter proves that the existing `simplify`, `fieldAdd`, `fieldNeg`, and
`fieldMul` preserve their intended values. It also proves that two original
lists have equal fraction-field values exactly when every exponent has the
same summed coefficient. A regression checks that two exponent −1/2 monomials
multiply to exponent −1.

This rational-exponent field is larger than the integer-exponent field over
the same coefficient field. In particular, it has a formal square root of ε.
It must not be silently identified with K(ω). An ordered probability interface
for this larger field, and a formal embedding relating both implementations,
remain future work. Neither is needed to represent the formulas currently in
the paper, which all have integer ε-exponents and standard real coefficients.

## Checked implementation and remaining boundaries

- [HyperListFoundation.lean](../Hyper/HyperListFoundation.lean): generic integer
  lists, correct finite arithmetic, two-list presentation of every rational
  function, cross-multiplication equality, quotient equivalence and field.
- [HyperListProbability.lean](../Hyper/HyperListProbability.lean): the integral
  built from list fractions, interpretation theorem, normalization, and sparse
  presentations for the selected geometric contents.
- [HyperListSemantics.lean](../Hyper/HyperListSemantics.lean): adapter proving the
  coefficient-level soundness of the actual original rational-exponent backend.
- [test_hyperlist_foundation.lean](../test_hyperlist_foundation.lean): regression
  examples and explicit theorem-dependency audit. The test script allows only
  `propext`, `Classical.choice`, and `Quot.sound` for this audit.

The core and probability modules import no legacy HyperList field instance.
The adapter necessarily imports the legacy module, but its audited results do
not depend on that module's unsupported field/equality axioms or unfinished
proofs. Historical files are preserved; this change does not certify every
old use of their raw-list operations.

The point, dot, and halo distinction also remains unchanged. A numerical
content does not identify their underlying sets, and a halo still lacks the
finite geometric support specification used for a dot. Likewise, selecting
geometric contents and proving positivity and compatibility on a broad event
algebra is separate from constructing their scalar field. The existing
finite dart contexts are checked; the global geometric extension remains open.

Algebraic O-notation applies to the exact interpreted fraction. Discarding
higher-order terms for display never changes the exact list-fraction value or
makes ε² zero. Exact conditioning should precede truncation because division
by an infinitesimal can promote a higher-order correction.
