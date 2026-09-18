> **Update (2026-09-18).** The exact field, event algebra, normalized integral,
> and dart model are now implemented in the new trusted path described in
> [the current foundations](../algebraic-hyperreal-foundations.md).
> The backend restrictions below still apply to the legacy HyperList API,
> but exact mixed-order division no longer needs a series or approximation.

# Algebraic hyperreal probability from symbolic counts

Revised 2026-09-10 after the design correction that probability values in
this project are to be treated directly as algebraic ratios. The primitive idea is
normalized algebraic counting:

```text
P(E) = count(E) / count(Ω).
```

The companion curriculum is
[`algebraic-stochastics-exercises.md`](algebraic-stochastics-exercises.md):
20 worked problems progressing from elementary outcomes to research-level
hyperfinite asymptotics, each labeled by current framework readiness.

The counts may contain powers of the canonical infinite number `ω`; their
quotient is a hyperreal probability containing powers of `ε`, with
`εω = 1`. This gives direct algebraic calculations with probabilities,
including positive infinitesimal values for elementary outcomes.

## 1. The Dart calculation is a count ratio

Choose an algebraic grid convention for a two-dimensional region. If the
region has normalization coefficient `A`, write its number of elementary
outcomes as

```text
count(Ω) = Aω².
```

A particular elementary outcome has count `1`, while a line containing `Lω`
grid outcomes has count `Lω`. Therefore

```text
P(point) = 1 / (Aω²)    = ε²/A,
P(line)  = Lω / (Aω²) = Lε/A,
P(line) / P(point) = Lω.
```

Both probabilities are positive and have zero standard coefficient, but they
are not equal. A classically null event need not be logically impossible;
the gain here is more precise: ordered infinitesimals retain comparative
information among events that receive the same classical value `0`.

The grid convention is part of the model. `ω` cells and `ω + 1` endpoints
are different choices, and assigning probability `ε` to every one of
`ω + 1` outcomes would total `1 + ε`, not `1`. Every example must state a
normalization convention and prove `P(Ω) = 1`.

## 2. General uniform-event formula

For an `n`-dimensional uniform algebraic grid, let

```text
count(Ω) = Aωⁿ,
count(E) = cωᵈ,   with d ≤ n.
```

Then the event has rarity order `k = n - d` and

```text
P(E) = (c/A)εᵏ.
```

Thus the familiar codimension expression is a theorem about symbolic counts,
not the definition of probability. A larger `k` is strictly rarer than a
smaller `k` when both coefficients are positive. Events of equal rarity
order compare by their rational coefficients.

The current reference backend uses rational coefficients, so `A` and `c` are
rational normalization/count coefficients. It does not yet represent a
literal disc area `πr²` in this path.

## 3. Probability algebra

Once event probabilities are normalized, ordinary finite probability rules
are algebraic identities in `R*`:

```text
P(not A)              = 1 - P(A)
P(A or B)             = P(A) + P(B)              when A and B are disjoint
P(A and B)            = P(A) P(B)                when A and B are independent
P(A | B)              = P(A and B) / P(B)        when the quotient is defined
E[X]                  = Σ x P(X = x)
Var(X)                = E[(X - E[X])²]
```

These equations need an event representation to justify when events are
disjoint, overlap, or are independent. Codimension by itself is insufficient:
a point on a line is already included in the line, whereas an off-line point
creates a probability with two rarity orders. A future Boolean event algebra
should make these distinctions explicit and derive complement,
inclusion-exclusion, and monotonicity from a small set of finite axioms.

Finite weighted sums are enough to formalize expectation, moments, variance,
and covariance for explicitly listed outcomes. They do not turn a Lean
`Fin n` into a genuinely hyperfinite index type.

## 4. Conditional probability and exact division

Same-order conditioning is especially clean. If

```text
P(A and B) = aεᵏ,
P(B)       = bεᵏ,
```

then `P(A | B) = a/b`: the infinitesimal factor cancels. This supports, for
example, Bayes calculations after an exact continuous-like observation.

Mixed-order denominators are different. The current `HyperList` inverse maps
each term separately, so it is exact for one monomial but not for a sum such
as `Lε + ε²`. A correct calculation such as

```text
Lε / (Lε + ε²) = 1 - ε/L + O(ε²)
```

requires either a fraction-field/completed-series backend or a certified
truncated inverse with an explicit remainder theorem. The initial API must
therefore expose exact monomial division only and must not route mixed-order
conditioning through the aspirational `Field R*` instance.

## 5. Statistics that the algebra makes visible

The framework is useful beyond geometric examples:

- An exact tie of two uniform `ω`-way observations has probability `ε`.
- For fixed sample size `m`, a collision among `ω` equally likely labels
  begins at order `choose(m,2)ε`; higher collision patterns occupy higher
  powers of `ε`.
- A geometric waiting-time recurrence with success probability `ε` gives
  expected wait `1/ε = ω`.
- Posterior odds after an exact observation can remain ordinary because a
  common infinitesimal likelihood factor cancels.
- Estimators with the same classical limiting error can still be compared by
  the leading coefficients and orders in their hyperreal MSE expressions.

These are algebraic calculations. Statements about infinite sequences,
almost-sure convergence, laws of large numbers, central limit theorems, or
Loeb constructions require substantially more structure.

## 6. Honest boundary of the current Lean model

`Hyper/HyperList.lean` represents a hyperreal expression as a finite list of
rational coefficient/exponent pairs. It is a useful executable algebra of
formal `ε`/`ω` orders, but it is not an ultrapower and currently provides no
transfer principle, internal sets, saturation, or genuinely hyperfinite index
types.

Two existing implementation shortcuts are outside the trusted probability
path:

1. `eq_of_simplify_eq` identifies raw lists from equality of normal forms,
   although differently shaped lists can normalize alike. The durable repair
   is a canonical subtype or quotient, not an axiom equating raw lists.
2. The bundled `Field R*` admits `mul_inv_cancel` even though termwise inverse
   is not an inverse for multi-term expressions. Exact probability division
   must use a proved monomial operation until a true fraction-field or series
   representation replaces it.

Consequently, importing `HyperList` does not by itself justify calling a new
theorem axiom-free. Headline probability results should be checked with
`#print axioms`, and their proofs should avoid both shortcuts.

## 7. Framework roadmap

1. Define symbolic monomial counts and proved exact monomial quotients.
2. Define normalized uniform probability from favorable and total counts;
   prove `P(Ω)=1`, positivity, and the general rarity-order formula.
3. Rename the Dart and codimension APIs around `pointProbability`,
   `lineProbability`, and `uniformEventProbability`.
4. Add finite event expressions with complement, conjunction, disjoint union,
   and explicit independence evidence.
5. Add finite random variables and weighted sums for expectation and moments.
6. Replace raw `HyperList` equality by a sound canonical representation.
7. Add a correct fraction/completed-series representation or certified
   truncation before supporting mixed-order conditional probabilities.
8. Only then consider a separate nonstandard-universe development for
   transfer-based limit theorems.

## 8. Verification discipline

For every probability construction:

- prove the sample-space normalization explicitly;
- distinguish exact equality from leading-order or truncated equality;
- check disjointness before adding event probabilities;
- restrict exact division to proved denominator classes;
- restrict standard-coefficient claims to finite expressions;
- use `#print axioms` on headline theorems;
- never infer transfer, internality, or countable probability laws from this
  finite Laurent representation.

This scope is narrower than a complete nonstandard probability theory, but it
is strong enough for a substantial progression of exact algebraic exercises
while keeping every claimed result honest.
