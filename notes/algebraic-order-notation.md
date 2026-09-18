# Algebraic O-notation and retained precision

O-notation is part of the theory's precision language. The working default
is to display the leading nonzero geometric contribution with an explicit
remainder order, while retaining the exact algebraic expression whenever it
is known. This gives concise formulas without deleting boundary terms.

An O statement alone does not retain omitted coefficients. They can be
recovered only from a retained exact expression or additional information;
they cannot be inferred from the O bound itself.

## Definition without limits

Let H=ℝ(ω) be the existing ordered rational-function field. Choose a positive
infinitesimal gauge g, normally the context's normalized resolution
η=ε/(1+ε). For any integer n, define

```
r ∈ O(g^n)  iff  there exists a standard real M≥0 with |r|≤M g^n.
x = y + O(g^n)  means  x−y ∈ O(g^n).
```

The real bound M is embedded in H. It must be a standard real, not an
arbitrary hyperreal; otherwise the definition would be vacuous. This is
an order comparison in one fixed field, with no limiting process, sequence,
infinite series, or transfer principle.

Writing F for the elements bounded by standard reals, the equivalent
algebraic description is O(g^n)=g^n F, checked by `isO_iff_scaled`.
Order zero describes finite elements. Positive orders specify increasingly
small remainders, and negative orders allow infinite scales. The reference
gauge stays explicit: below it is η, not the distinct raw ε.

In Lean, `IsO g n r` is the bound and `Approx g n x y` is the remainder
statement. The printed `x = y + O(g^n)` is a statement about a remainder
class, not equality with a new field-valued object named O. Two occurrences
of O(g^n) need not be the same remainder.

## Algebraic rules

For a positive gauge g≤1:

| Operation | Valid bound |
|---|---|
| Add or subtract two O(g^n) remainders | O(g^n) |
| Multiply O(g^m) by O(g^n) | O(g^(m+n)) |
| Weaken precision, n≥m | O(g^n) is contained in O(g^m) |
| Divide O(g^n) by g^m | O(g^(n−m)) |
| Multiply a remainder by a bounded factor | Its order is preserved |

For unequal addition orders the weaker bound is O(g^min(m,n)); cancellation
may improve it. At a fixed order, `Approx` is reflexive, symmetric, and
transitive. It respects multiplication when the necessary other factors
are bounded. Reciprocals preserve an absolute error order when both
reciprocals are bounded; infinitesimal denominators require scale tracking.

These rules do not set g² to zero. The exact field still has all powers and
g⁻¹. No quotient identifying infinitesimals with zero is used.

## Geometric formulas at their natural precision

For closed segments of standard length L and closed convex planar patches
with standard area A and perimeter P, the [square](geometric-algebraic-content.md)
and [cube](algebraic-cube-content.md) formulas become

```
square: P(segment) = Lη + O(η²),
cube:   P(segment) = Lη² + O(η³),
cube:   P(patch)   = Aη + O(η²).
```

All three remainder statements are checked against the exact formulas.
For example, the exact spatial segment expression remains

```
P(segment) = Lη² + (1−L)η³.
```

For a closed planar patch in the cube the next terms are

```
P(patch) = Aη + (P/2−2A)η² + (A−P/2+1)η³.
```

The unit cube's coordinate events already have the exact probabilities
1, η, η², η³. They need no remainder label. In particular a line's leading
η² contribution is never discarded merely because it is second order.
Precision is relative to the leading nonzero order of the event.

## Cancellation, conditioning, and integration

From x=1+O(η) and y=1 one can conclude x−y=O(η), but not x−y=0.
The exact witness x=1+η gives the nonzero result η. After a leading-term
cancellation, consult the retained expression or keep the unresolved O
term; do not invent a new leading coefficient.

Conditioning can promote previously small corrections. For example,

```
(η² + O(η³)) / η = η + O(η²).
```

If the denominator itself is approximate, its scale and nonvanishing must
be established before division. The checked reciprocal rule makes its
boundedness assumptions explicit.

For any existing positive normalized integral context Ω, a common bound
|f(i)−h(i)|≤M g^n for every observable region i implies

```
∫[Ω] f = ∫[Ω] h + O(g^n).
```

This follows from positivity, linearity, and ∫[Ω]1=1 and is checked as
`integral_approx_of_uniform_bound`. The hypothesis supplies one common
standard real M. The statement does not silently extend the current finite
observable-partition integral to arbitrary infinite families.

## More precision by finite algebra

A simple checked example is

```
1/(1+g) = 1−g + g²/(1+g) = 1−g + O(g²),   g>0.
```

For any finite truncation length N the finite geometric identity gives

```
1/(1+g) = Σ(k=0,...,N−1) (−g)^k + (−g)^N/(1+g).
```

Multiplication by 1+g verifies the identity by cancellation. The remainder
has absolute value at most g^N for g>0, supplying any chosen finite
precision without an infinite series. Lean currently checks the displayed
two-term reciprocal case; the general finite-N identity here is an algebraic
derivation, not a claim of a newly formalized theorem.

## Implementation status

`Hyper/AlgebraicOrder.lean` defines the remainder relation and proves these
rules, the normalized-integral bound, and the geometric examples. It also
proves 1 is not O(ε), guarding against a vacuous definition.
`test_algebraic.lean` audits the proofs for trust dependencies.

This is a precision API for exact expressions and their bounds. An automatic
renderer or general truncation algorithm has not been implemented. The
presentation policy is now explicit: display the needed order, preserve
known exact expressions, and revisit them when cancellation or conditioning
requires more precision.
