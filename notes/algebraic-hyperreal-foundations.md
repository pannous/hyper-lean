# Algebraic hyperreals, normalized integration, and the dart

**Round boards:** the [unit disk and solid ball](algebraic-round-dart.md)
have concrete positive dart contexts with exact normalization and the same
codimension orders, derived from a specified round-body content convention.

**Precision convention:** use [algebraic O-notation](algebraic-order-notation.md)
to display the needed order while retaining known exact expressions. The
remainder bounds use standard real constants and no limiting process.

Revised 2026-09-19. This is the current foundational specification. It
supersedes the point/dot/halo identifications and unrestricted integration
claims in the older integral notes. The historical list backend and its
examples remain available. The [HyperList foundation](hyperlist-probability-foundation.md)
now supplies checked finite-list fractions and a list implementation of the
normalized integral. The core imports no legacy `HyperList`; a separate audited
adapter validates the original coefficient arithmetic.

**Geometric continuation:** for the selected Euclidean, rotation-invariant
model read [Why length appears naturally](geometric-algebraic-content.md).
It derives the line coefficient from symmetry, scaling, and unit calibration,
then derives endpoint corrections by finite additivity. In the closed unit
square the exact line probability is `(length·ε+ε²)/(1+ε)²`. The midpoint
sampling examples below are retained as a distinct earlier model.

The proposed resolution is **an exact ordered fraction field, a positive
algebraic content on an event algebra, and normalization by the ambient
sample space Ω**. No limits, infinite series, transfer principle, or
standard-part operation is needed for the probability calculations below.

The foundational core and the explicitly specified dart model are settled
here. This is not a claim to have integrated every function or constructed
a canonical probability on every subset of Euclidean space.

## The earlier minimal sampling example: square, descending line, point

Take the unit square Ω and the descending diagonal from `(0,1)` to `(1,0)`:
`L = {(x,y) ∈ Ω : x+y=1}`. Choose one admitted elementary outcome p on L.
In the midpoint resolution convention the normalized algebraic integral is

```
∫_Ω 1 = 1,         ∫_L 1 = ε,         ∫_{p} 1 = ε².
```

All three integrals use **the same two-dimensional probability context**.
In particular, the line integral here means `I_Ω(1_L)`; ordinary arc-length
integration would ask a different question and give length √2.

Only three disjoint regions are needed:

| Region | Normalized algebraic content |
|---|---:|
| `{p}` | `ε²` |
| `L \ {p}` | `ε − ε²` |
| `Ω \ L` | `1 − ε` |

These contents are positive and sum to 1. Thus, for an observable with
respective values a,b,c, the whole integral is simply

```
I_Ω(f) = aε² + b(ε−ε²) + c(1−ε).
```

Substituting `(a,b,c)=(1,1,1)`, `(1,1,0)`, and `(1,0,0)` proves the three
displayed values. This is the complete algebraic calculation on this event
algebra; it requires no limiting process or infinite summation.

The midpoint convention explains the descending line without endpoint
corrections. At finite resolution N, coordinates `(i+1/2)/N` and
`(N−1−i+1/2)/N` sum to 1. There are exactly N such pairs among N² samples.
The count polynomials N², N, and 1 give the ratios 1, ε, and ε² on algebraic
substitution `N=ω`. This motivates the content assignment above; it does not
assert that the ordered field contains a constructed array of ω indices.
Both the finite midpoint identity and the finite number of descending pairs
are proved in `Hyper/AlgebraicDart.lean`, alongside the three integrals under
`AlgebraicDart.Minimal`. Midpoints do not count the corner endpoints as extra
outcomes. An endpoint-inclusive convention needs its own normalization.

If p names one square **dot** of side ε in a resolution observation space,
that elementary outcome has the same assigned probability ε². This is a
choice of what an outcome represents, not an identification of a geometric
singleton with a region. A round dot of radius ε instead has geometric area
πε²; a **halo** has no prescribed radius or content. Consequently the minimal
example should say “point” or “one specified elementary dot,” not treat
point, dot, and halo as interchangeable supports.

## 1. The numbers: complete the field algebraically

Let K be an ordered coefficient field. Use K = ℝ when every ordinary real
constant is needed, or K = ℚ for rational examples. Define

```
H_K = K(ω) = Frac(K[ω]),       ε = ω⁻¹.
```

Elements are finite rational expressions p(ω)/q(ω), q ≠ 0. Equality is
polynomial cross-multiplication, not equality of expression lists. In a
representation with monic denominator, the sign of a nonzero element is
the sign of its numerator's leading coefficient. This is an ordered field:
products multiply leading signs, and sums of positive fractions have
positive leading sign after taking a common positive denominator.

Consequently

```
ω > r for every r ∈ K,
0 < ε < r for every positive r ∈ K,
εω = 1,             ε² > 0,
(1 + ε)⁻¹(1 + ε) = 1.
```

**An infinite expansion is unnecessary.** The exact answer to `1/(1+ε)`
is the finite fraction `1/(1+ε)`. Laurent polynomials are a subring of this
field, not the field itself. A fraction field is not a Laurent-series field;
the latter is a larger construction. Termwise inversion of a sum is invalid.

“Algebraic” describes the operations and construction. It does not assert
that ε is an algebraic number over ℝ: a nonzero real polynomial cannot vanish
at a positive infinitesimal, since its lowest nonzero power dominates its
higher powers. Thus ε must be transcendental over ℝ. Nor is H_ℝ a complete
Robinson universe: we do not assert transfer, saturation, or that every real
function has an extension.

Integer powers suffice for this core and its dimensional probability orders.
If rational powers are wanted, adjoining compatible positive nth roots is
an additional algebraic extension; it is not silently part of this Lean
type. π can simply be a coefficient in K = ℝ, with no conjecture about π and e.

For completeness, the usual finite/infinitesimal distinction also has an
algebraic description. If h = p(ω)/q(ω) is nonzero, its order is
`deg(p) − deg(q)`. Negative order is infinitesimal, zero order has ordinary
part `lc(p)/lc(q)`, and positive order is infinite. For finite elements,
discarding negative orders gives the standard part and is a ring
homomorphism: after changing to ε and canceling its common powers, the
denominator is nonzero at ε = 0, so ordinary polynomial evaluation proves
the laws. This description is a mathematical derivation; the new Lean
modules do not yet expose a standard-part API. Probability does not need it.

**Checked:** `Hyper/OrderedRational.lean` constructs the ordering and proves
ε smaller than every positive coefficient, gauging, and exact mixed inverses
using Mathlib's rational-function field. Its theorem audits contain only
Lean's ordinary `propext`, `Classical.choice`, and `Quot.sound`.

## 2. The context: Ω and a finite event algebra

Keep **Ω** for the whole sample space; reserve lowercase **ω** for the infinite
number. A probability context specifies:

1. Ω and an algebra of admitted events, closed under finite Boolean operations;
2. a content ν with ν(∅) = 0 and finite additivity on disjoint events;
3. ν(E) ≥ 0 and ν(Ω) > 0.

If every nonempty admitted event has strictly positive content, probability
zero means impossible *within that event algebra*. Strict positivity is an
extra property, not a consequence of mere nonnegativity. Neither cardinality
nor a σ-algebra is required. Symbolic counts are one way of specifying ν;
unnormalized geometric content is another. Common positive scaling cancels.

For a finite disjoint partition `Ω = C₁ ⊔ … ⊔ Cₙ` and a function constant
on each cell, define the algebraic integral by

```
J_Ω(f) = Σᵢ fᵢ ν(Cᵢ),
∫_Ω f dP_Ω = I_Ω(f) = J_Ω(f) / ν(Ω).
```

Refining a cell leaves this expression unchanged whenever the contents of
its subcells sum to its original content and f is unchanged there. This is
just the distributive law. Thus the integral belongs to the function and
context, not the chosen expression for the partition.

The implementation uses a finite index type to name these observable cells.
**A cell may represent infinitely many elementary outcomes.** It is not a
claim that `Fin n` has ω elements, nor that the continuum consists of a
finite set of dots. New observable sets require a compatible refinement.

In a fixed context abbreviate

```
∫_E f := I_Ω(1_E f),       P_Ω(E) := ∫_E 1.
```

Then, exactly as requested,

```
∫_Ω 1 = 1,       P_Ω(Ω) = 1.
```

The Lean notation is `∫[Ω] f` for the whole context, `∫[Ω; E] f` for
restriction without renormalization, and `∫[Ω | E] f` for conditioning.
Activate it with `open scoped AlgebraicIntegral`.

This means the integral of **1** over the whole space is 1; an arbitrary
function need not integrate to 1. The raw content integral still has
`J_Ω(1) = ν(Ω)`. This distinguishes, for example, length `2ω` from total
probability `1` on the chosen ambient interval `[−ω,ω)`.

Do not normalize each subset during an ordinary event integral. That would
make every nonempty event have probability one and destroy additivity.
An explicit context change instead gives

```
I_{Ω|E}(f) = I_Ω(1_E f) / P_Ω(E),       P_Ω(E) > 0.
```

The dependence on the original context remains in the notation `Ω|E`.
In particular `I_{Ω|E}(1)=1`, while `I_Ω(1_E)=P_Ω(E)`.

**Checked:** `Hyper/ContextIntegral.lean` proves normalization, linearity,
positivity, monotonicity, bounds `0 ≤ P(E) ≤ 1`, complement, inclusion–exclusion,
disjoint additivity, conditional normalization, invariance under scaling,
compatible-refinement invariance, density reweighting,
and Fubini for the product of finite observable partitions. No measure-theory
integration or countably infinite sum appears in these proofs.

## 3. Point, dot, and halo: three different questions

Use these names precisely:

| Support | Meaning | What its normalized spike does |
|---|---|---|
| Point `{y}` | One exact admitted outcome | Reproduces `f(y)` exactly |
| Dot `D_r(y)` | A specified region at a specified resolution | Reproduces the conditional average over the region |
| Halo `halo(y)` | All points whose difference from y is infinitesimal | Has no automatically specified content or spike height |

The former “epsilon disk” is henceforth a **dot**. A round dot of radius ε
is a disk in two dimensions, an interval in one dimension, or a ball in
higher dimensions. A half-open cubical dot is a different chosen shape.
Do not identify their sizes: a radius-ε interval has length `2ε`; a
half-open cell `[y,y+ε)` has length `ε`; a round planar dot has geometric
area `πε²`, when that geometric content is used. A prescribed area ε would
require a different radius. “Dot” alone never fixes all these conventions.

Dots with arbitrary centers overlap. Only a stated partition convention
makes particular dots disjoint. A point is not automatically its dot.
One may deliberately use dots as the elementary outcomes of a measurement
space, but then an exact outcome means an exact *cell label*. That is a
different observable from exact equality of geometric coordinates.

`Hyper/AlgebraicSupport.lean` proves that a singleton, a radius-ε dot,
and a halo are distinct: `y+ε/2` is in the dot but not the singleton, and
`y+2ε` is in the halo but outside the dot.

The halo is not `[y−ε,y+ε)`. In H_ℝ it also contains `y + nε` for every
ordinary integer n, and many other infinitesimal displacements. It has no
outermost infinitesimal radius. Therefore the prescription “ω/2 throughout
the halo integrates to 1” is unjustified. If a model explicitly admits a
halo and assigns it positive content, it can be normalized by that content;
the field axioms alone do not assign it.

The single algebraic rule covering every admitted support is

```
δ_E^Ω = 1_E / P_Ω(E),                  P_Ω(E) > 0,
I_Ω(δ_E^Ω) = 1,
I_Ω(f δ_E^Ω) = I_{Ω|E}(f).
```

**Use a point for an exact Dirac evaluation and a dot for a resolution
kernel. Use a halo for infinitesimal proximity, not as an unspecified
normalization region.** These roles are compatible and need no competing
delta definitions. In particular, whenever a singleton is admitted with
positive content,

```
I_Ω(f δ_{ {y} }^Ω) = f(y).
```

The corresponding identity for a dot is an *average*, equal to f(y) only
with additional assumptions, such as f constant on that dot. A two-cell
central-difference stencil averages two values; it is not exact point
evaluation. All of these identities retain infinitesimal corrections.

The height of δ depends on the reference integral. Under uniform interval
normalization a point of probability ε needs height ω; under a square law
where a point has probability ε² it needs height ω². With raw geometric
content the coefficient is instead `1/ν(E)`. This context dependence removes
the erroneous universal rule “δ always equals ω”.

## 4. The sampling dart, with the event algebra and assumptions included

Choose the unit-square resolution convention

```
ν(Ω) = ω²,       ν(L) = ω,       ν({p}) = ν({q}) = 1,
```

where L is the diagonal, p lies on L, and q lies off L. These are the model's
geometric content data. They correspond to the polynomial identities for
an N-by-N square array: N² outcomes, N diagonal outcomes, and one specified
outcome. Substitution of ω in these polynomials is algebraic; it does not
construct a hyperfinite index type or identify every real point with a grid
site. The Lean model directly checks the resulting content assignment.

The disjoint partition and contents are

| Region | ν |
|---|---:|
| `{p}` | `1` |
| `L \ {p}` | `ω − 1` |
| `{q}` | `1` |
| `Ω \ (L ∪ {q})` | `ω² − ω − 1` |

All four contents are strictly positive, and their sum is ω². Assign each
union of cells the sum of its contents. This gives a consistent, finitely
additive event algebra: overlaps are not accidentally counted twice.
For an observable with the four respective values a,b,c,d,

```
I_Ω(f) = [a + b(ω−1) + c + d(ω²−ω−1)] / ω².
```

The results now follow from that integral, without limits:

```
I_Ω(1) = 1,
P({p}) = ε²,
P(L) = ε,
0 < P({p}) < P(L),
P(L)/P({p}) = ω,
P({p} | L) = ε,
P(L ∪ {q}) = ε + ε²,
P(L | L ∪ {q}) = 1/(1+ε),
P({q} | L ∪ {q}) = ε/(1+ε).
```

The final two sum to 1 exactly. This mixed-order conditioning is where the
new exact field matters. `Hyper/AlgebraicDart.lean` checks the event model,
the main probabilities, strict rarity, conditioning, and point evaluation.

For a different board, if its specified content is `Aω²` and a chosen
line event has content `Lω`, the same calculation gives `ε²/A` and `Lε/A`.
The coefficient L here is resolution content, not automatically Euclidean
length: the square diagonal has content coefficient 1 although its length
is √2. Changing the geometric observation convention can change L.

For a circular board one can use the real coefficient A = πR², but its
area alone does **not** determine positive singleton contents, line contents,
or exact boundary corrections. Those still require compatible geometric
content data. The new code settles the explicit square dart and the
normalization mechanism; it does not claim a derived rotation-invariant
content on all subsets of a disk. Merely writing a two-dimensional integral
sign would not fill that mathematical gap.

## 5. Polynomial observables: algebraic integration beyond simple functions

The normalized finite partition integral handles step observables. To admit
polynomial observables varying inside a cell, additionally specify its
polynomial moment functional. One exact algebraic convention is finite
calculus: define power-sum polynomials recursively by

```
S₀(N) = N,
(m+1) Sₘ(N) = N^(m+1) − Σ_{j<m} binomial(m+1,j) Sⱼ(N).
```

This is finite polynomial recursion, not an infinite sum. It agrees with
ordinary finite sums at natural N. Evaluate it at N = ω. Midpoint sampling
`x=(k+1/2)/N` then gives the normalized unit-interval moments

```
I(1) = 1,
I(x) = 1/2,
I(x²) = 1/3 − ε²/12,
Var(x) = (1−ε²)/12.
```

The left convention gives `I(x)=1/2−ε/2`; these are different exact
algebraic integrals. A polynomial antiderivative convention would instead
give `I(x²)=1/3`. Choose and state a convention rather than equating them.
For products, tensor the specified moment functionals; for independent
unit coordinates, for example, `I(xy)=1/4`.

The earlier `HyperIntegral` computes these power-sum expressions on its list
backend. The new exact-field regression file verifies the displayed moment
formulas by field algebra. A general moment/refinement compatibility theorem
for that legacy implementation is not claimed. In particular, a polynomial
formula at arbitrary hyperreal bounds is not automatically positive: extending
midpoint variance `(N²−1)/(12N²)` to `0<N<1` makes it negative. Valid
polynomial contexts need explicit positivity and resolution conditions.

The finite-difference fundamental theorem is the algebraic identity
`Σ_{k<N}(F(k+1)−F(k)) = F(N)−F(0)`, extended as a polynomial identity when
F is polynomial. It pairs with finite differences, not automatically with
the ordinary formal derivative. Applying a central difference to a step
creates a two-dot stencil; it does not prove support on an entire halo.

## 6. Densities and probability applications

Relative to a fixed normalized base context, an admitted density p satisfies
`p≥0` and `I_Ω(p)=1`. Define

```
P_p(E) = I_Ω(1_E p),           E_p[f] = I_Ω(fp).
```

If g≥0 and `I_Ω(g)>0`, its normalized density is `g/I_Ω(g)`. General exact
division makes this work also for mixed orders. Concentrated and spread-out
laws use the same algebra: for `0≤a≤1`, `(1−a) + a δ_{ {y} }^Ω` integrates
to 1. Its probability at y is `(1−a)P_Ω({y})+a`; the baseline contribution
must not be silently dropped.

Conditional probability, Bayes' rule with nonzero evidence, independent
products, expectations, and variances follow by field identities and finite
additivity. An ω payoff occurring with probability ε contributes exactly 1
to expectation. Conditioning on a positive infinitesimal event is ordinary
division, not conditioning on zero. No separate point-weight mechanism or
analytic distribution theory is necessary.

Endpoint conventions also become honest exact expressions. A symbolic
half-open interval with ω sites gives per-site probability ε; a closed
interval with ω+1 sites gives `1/(ω+1)=ε/(1+ε)`. They are different models,
both normalized. A uniform law on the chosen interval `[−ω,ω)` is likewise
a bounded ambient model; it is not a translation-invariant law on the entire
ordered field, which also contains ω².

## 7. What is now fixed, and what is deliberately not asserted

The field operations and ordering, normalization, Boolean event laws,
products of observable partitions, support-normalized delta identity, and
explicit dart model have kernel-checked proofs. There are no added axioms,
`sorry`s, series, limits, or calls to the unsound list-field instance in this
path. Run `./test.sh` for both the legacy regression examples and these proofs.

The remaining choices are mathematical input: which geometric events and
functions are admitted, what resolution content they carry, and which
polynomial sampling convention is intended. Field algebra cannot uniquely
choose these from the word “uniform”. Arbitrary transcendental integration,
countable additivity, and a content assignment to every halo are not
consequences of this specification. Extending the event/function domain must
preserve its finite algebraic identities and positivity.

The [Mathlib rational-function documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/RatFunc/Basic.html)
describes the fraction field used in the implementation. The proof and
normalization design above are given explicitly here; no nonstandard-universe
construction is being imported through that reference.
