# Alternatives to our algebraic geometric probability

**Status: separate comparison note.** This note does not change the current
theory, manuscript, definitions, or Lean modules. Its purpose is to explain
which choices are conventions, which produce different probabilities, and
what can be gained or lost by making another choice.

The current construction is not the only canonical possibility. It is
natural relative to a specified event domain, geometric calibration,
finite additivity, and a product rule for independent coordinates. The
existence of a positive infinitesimal alone does not determine these choices.

## 1. The cube already has probability one

Three quantities must be kept separate:

| Quantity for the closed unit cube | Current value |
|---|---|
| Ordinary Euclidean volume | 1 |
| Raw geometric content | (1+ε)³ = 1+3ε+3ε²+ε³ |
| Normalized probability | 1 exactly |

The raw content is not ordinary volume. It records several geometric
dimensions at once. Its first correction is half the cube's surface area
times ε; the other coefficients follow the selected intrinsic-volume
calibration. They are not a literal sum of separately counted closed faces,
edges, and vertices, which overlap.

The expression 1+ε belongs to a closed **unit interval**. Its orthogonal
products give (1+ε)² for the square and (1+ε)³ for the cube. In every case,
normalizing by the whole context gives probability one.

The polynomial is a reversed and scaled classical Wills polynomial; see
[Hernández Cifre and Yepes Nicolás, equation (1.4)](https://webs.um.es/jesus.yepes/publicaciones_files/paper_WillsFunctional.pdf).
The choice to use it as raw content is part of the model, not an unavoidable
consequence of having an infinitesimal field.

## 2. A closed-unit-cube content of exactly one: an equivalent presentation

This is the simplest way to remove the visually surprising total without
changing any of our probabilities. Use the normalized coordinate gauge

```
η = ε/(1+ε),          ε = η/(1−η).
```

For the existing d-dimensional content define

```
μ_d(E) = ν_d(E)/(1+ε)^d.
```

In the intrinsic-volume notation this becomes

```
μ_d(E) = Σ(j=0,...,d) V_j(E) η^(d−j) (1−η)^j.
```

This identity applies wherever the original content is defined; it does
not enlarge its geometric event domain. Multiplication by a common
positive factor preserves additivity and positivity, and the factors
also respect our orthogonal-product convention across dimensions.

For a closed interval of standard length L the formula is particularly
simple:

```
μ₁([a,b]) = (1−η)L + η,       μ₁({a}) = η.
```

Therefore a closed unit interval has content 1. A closed unit cube has
content 1³=1; full coordinate slices, crossings, and points have contents
η, η², and η³. No boundary point has been deleted or made probability zero.

The price is visible in other intervals: a half-length closed interval
has content (1+η)/2, not 1/2. Gluing two such intervals subtracts the shared
point and gives exactly one:

```
(1+η)/2 + (1+η)/2 − η = 1.
```

For an arbitrary board Ω we still normalize by μ_d(Ω). The common scaling
cancels, so

```
μ_d(E)/μ_d(Ω) = ν_d(E)/ν_d(Ω).
```

Thus this is an alternative **presentation**, not a competing theory.
It privileges the unit cube as a reference shape; a unit disk's raw μ
content need not be one, though its normalized probability remains one.
It answers the concern about the cube's raw total without changing results.
It is only being described here, not adopted in the current theory.

## 3. Half-open boxes: change the boundary convention

Under the existing content, subtracting one endpoint from a closed
interval gives ν₁([0,1))=1. Consequently

```
ν_d([0,1)^d)=1.
```

An admitted point still has content ε^d and a full half-open coordinate
crossing has the expected power of ε. This convention is convenient when
tiling boxes: each shared boundary is assigned to one side.

It is not the same sample space as the closed cube. For example, reflection
of [0,1) about its midpoint produces (0,1], a different set. The valuation
can remain geometrically invariant while the selected board is not
preserved by that reflection. One must not silently count an excluded
endpoint as an event inside the board.

This is another boundary choice within the existing theory, rather than a
new field or a new probability rule. It does not give the full closed cube
raw content one with the original calibration.

## 4. A genuinely different algebraic theory: independent dimension weights

Within the same kind of planar geometric formulas, choose positive
standard real parameters α and β and set

```
ν_(α,β)(closed polygon of area A and perimeter P)
    = A + α(P/2)ε + βε²,
ν_(α,β)(closed segment of length L) = αLε + βε²,
ν_(α,β)(point) = βε².
```

The current calibration is α=β=1. All these formulas use Euclidean sizes,
keep the same dimension orders, and obey the elementary polygon-cut and
segment-gluing identities. The endpoint correction remains forced, but
its value is βε² because that is the selected point content.

This family illustrates freedom in calibration, not an asserted global
extension to all geometric sets. For a complete explicit alternative,
take α=1 and β=2 on the following four-region event algebra. In a unit
square, let H and V be a horizontal and a vertical full closed crossing,
meeting at p. Assign the disjoint regions these contents:

| Observable region | Alternative content |
|---|---|
| {p} = H∩V | 2ε² |
| H without p | ε |
| V without p | ε |
| Outside H∪V | 1 |

Every entry is positive. Their total is Z=1+2ε+2ε². Define probabilities by
division by Z, and extend to all unions of these four regions by finite
addition. This is a complete positive normalized probability on that
finite observable algebra, with no existence theorem or infinite sum needed.

It gives

```
P(H)=P(V)=(ε+2ε²)/Z,          P({p})=2ε²/Z,
P(H∩V) − P(H)P(V) = ε²/Z² > 0.
```

The perpendicular crossing events are now positively correlated. In our
present product context they are independent. This difference survives
normalization and is not removed by renaming ε, so this is a genuinely
different model.

Why does our product rule select a smaller family? If the one-dimensional
closed-interval content is L+cε, multiplying two such contents gives

```
(a+cε)(b+cε) = ab+c(a+b)ε+c²ε².
```

Comparison with the planar formula forces α=c and β=c². Therefore the
independent parameters must satisfy β=α² if this particular product rule
is retained. Our α=β=1 is its unit calibration. The alternative α=1, β=2
deliberately gives up that product rule, while retaining positive point
probabilities and the leading orders of lines and points.

Its whole-square probability is one, as usual. Its raw content can also
be made one by a common positive rescaling; that would not undo the
correlation and therefore would not turn it into our model.

## 5. A genuinely different board: identify opposite faces

There is an alternative with raw total one that keeps the original length
coefficient, positive points, and independent coordinates: use a periodic
board. A unit interval with its endpoints identified is a circle of
circumference one. Three independent such coordinates form a flat torus,
represented by a cube with opposite faces identified.

Here is a purely algebraic construction on a precise event domain. Divide
the circle at finitely many standard points into open arcs of positive
standard lengths ℓ₁,...,ℓ_k, with their sum equal to one. Assign

```
each vertex:       ε,
each open arc:     ℓ_i−ε.
```

All contents are positive because each standard ℓ_i exceeds ε. There are
k vertices and k open arcs, so the raw content of the whole circle is

```
kε + Σ(ℓ_i−ε) = 1.
```

Inserting a new vertex preserves content, since splitting an open arc gives

```
(ℓ₁−ε) + ε + (ℓ₂−ε) = (ℓ₁+ℓ₂)−ε.
```

Any two finite partitions have a common refinement. Consequently this
defines a positive finitely additive content on all finite unions of arcs
and points, independently of the chosen partition. The whole circle must
not be treated as a closed interval: it has no pair of distinct endpoints.
A proper closed arc still has content ℓ+ε, as in our original calibration.

Take the product of these contents in three coordinates. On the algebra of
finite unions of products of arcs and points, common coordinate refinements
again give a well-defined positive content. Its raw total is 1³=1, and

```
whole periodic board:                 1,
one fixed coordinate (a subtorus):    ε,
two fixed coordinates (a loop):      ε²,
three fixed coordinates (a point):   ε³.
```

Thus no separate normalizing denominator is needed for this board. Both
the construction and its refinement check use finite sums and products.
This paragraph is a mathematical construction, not a claim of an added
Lean implementation.

The cost is an actual change of space. Opposite faces represent the same
positions, and a coordinate crossing is a closed loop rather than a
segment with two distinct ends. The event algebra described here is based
on rectangular coordinate products; it does not yet cover arbitrary
oblique curves or curved regions. A cubic flat torus also does not have
the full ambient rotation symmetry of Euclidean space.

This alternative explains the extra boundary terms particularly clearly:
a cube with distinct boundary faces and a periodic board with those faces
identified are different geometric objects. Both can support positive
infinitesimal points, but their raw totals need not agree.

## 6. A different resolution model: count sites instead of geometric content

At finite resolution N, choose N midpoint sites in each coordinate and
assign every d-dimensional sample site weight 1/N^d. Then

```
whole sample = 1,     coordinate slice = 1/N,
coordinate crossing in 3D = 1/N²,     sample point in 3D = 1/N³.
```

The relevant count polynomials give the symbolic forms 1, ε, ε², ε³ on
substitution N=ω=1/ε. For these selected observable families this is finite
algebra; it does not assert that our field contains an actual ω-sized array.
The earlier midpoint example already checks this convention for a square.

It makes the whole closed board's sampled content one because all the
selected sites lie inside it. But the exact boundary sites are not selected.
At finite resolution, a nonselected geometric singleton has probability
zero; only admitted sites have positive singleton probability. A site's
label may instead represent a cell or dot, which changes the meaning of
an outcome. Symbolic substitution is justified for the chosen polynomial
counts, not automatically for every geometric event's counting function.

There is also a geometric tradeoff. In the midpoint square a full axis row
and a full diagonal both contain N sites, despite their Euclidean lengths
being 1 and √2. This grid model does not have the current Euclidean
length coefficient, and a fixed Cartesian grid is not invariant under
arbitrary rotations. It is useful when the observation procedure genuinely
comes with a grid or finite resolution.

## 7. What cannot be combined without a correction

Suppose every closed interval has content exactly equal to its ordinary
length, while a point has positive content p. Splitting [0,1] into two
closed half intervals would require

```
1 = 1/2 + 1/2 − p,
```

so p=0, a contradiction. Thus finite additivity and positive points prevent
all closed intervals from having their ordinary lengths as exact contents.
They do **not** prevent one chosen closed unit interval or cube from having
content one: section 2 supplies that alternative calibration explicitly.

Ordinary area/volume probability is another valid alternative if positive
point and line probabilities are dropped. It assigns the unit cube value
one and every lower-dimensional event value zero. The infinitesimal
corrections in our theory retain information that this choice omits.

## 8. What is canonical, and what is a decision?

Given the field, contents, and event algebra, normalization and the exact
conditional calculations are determined. Given our graded segment form,
point calibration, and additivity, its endpoint correction is forced.
Given independent coordinate products, the cube formulas follow.

The geometry, admitted observations, relative dimension weights, and
independence assumptions are model choices. Rotation invariance does not
choose all the coefficients by itself. Classical classification results
for continuous Euclidean-invariant valuations explain the intrinsic-volume
basis, but do not single out our coefficient choices; see
[Baryshnikov, Ghrist, and Wright](https://mlwright.org/docs/hadwiger_definable_functions.pdf).
Their continuity assumptions are context for the comparison, not new
axioms introduced into our algebraic construction.

Broader non-Archimedean probability constructions offer other domains and
symmetry choices as well; see
[Benci, Horsten, and Wenmackers](https://arxiv.org/abs/1106.1524).
The present note does not claim a full comparison of those theories.

**Assessment:** our theory is a coherent calibrated choice, not the unique
possible one. The most direct answer to the surprising cube total is the
equivalent unit-cube calibration in section 2. The weighted finite model
in section 4 shows which independence property the original calibration
buys us. The periodic model in section 5 retains independence and makes
the raw total one by changing the board's topology and admitted geometry.

Only this note is added. The alternative formulas are explanatory algebra,
with their displayed identities checked symbolically; they are not new
Lean axioms or a replacement implementation. Existing regression tests
are run before and after the documentation addition.
