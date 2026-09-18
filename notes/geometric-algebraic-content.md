# Why Euclidean length appears in algebraic probability

This is the preferred geometric continuation of
[the algebraic foundations](algebraic-hyperreal-foundations.md). The previous
midpoint grid remains a valid sampling convention, but it is not a
rotation-invariant model of Euclidean line content.

The main result is that **length need not be a direction-specific probability
axiom**. Rotation invariance, dimensional scaling, and one unit calibration
force the one-dimensional coefficient. Finite additivity then forces
endpoint corrections. All subsequent calculations are finite algebra.

## 1. Three conditions force length

Let F(v) be the real coefficient of the order-ε contribution of a segment
with displacement vector v. Require:

1. **Euclidean invariance:** rotating v does not change F(v).
2. **Degree-one scaling:** F(tv) = t F(v) for real t ≥ 0.
3. **Unit calibration:** F((1,0)) = 1.

These are conditions on the one-dimensional coefficient; they do not assert
that the complete content, including endpoints, scales linearly.

Set ℓ² = x²+y² and choose the nonnegative root ℓ. For ℓ > 0 the pair
`c=x/ℓ, s=y/ℓ` satisfies `c²+s²=1`. Hence the matrix

```
[ c  -s ]
[ s   c ]
```

rotates `(1,0)` into `(x/ℓ,y/ℓ)`. Rotation invariance and scaling give

```
F((x,y)) = ℓ F((x/ℓ,y/ℓ)) = ℓ F((1,0)) = ℓ.
```

The zero case follows from scaling by zero. Thus

```
F((1,0)) = F((0,1)) = 1,
F((1,-1)) = √2.
```

There is no trigonometric parameterization, limiting argument, or continuum
sum in this derivation. The square root is the nonnegative solution of a
quadratic equation. `GeometricContent.length_coefficient_forced` checks the
derivation in Lean, with the three conditions as explicit hypotheses.

The calibration of the one-dimensional scale relative to the point scale
is still a choice. Symmetry cannot determine a unit of measurement.
Nor do these three conditions constitute a uniqueness theorem for every
possible geometric probability functional.

## 2. Why exact additivity changes closed segments

Fix the unnormalized planar content of one point as ε². For a closed segment
of length ℓ, consider the dimensionally graded expression

```
ν([a,b]) = ℓε + k,
```

where k is the zero-dimensional endpoint contribution. Split this segment
at an interior point m. Finite additivity gives

```
ν([a,b]) = ν([a,m]) + ν([m,b]) − ν({m}).
```

Substitute the expressions and cancel the lengths. The remaining equation
is `k=2k−ε²`, so **k=ε²**. Subtracting endpoints now gives

| Segment convention | Content |
|---|---:|
| Closed `[a,b]` | `ℓε + ε²` |
| Half-open `[a,b)` | `ℓε` |
| Open `(a,b)` | `ℓε − ε²` |

These are formulas for positive-length segments with standard real
coordinates; the degenerate closed segment is a single point. The table is
not three independent axioms. Its first-order coefficient follows from §1,
and its endpoint coefficients follow from additivity and point calibration.
The proof of `endpoint_correction_forced` checks the gluing calculation.

My earlier suggestion `P(L)=length(L)ε` was therefore incomplete: it is an
exact half-open, unnormalized content formula, not a universal formula for
all closed line events in every normalized context.

## 3. One finite geometric content, for all three dimensions

For a closed convex polygon K with area A and perimeter P, the compatible
expression is

```
ν(K) = A + (P/2)ε + ε².
```

The half-perimeter factor is explained by a cut. When a polygon is divided
into two closed polygons along a segment of length ℓ, their areas add, but
their perimeters add to `P+2ℓ`. The shared closed segment has content
`ℓε+ε²`. Inclusion–exclusion therefore cancels both the duplicated internal
length and the duplicated point-level term:

```
[A₁ + P₁ε/2 + ε²] + [A₂ + P₂ε/2 + ε²] − [ℓε+ε²]
  = (A₁+A₂) + (P₁+P₂−2ℓ)ε/2 + ε².
```

Within an area-plus-perimeter-plus-point expression, the coefficient of
perimeter must be 1/2 to cancel an arbitrary internal cut with the calibrated
line content. A rectangle supplies an independent compatibility check:

```
ν([0,a]×[0,b]) = (a+ε)(b+ε)
               = ab + (a+b)ε + ε².
```

This agrees with area `ab` and perimeter `2(a+b)`. This rectangle check does
not assert that arbitrary intrinsic-volume content is multiplicative for
every Cartesian product of arbitrary sets.

For finite polyhedral events the concise notation is

```
ν(E) = V₂(E) + ε V₁(E) + ε² V₀(E).
```

Here V₂ is area, V₁ is the geometric length coefficient (half-perimeter for
a closed two-dimensional convex polygon, length for a closed segment), and
V₀ is the finitely additive Euler characteristic. On a finite complex its
value is the signed count `vertices − open edges + open faces`. It is not
simply the number of connected components for every event.

This is the planar intrinsic-volume polynomial with a chosen common gauge.
The background valuation and extension results are described in
[Tropp's lectures, chapters 8–10](https://tropp.caltech.edu/notes/Tro18-Lectures-Convex-LN.pdf)
and [Klain's discussion of polytope valuations, §3](https://faculty.uml.edu/dklain/Klain-Euler.pdf).
The construction here is restricted to finite polyhedral geometry; it does
not require the analytic extension to arbitrary convex bodies.

An explicit finite recipe is to decompose an event into relatively open
polygonal cells and add:

```
point:                  ε²,
open segment:           ℓε − ε²,
interior of polygon:    A − (P/2)ε + ε².
```

The formulas for a closed triangle result by adding its open interior,
three open edges, and three vertices. A common subdivision makes arbitrary
finite unions/intersections additive. Segment splits and polygon cuts
preserve the expressions by the identities above. The general independence
of decomposition is a standard polyhedral valuation theorem; only the
displayed local dissection identities, not its full geometric formalization,
are currently checked in this repository.

For bounded nonempty **standard** polyhedral sets, the leading nonzero
coefficient is positive: area in dimension two, total length in dimension
one, or the number of points in dimension zero. Thus negative lower-order
boundary corrections do not make content negative. This is why the
non-Archimedean ordered field is useful here.

## 4. The unit square, with all endpoints treated symmetrically

For the closed unit square Ω = [0,1]²,

```
Z = ν(Ω) = 1 + 2ε + ε² = (1+ε)²,
I_Ω(f) = J_ν(f)/Z,          P_Ω(E) = ν(E)/Z.
```

For simple functions J is the same finite algebraic integral already
implemented in `ContextIntegral`. In particular, `I_Ω(1)=1` exactly.

| Event in the closed unit square | Exact probability |
|---|---:|
| Whole square | `1` |
| A point | `ε²/(1+ε)²` |
| Closed horizontal or vertical unit crossing | `(ε+ε²)/(1+ε)² = ε/(1+ε)` |
| Closed diagonal from `(0,1)` to `(1,0)` | `(√2 ε+ε²)/(1+ε)²` |

The diagonal is strictly more probable than an axis crossing. With identical
endpoint conventions, their difference is exactly

```
P(diagonal) − P(horizontal) = (√2−1)ε/(1+ε)².
```

Thus the orientation effect comes from length, and every endpoint is
accounted for. The ratio is `(√2+ε)/(1+ε)`, not exactly √2, because each
closed segment also contains the same order-ε² contribution.

There is no difficulty normalizing the new Z: the exact rational-function
field already supplies its inverse. The requirement was total probability
one, not raw square content one under every boundary convention.

`GeometricContent.squareContext` realizes the relevant Boolean algebra with
three cells: a point p on the closed segment, the rest of that segment, and
the rest of the square. Their raw contents are

```
ε²,       ℓε,       1+(2−ℓ)ε.
```

They sum to Z. For `0<ℓ≤2` they are positive; horizontal and diagonal
crossings satisfy this bound. Lean checks positivity, normalization, the
point and line probabilities, and the strict diagonal comparison. The
geometric placement is input; the code does not yet parse arbitrary planar
sets into cells.

### The simplest normalized gauge

We can recover the particularly simple point and axis formulas by defining
the context's effective resolution `η = ε/(1+ε)`. This is still a positive
infinitesimal, and is an exact algebraic change of gauge, not a truncation.
Then the closed-square formulas become

```
P(point) = η²,
P(horizontal) = P(vertical) = η,
P(closed segment of length ℓ) = ℓη + (1−ℓ)η²,
P(diagonal) = √2 η + (1−√2)η².
```

After declaring this context gauge one may denote η by ε locally. The
important point is to declare the change: the original infinitesimal and
the effective one are not exactly equal. These formulas retain the desired
minimal square/axis/point example while deriving the diagonal's length
factor and its necessary endpoint correction. The gauge transformation is
checked in `point_probability_effective` and `segment_probability_effective`.

## 5. Retaining a square of raw content one

If a half-open square is preferable, finite additivity gives

```
ν([0,1)²) = 1.
```

An interior horizontal crossing `[0,1)×{c}` is half-open and has content ε.
The descending diagonal inside `[0,1)²` excludes both corner endpoints,
so its content is **√2 ε − ε²**. The ascending diagonal includes one corner
and excludes the other, so its content is **√2 ε**.

This is not a failure of Euclidean invariance: reflection changes the
half-open boundary convention of the square. The closed square is the
cleanest example when all directions should be treated symmetrically.
The earlier exact pair `diagonal=ε, point=ε²` remains a result of the
coordinate-sampling model, not the selected Euclidean content.

## 6. What the construction does not silently assume

The new geometry is finite and uses standard real coordinates. It does not
extend its positivity theorem to all infinitesimal-coordinate regions.
For example, formally inserting `ℓ=ε/2` in the open-segment expression gives

```
ℓε − ε² = −ε²/2 < 0.
```

This counterexample is checked in Lean. Consequently an infinitesimal dot
cannot automatically be treated as just another geometric region under this
same content formula. A dot used as an elementary observation is a separate
resolution convention; a halo still has no canonical content. Extending the
event domain to literal infinitesimal regions requires additional compatible
structure, rather than an unjustified substitution in a standard-geometry
formula.

The minimal commitments here are finite additivity, Euclidean symmetry and
dimensional scaling, and calibration of the area/line/point scales. The
metric, square roots, polygonal area, and finite incidence counts are ordinary
geometry over the coefficient field. There is no additional probability
axiom for “diagonal,” “north,” or “east.”

## 7. Checked implementation

`Hyper/GeometricContent.lean` proves the length-coefficient characterization,
rotation invariance, endpoint forcing, closed/open segment splits,
closed/open polygon dissection algebra, rectangle compatibility, the closed
square probabilities, and the explicit positivity scope. The general
triangulation/valuation extension theorem is documented above and is not
replaced by a Lean axiom.

`test_algebraic.lean` audits these proofs; `./test.sh` also runs the earlier
sampling and integral regressions. The old sampling model is retained as a
distinct model so its results cannot be mistaken for Euclidean invariance.
