# The cube and the codimension rule

The [algebraic O-notation convention](algebraic-order-notation.md) gives
shorter leading-order formulas while retaining the exact contents below.

The cube extends the [square construction](geometric-algebraic-content.md)
by orthogonal products. No new exponent is assigned separately to a face,
line, or point. The structural assumption is the existing product rule for
independent coordinate contexts; Euclidean invariance alone would not imply
independence.

Throughout, ε is the raw geometric gauge and

```
η = ε/(1+ε)
```

is the normalized resolution, exactly as for the square. They are distinct
field elements. After declaring the ambient unit-cube convention, η may be
called the context's epsilon. This is an explicit change of gauge, with no
discarded terms.

## One interval, then three factors

A closed interval of standard length a has one-dimensional content a+ε;
a singleton has content ε. Multiplication gives the closed rectangular box

```
ν₃([0,a] × [0,b] × [0,c])
  = (a+ε)(b+ε)(c+ε)
  = abc + (ab+ac+bc)ε + (a+b+c)ε² + ε³.
```

The first coefficient is volume; the second is half the boundary area.
All terms follow by expanding a product. In particular the closed unit cube
Ω=[0,1]³ has content (1+ε)³, and probability is ν₃(E)/ν₃(Ω).

Fixing a coordinate replaces its factor 1+ε by ε. Therefore:

| Event in the closed unit cube | Raw content | Exact probability |
|---|---|---|
| Whole cube | (1+ε)³ | 1 |
| Full coordinate plane slice, including a boundary face | ε(1+ε)² | η |
| Full axis-parallel line crossing, including a boundary edge | ε²(1+ε) | η² |
| One point | ε³ | η³ |

The chosen fixed coordinate may be anywhere in [0,1]. These statements use
closed slices, including their boundary points. The whole cube has
probability one; its ordinary Euclidean volume is also one, but the two are
different notions.

More generally, in an n-dimensional unit cube, let k coordinates remain
free and let r=n−k coordinates be fixed. Then finite algebra gives

```
P(E) = (1+ε)^k ε^r / (1+ε)^(k+r) = η^r.
```

Thus the exponent counts fixed coordinates, or codimension. This is proved
for every natural k and r by `CubicContent.codimension_law`; no induction
axiom about probabilities is added.

## Compatibility with cuts and normalized integration

Cut a box across one axis into lengths a and b. The two closed boxes share
a rectangle. Its three-dimensional content is ε(c+ε)(d+ε), so

```
(a+ε)(c+ε)(d+ε) + (b+ε)(c+ε)(d+ε)
  − ε(c+ε)(d+ε)
  = (a+b+ε)(c+ε)(d+ε).
```

The shared surface correction is precisely what finite additivity requires.
This identity is checked as `box_dissection`.

For an actual positive integral context, partition each coordinate interval
into a chosen point and its complement. Their contents are ε and 1, so
their normalized probabilities are η and 1−η. Take the existing `Context`
product three times. This yields eight observable regions with nonnegative
contents and total (1+ε)³. These eight regions are a partition for observing
three coordinate constraints, not a claim that the cube has eight points.

The existing finite algebraic Fubini theorem proves that coordinate
indicator products integrate to the product of their probabilities.
`cube_face_probability`, `cube_line_probability`, and
`cube_point_probability` consequently verify η, η², and η³ within that
normalized context. Normalization and positivity are not merely formal
labels on a polynomial.

## Length, area, and boundary corrections

An embedded closed segment of standard Euclidean length L has content

```
ν₃(segment) = ε(Lε+ε²) = Lε²+ε³.
P(segment) = Lη² + (1−L)η³.
```

The unit crossing therefore has probability η². For the body diagonal,
L=√3, giving √3 η²+(1−√3)η³. The square root is defined algebraically by
the squared-distance equation.

A closed convex planar patch of standard area A and perimeter P has the
compatible content obtained from the planar formula:

```
ν₃(patch) = ε(A+(P/2)ε+ε²).
P(patch) = Aη(1−η)² + (P/2)η²(1−η) + η³
         = Aη + (P/2−2A)η² + (A−P/2+1)η³.
```

For a unit square A=1 and P=4, both corrections cancel and the result is
exactly η. An arbitrary unit-area patch need not have perimeter 4, so its
probability need not be exactly η. Area determines the leading coefficient;
boundary geometry supplies the remaining terms. Likewise, an arbitrary
line segment has probability of order η² rather than always exactly η².

These formulas describe geometric content, not the probability of a dot or
halo unless an additional observation convention identifies such an event
with a point. A literal infinitesimal region is still outside the proved
standard-coordinate positivity scope.

## What has been established

`Hyper/CubicContent.lean` checks box expansion and cutting, cube
normalization, the segment and planar-patch probability identities, the
codimension identity in every finite dimension, and the positive cube
context with its three coordinate-event probabilities. It uses the same
ordered rational-function field and the same η as the planar construction.

The numerical geometry formulas take standard real lengths, areas, and
perimeters as inputs; Lean does not yet identify all these data with
arbitrary embedded geometric sets. A complete rotation-invariant valuation
on arbitrary three-dimensional polyhedra, and any extension to curved
surfaces or infinitesimal-coordinate regions, remain separate work.
The cube calculation does not assume those extensions, nor does it claim
that the three earlier conditions on a line coefficient uniquely determine
all three-dimensional contents.
