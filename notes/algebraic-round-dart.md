# The dart on a unit disk or unit ball

The dart construction extends to round boards with the same codimension
orders. Geometric coefficients and exact boundary corrections change.
Here “unit” means radius one. A disk has ordinary area π, and a solid ball
has ordinary volume 4π/3; their normalized probabilities are both one.

We use the raw geometric gauge ε throughout this note. It is distinct from
the square/cube's normalized coordinate resolution η=ε/(1+ε). The leading
coefficients below use a fixed ε so that different shapes can be compared.

## How round content is selected algebraically

The existing polyhedral rules do not by themselves establish a unique
extension to every curved set. We make a specific compatible extension for
round boards using finite coefficient matching. Standard real geometry
supplies disk area πr² and ball volume 4πr³/3. The circle constant π is an
allowed coefficient in ℝ(ω); no claim is made that π is algebraic over ℚ.

The geometric normalization is the intrinsic-volume convention

```
Vol(K+t B_d) = Σ(j=0,...,d) κ_(d−j) V_j(K) t^(d−j),
κ₀=1, κ₁=2, κ₂=π, κ₃=4π/3.
```

Here κ_j is unit-ball volume and K+t B_d is the ordinary parallel body.
This convention is stated in equation (1.1) of
[McCoy and Tropp](https://tropp.caltech.edu/papers/MT14-Steiner-Formulas-preprint.pdf).
Our round-board calculation only uses the polynomial identity for a radius
r+t. It does not invoke a limiting construction or integrate over directions.
We define ν_d(K)=Σ V_j(K) ε^(d−j) for these round shapes, matching the
previous segment, polygon, and box calibrations.

For a disk, expanding π(r+t)² and matching coefficients gives

```
V₂=πr², V₁=πr, V₀=1,
ν₂(D_r)=πr²+πrε+ε².
```

For a ball, expanding (4π/3)(r+t)³ gives

```
V₃=4πr³/3, V₂=2πr², V₁=4r, V₀=1,
ν₃(B_r)=4πr³/3+2πr²ε+4rε²+ε³.
```

Both expansions are checked as polynomial identities in Lean. This is
algebra over the given real geometric coefficients. It does not purport
to derive ordinary Euclidean area or π from field axioms alone.

## The disk

Put Z_D=π+πε+ε² and P_D(E)=ν₂(E)/Z_D. Then

```
P_D(D)=1,
P_D(point)=ε²/Z_D,
P_D(closed chord of length L)=(Lε+ε²)/Z_D.
```

Every diameter has length 2, hence exactly the same probability
(2ε+ε²)/Z_D regardless of direction. A chord whose line has standard
distance h from the center has L=2√(1−h²), for |h|<1; this length follows
from the quadratic circle equation. Tangency, |h|=1, gives a point and
therefore ε²/Z_D, in agreement with the degenerate closed-segment formula.

The leading forms are

```
P_D(chord)=(L/π)ε+O(ε²),
P_D(diameter)=(2/π)ε+O(ε²),
P_D(point)=(1/π)ε²+O(ε³).
```

These are for fixed standard real lengths, with the algebraic O convention.
The square's coefficient one was tied to its unit lengths and unit area;
normalizing the whole board to probability one does not erase geometry.

## The solid ball

Put Z_B=4π/3+2πε+4ε²+ε³ and P_B(E)=ν₃(E)/Z_B. A planar disk of radius ρ
embedded in the ball has content ε ν₂(D_ρ). Thus

```
P_B(B)=1,
P_B(point)=ε³/Z_B,
P_B(diameter)=(2ε²+ε³)/Z_B,
P_B(central disk)=(πε+πε²+ε³)/Z_B.
```

A plane at distance h from the center cuts out a disk of radius
ρ=√(1−h²), for |h|<1. Its numerator is πρ²ε+πρε²+ε³. Again, at tangency
ρ=0 the formula reduces to the point content.

For the central examples:

| Event | Leading probability |
|---|---|
| Whole solid ball | 1 exactly |
| Central disk | (3/4)ε+O(ε²) |
| Diameter | (3/(2π))ε²+O(ε³) |
| Point | (3/(4π))ε³+O(ε⁴) |

The general leading coefficient is area divided by board volume for a
planar patch, or length divided by board volume for a segment. Codimension
determines the power of ε; size determines the coefficient.

If “sphere” means only the two-dimensional spherical surface as the sample
space, that is a different context from the solid ball. A surface-sampling
extension should have curve events of order ε and points of order ε².
The Lean examples here establish the solid-ball context, not a complete
probability theory on the spherical surface.

## Positivity and conditioning are checked, not assumed

The disk example uses the finite observable partition

```
point:                     ε²,
diameter minus point:      2ε,
disk minus diameter:       π+(π−2)ε.
```

The ball example uses a nested partition

```
point:                       ε³,
diameter minus point:        2ε²,
central disk minus diameter: πε+(π−2)ε²,
ball minus central disk:     4π/3+πε+(4−π)ε².
```

Each entry is nonnegative, using 2<π<4 and ε>0. The entries sum to Z_D and
Z_B respectively. Thus the existing normalized integral supplies genuine
finite probability contexts, including complements and finite additivity
on their observable event algebras.

Because the point lies on the chosen diameter, conditioning cancels the
ambient normalizer and the transverse epsilon factors:

```
P_D(point | diameter)=ε/(2+ε),
P_B(point | diameter)=ε/(2+ε).
```

Both identities are exact and Lean-checked. They are the same normalized
point probability on a closed interval of length 2.

## Scope of the extension

`Hyper/RoundContent.lean` checks the parallel-volume polynomial arithmetic,
positive disk/ball observable contexts, exact normalizers, point/diameter/
central-disk probabilities, and the conditioning ratios. It uses ordinary
mathlib bounds on the real constant π; the nonstandard arithmetic and
probability computations introduce no limits or infinite sums.

The leading O forms above follow by algebraically expanding the exact
reciprocals to the indicated finite order. This module checks their exact
underlying ratios, not separate Lean O certificates for every displayed row.

This is a concrete extension of the dart examples. A general compatible
valuation for arbitrary curved event sets, intersections of arbitrary
round regions, or infinitesimal-coordinate dots remains outside the proved
event domain. The result should not be read as a proof that those broader
extensions follow solely from the earlier polyhedral axioms.
