# Algebraic integration: current specification and legacy implementation

The current specification is
[Algebraic hyperreals, normalized integration, and the dart](../algebraic-hyperreal-foundations.md)
(2026-09-18). Read that document for the field, event algebra, normalized
integral, support conventions, and checked dart calculation.

The exact implementation consists of `Hyper/OrderedRational.lean`,
`Hyper/ContextIntegral.lean`, and `Hyper/AlgebraicDart.lean`. It uses a genuine
ordered rational-function field, including exact division by mixed-order
expressions. In a fixed context Ω,

```
I_Ω(f) = J_Ω(f) / J_Ω(1),
P_Ω(E) = I_Ω(1_E),
I_Ω(1) = 1,
δ_E^Ω = 1_E / P_Ω(E).
```

A point is an exact outcome. A dot is a specified resolution region (the new
name for an epsilon disk). A halo consists of all infinitesimally close
points. The interval `[y−ε,y+ε)` is a two-dot stencil, not a halo. A point
spike reproduces evaluation; a dot spike reproduces a conditional average.

## Status of HyperIntegral and the earlier exercise sheet

`Hyper/HyperIntegral.lean` and `Hyper/probes/IntegralExamples.lean` remain
executable legacy calculations of polynomial power sums and cell spikes.
They do not implement the current general probability context. In particular:

- Their raw integral need not normalize the whole domain to one.
- The sample offset affects exact moments and must be specified.
- `probPoint` is a density-sampling helper, not a proof that a geometric
  singleton is a cell. It does not check membership in the distribution's
  domain. Use the new event algebra for probability laws.
- `spikeMass` includes only complete cells. It is not additive under arbitrary
  cuts through a cell. The legacy spike integral and polynomial integral
  therefore cannot be presented as one unrestricted integral over all sets.
- `IsDensity` checks total normalization, but does not check positivity.
- `uniformOn` uses the legacy inverse, exact only for a nonzero monomial
  interval length. It is not a general constructor of probability contexts.
- Polynomial power-sum substitution at arbitrary hyperreal bounds is not
  automatically a positive functional. Resolution conditions are needed.
- `[-ω,ω)` is a chosen ambient interval, not the entire ordered field or
  literally the set ℝ.

The earlier claims that all real points are canonically disjoint dots,
that a halo has width `2ε`, that midpoint dot integration always equals
`f(y)ε`, and that the code supplies arbitrary-function integration are
withdrawn. The new foundations derive the valid identities with their
assumptions and distinguish ordinary geometric points from cell labels.

The historical [exercise sheet](integral-probability-exercises.md) remains
useful for algebraic examples under its stated sampling convention. Its
point/cell language should be read subject to the corrections above. The
trusted tests are in `test_algebraic.lean`; run `./test.sh` for both paths.
